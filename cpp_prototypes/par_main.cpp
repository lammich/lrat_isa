#include <vector>
#include <cassert>
#include <cstdlib>
#include <iostream>

#include <tbb/task_group.h>

#include "Literal.h"
#include "ClauseId.h"
#include "Logging.h"

#include "Assignment.h"

#include "MMFile.h"

#include "CNF_It.h"

#include "VBEnc_It.h"



// #define PROFILING

#ifdef PROFILING
#include <gperftools/profiler.h>
#endif

using namespace std;


template <typename T> class nat_map {
  vector<T> map;

  T dflt;

public:

  nat_map(T _dflt = T()) : map(), dflt(_dflt) {}

  T get(size_t i) {
    if (i<map.size()) return map[i];
    else return dflt;
  }

  void set(size_t i, T v) {
    if (i>=map.size()) map.resize((i+1),dflt);

    map[i]=v;
  }

};


/*

  Clause-DB structure:

    DBs: db_id -> DB
    DB: db_ofs -> lit_t

  db_id,db_ofs packed in one size_t, 10 bit db_id

*/

class cofs {
  uint64_t packed;

public:
  cofs(size_t db_id = 0, size_t ofs = 0) : packed(0) {
    assert(db_id < (((uint64_t)1)<<10));
    assert(ofs < (((uint64_t)1)<<54));

    packed = (db_id<<54) | ofs;
  }

  size_t db() {return packed>>54;}
  size_t ofs() {return packed & (((uint64_t)1<<54) - 1);}

  operator bool() {return packed!=0;}


};

/*
  One database in parallel clause database assembly
*/
class ClauseDB_DB {
  vector<lit_t> db;
  uint32_t maxvar;

  // Id range for this database
  cid_t id_begin;
  cid_t id_end;

public:

  ClauseDB_DB(cid_t _id_begin, cid_t _id_end) : db(), maxvar(0), id_begin(_id_begin), id_end(_id_end) {
    db.push_back(lit_t::zero());
  }

  void check_range(cid_t id) {
    if (!(id_begin.val <= id.val && id.val < id_end.val))
      error("Id " + to_string(id) + " out of range " + " (" + to_string(id_begin) + " .. " + to_string(id_end) + ")");

  }


  template<typename R> size_t read_clause(charit_t &it, charit_t end) {
    // Read a clause
    size_t db_ofs = db.size();
    lit_t l;

    do {
      l=R::read_lit(it,end);
      db.push_back(l);
      maxvar=max(maxvar,l.var());
    } while (l);

    return db_ofs;
  }

  inline uint32_t get_maxvar() {return maxvar;}

  inline lit_t* lookup_ofs(size_t ofs) { assert(ofs<db.size()); return db.data()+ofs; }



};


class ClauseDB_Par {
  // Indexed by db-index
  vector<ClauseDB_DB> dbs;
  size_t num_dbs;

  struct entry {
    cofs ofs = cofs();                // Clause offset in db
    charit_t prf=nullptr;     // Pointer to (encoded) proof

    entry() {}
    entry(cofs _o, charit_t _p) : ofs(_o), prf(_p) {}

    operator bool() {return ofs; }

  };


  vector<entry> cmap;
  size_t num_ids;

  uint32_t maxvar = 0;

public:

  ClauseDB_Par(size_t _num_ids) : dbs(), num_dbs(0), cmap(_num_ids), num_ids(_num_ids) {
  }

  size_t add_db(cid_t id_begin,cid_t id_end) {
    assert(num_dbs == dbs.size());
    size_t res=num_dbs;
    dbs.push_back(ClauseDB_DB(id_begin,id_end));
    ++num_dbs;
    return res;
  }


  template<typename R> void read_clause(size_t dbi, cid_t id, charit_t &it, charit_t end) {
    assert(dbi<num_dbs);
    ClauseDB_DB &db = dbs[dbi];

    db.check_range(id);
    assert(id.val < cmap.size());

    CHECK(!cmap[id.val],"Duplicate id " + to_string(id));

    size_t ofs = db.read_clause<R>(it,end);

    cmap[id.val] = entry(cofs(dbi,ofs),it);

  }


  void compute_maxvar() {
    assert(maxvar==0);

    for (auto db : dbs) maxvar = max(maxvar,db.get_maxvar());
  }

  uint32_t get_maxvar() { assert(maxvar); return maxvar; }


  bool is_bound(cid_t id) {
    assert(id.val<num_ids);
    return cmap[id.val];
  }

  pair<lit_t*, charit_t> lookup_lemma(cid_t id) {
    assert(is_bound(id));
    auto e = cmap[id.val];

    size_t dbi=e.ofs.db();
    size_t dbofs = e.ofs.ofs();

    assert(dbi < num_dbs);

    lit_t *l = dbs[dbi].lookup_ofs(dbofs);

    return {l,e.prf};
  }


  lit_t* lookup_clause(cid_t id) {
    CHECK(id.val<num_ids,"Id out of range " + to_string(id));
    auto e = cmap[id.val];
    CHECK(e,"Id not bound " + to_string(id));

    size_t dbi=e.ofs.db();
    size_t dbofs = e.ofs.ofs();

    assert(dbi < num_dbs);

    lit_t *l = dbs[dbi].lookup_ofs(dbofs);

    return l;
  }



};


struct proof_segment {
  charit_t begin;
  charit_t end;

  cid_t id_begin;
  cid_t id_end;
};

void skip_to_zero_scid(charit_t &it, charit_t end) {
  while (it!=end) {
    if (!VBEnc_It::read_scid(it,end)) break;
  }
}



class Par_Reader {
  ClauseDB_Par &cdb;
  size_t this_dbi;

  proof_segment seg;


public:

  Par_Reader(ClauseDB_Par &_cdb, proof_segment _seg) : cdb(_cdb), this_dbi(0), seg(_seg) {
    this_dbi = cdb.add_db(seg.id_begin,seg.id_end);
  }


  void read_cnf() {
    cid_t::val_t id = seg.id_begin.val;

    charit_t it = seg.begin;

    while (it!=seg.end) {
      cdb.read_clause<CNF_It>(this_dbi,{id},it,seg.end);
      ++id;
    }

    CHECK(id == seg.id_end.val, "(Internal) id setup error " + to_string(id) + " != " + to_string(seg.id_end.val));

  }

  void read_proof() {
    charit_t it = seg.begin;

    while (it != seg.end) {

      char c = *(it++);

      if (c=='a') {
        // Read Id
        cid_t id = VBEnc_It::read_cid(it,seg.end);

        // Read clause
        cdb.read_clause<VBEnc_It>(this_dbi,id,it,seg.end);

        // Skip over proof
        skip_to_zero_scid(it,seg.end);
      } else if (c=='d') {
        // Ignore deletions
        skip_to_zero_scid(it,seg.end);
      } else {
        error("Unknown item code " + to_string(c));
      }
    }


  }





};



// Advance iterator beyond next zero
void advance_beyond_zero(charit_t &it, charit_t end) {
  for (;it!=end && *it;++it);
  if (it!=end) ++it;
}


cid_t find_first_id(charit_t it, charit_t end) {
  while (it!=end && *it!='a') advance_beyond_zero(it,end);

  if (it!=end) {
    ++it;
    return VBEnc_It::read_cid(it,end);
  } else {
    error("Proof must contain at least one 'a' item");
  }
}

/*
  File must end with addition of empty clause:

  (0|begin) a <id> 0 <sid>* 0

  Returns id one beyond last id

*/
cid_t find_last_id(charit_t begin, charit_t end) {
  charit_t it=end;
  CHECK(it!=begin,"Proof must not be empty");

  --it;
  CHECK(*it == 0,"Proof must end with 0");

  // Find middle zero
  do {
    CHECK(it!=begin,"Proof to short");
    --it;
  } while (*it);

  CHECK(it!=begin,"Proof to short");
  --it;

  // Find terminating zero of previous entry, or begin
  while (it!=begin && *(it-1)) --it;

  CHECK(*(it++) == 'a', "Last item must be 'a' item");

  cid_t res = VBEnc_It::read_cid(it,end);

  return {res.val+1};
}



/*
  find item boundary heuristics:

  We must find an 'a', and the corresponding id:

  0 'a' [^0]* 0 [^ad]

*/

cid_t find_boundary(charit_t &it, charit_t end) {

    while (it != end) {

      advance_beyond_zero(it,end);
      if (it==end) break;

      if (*it != 'a') continue;
      charit_t saved = it;

      advance_beyond_zero(it,end);

      if (it==end || (*it != 'a' && *it != 'd')) { // Found
        charit_t id_it = saved+1;
        cid_t id = VBEnc_It::read_cid(id_it,end);
        it=saved;
        return id;
      };
    }

    // Reached end
    assert(it==end);

    return {0};
}


std::atomic<uint64_t> cnt = 0;

bool check_range(ClauseDB_Par &cdb, cid_t id_begin, cid_t id_end, charit_t prf_end) {
    Assignment_CharV ass(cdb.get_maxvar());

    bool empty_clause = false;

    for (cid_t::val_t id = id_begin.val; id < id_end.val; ++id) {
      auto [clause,prf] = cdb.lookup_lemma({id});

      ass.reset_all();

      if (!*clause) empty_clause=true;

      // Negate literals of clause
      for (lit_t *l = clause;*l;++l) ass.set(-*l);

      // Check proof
      charit_t p = prf;

      bool invalid=false; // Will be set to true if something was odd with proof

      while (!invalid) {
        // Get next unit clause
        cid_t uid = VBEnc_It::read_scid(p,prf_end).cid(); // Note: we could assume that mapped memory does not change, and check earlier that each lemma ends with 0

        if (!uid) {
          invalid=true;
          break;
        }

        CHECK(uid.val < id, "Proofs must be ordered. Used id " + to_string(uid) + " in proof of clause " + to_string(id));


        // Find unit literal
        lit_t ulit=lit_t::zero();

        for (lit_t *l=cdb.lookup_clause(uid);*l;++l) {
          if (!ass.get(-*l)) {
            if (ulit) invalid=true;
            ulit=*l;
          }
        }

        if (!ulit) break; // Found conflict, we're done

        ass.set(ulit);
      }

      if (invalid) error("Invalid proof, for clause " + to_string(id));


      if (empty_clause) break;
    }


    return empty_clause;
}





int main(int argc, char**argv) {

  size_t num_threads = 128;

  if (argc!=3) error("usage: check <cnf-file> <lrat-file>");


//   #ifdef PROFILING
//   ProfilerStart("prof.out");
//   #endif

  MSG("Mapping cnf file");
  MMFile cnf(argv[1]);
  MSG("Mapping proof file");
  MMFile prf(argv[2]);


  // Setup CNF parsing
  charit_t cnf_it = cnf.begin();
  dimacs_header cnf_header = CNF_It::parse_dimacs_header(cnf_it,cnf.end());

  proof_segment cnf_seg = {cnf_it,cnf.end(),{1},{cid_t::val_t(cnf_header.num_clauses + 1)}};




  // Split
  vector<proof_segment> segs;

  cid_t prf_id_begin;
  cid_t id_end;

  {
    size_t prf_size = prf.end() - prf.begin();
    size_t seg_size = prf_size / num_threads;

    // Find first id
    prf_id_begin = find_first_id(prf.begin(),prf.end());
    cid_t cid = prf_id_begin;
    charit_t it = prf.begin();

    MSG("First id " + to_string(cid));


    // Advance
    while (true) {
      charit_t new_it = it;
      if ((size_t)(prf.end() - new_it) <= seg_size) break;
      new_it+=seg_size;

      cid_t new_cid = find_boundary(new_it,prf.end());

      if ((size_t)(prf.end() - new_it) < seg_size/2) break;
      assert(new_cid);

      // Create entry
      segs.push_back({it,new_it,cid, new_cid});

      it=new_it;
      cid=new_cid;
    }

    // Find last id
    assert(it!=prf.end());
    id_end=find_last_id(it,prf.end());
    segs.push_back({it,prf.end(),cid,id_end});

//     for (auto sg : segs) {
//       MSG("SEG " + to_string(sg.begin - prf.begin()) + " .. " + to_string(sg.end - prf.begin()) + "  IDs " + to_string(sg.id_begin) + " .. " + to_string(sg.id_end));
//     }

  }

  ClauseDB_Par cdb(id_end.val);

  // Do reading
  {
    Par_Reader cnf_reader(cdb,cnf_seg);

    vector<Par_Reader> prf_readers;

    for (auto seg : segs) prf_readers.emplace_back(Par_Reader(cdb,seg));

    tbb::task_group rd_tasks;

    MSG("Reading proof and cnf in parallel");

    rd_tasks.run([&] {cnf_reader.read_cnf();});

    for (size_t i=0; i<prf_readers.size();++i) // Avoid reference-capture of iterator variable (TODO: there must be a better way than resorting to by-index-iteration)
      rd_tasks.run([i,&prf_readers] {prf_readers[i].read_proof();});

    rd_tasks.wait();

    MSG("Done");
  }

  // Do checking

  #ifdef PROFILING
  ProfilerStart("prof_par.out");
  #endif

  MSG("Checking");

  cdb.compute_maxvar();

  size_t num_lemmas = id_end.val - prf_id_begin.val;

  size_t seg_size = (num_lemmas + num_threads - 1) / num_threads;

  assert(seg_size);

  vector<bool> results(num_threads,false);

  tbb::task_group chk_tasks;

  cid_t::val_t id = prf_id_begin.val;
  for (size_t i = 0; i<num_threads && id < id_end.val; ++i) {
    cid_t::val_t next_id = min(id+(cid_t::val_t)seg_size,id_end.val);

    chk_tasks.run([i,id,next_id,&results,&cdb,&prf] { results[i] = check_range(cdb,{id},{next_id},prf.end()); });

    id = next_id;
  }

  chk_tasks.wait();

  bool has_empty=false;
  for (size_t i=0; i<num_threads; ++i) {
    cout<<results[i]<<" ";
    has_empty = has_empty || results[i];
  }
  cout<<endl;




//   bool has_empty = check_range(cdb,prf_id_begin,id_end,prf.end());

  CHECK(has_empty,"No empty clause found");

  MSG("COUNT: " + to_string(cnt));

  MSG("s VERIFIED UNSAT");

  #ifdef PROFILING
  ProfilerStop();
  #endif


  return 0;
//   /*
//   size_t x = 0;
//
//   MSG("Test read");
//   for (charit_t i=cnf.begin(); i!=cnf.end();++i) x+= *i;
//   for (charit_t i=prf.begin(); i!=prf.end();++i) x+= *i;
//   MSG("Done " + to_string(x));
//
//   return 0;
//   */
//
//
//   ClauseDB_Par db;
//
//   MSG("Reading CNF");
//   db.read_cnf(cnf.begin(),cnf.end());
//
//   MSG("maxvar = " + to_string(db.get_maxvar()) + " last_id = " + to_string(db.get_lastid()));
//
//   MSG("Reading Proof");
//   db.read_proof(prf.begin(),prf.end());
//
//   MSG("maxvar = " + to_string(db.get_maxvar()) + " last_id = " + to_string(db.get_lastid()));
//
//   MSG("Checking");
//
//   Checker chk(db);
//
//   chk.check(prf.end());
//
//   MSG("s VERIFIED UNSAT");
//
//
//   return 0;
}

/*
  xxx: ctd here
    to be able to build id database without a data-race,
    we must split at 'a' entries, and assign id ranges to each part!*/




// class ClauseDB_Par {
//
// public:
//
//
//
//
//   struct entry {
//     cofs ofs;                // Clause offset in db
//     charit_t prf=nullptr;     // Pointer to (encoded) proof
//
//     entry() {}
//     entry(cofs _o, charit_t _p) : ofs(_o), prf(_p) {}
//
//     bool is_valid() {return ofs.ofs()!=0; }
//
//   };
//
// private:
//
//   nat_map<entry> cid_map = nat_map<entry>();
//
//   uint32_t this_db = 0;
//   vector<lit_t> db = vector<lit_t>();
//
//   cid_t::val_t last_id = 0;
//   cid_t::val_t first_lemma_id=0;
//
//   uint32_t maxvar = 0;
//
//
//
//   template<typename R> inline cofs read_clause(charit_t &it, charit_t end) {
//     // Read a clause
//     size_t db_ofs = db.size();
//     lit_t l;
//
//     do {
//       l=R::read_lit(it,end);
//       db.push_back(l);
//       maxvar=max(maxvar,l.var());
//     } while (l);
//
//     return cofs(this_db,db_ofs);
//   }
//
//
//   void skip_to_zero_scid(charit_t &it, charit_t end) {
//     while (it!=end) {
//       if (!VBEnc_It::read_scid(it,end)) break;
//     }
//   }
//
//
//
//
//
//
//
// public:
//
//
//   ClauseDB_Par() {
//     db.push_back(lit_t::zero()); // Push a dummy
//   }
//
//   void read_cnf(charit_t it, charit_t end) {
//     cid_t::val_t id = 0;
//
//     CNF_It::parse_dimacs_header(it,end);
//
//     while (it!=end) {
//       size_t ofs = read_clause<CNF_It>(it,end);
//       // Register that clause
//       ++id;
//       cid_map.set(id, {ofs,nullptr});
//     }
//     last_id=id;
//   }
//
//
//   void read_proof(charit_t it, charit_t end) {
//
//     while (it != end) {
//
//       char c = *(it++);
//
//       if (c=='a') {
//         // Read Id
//         cid_t id = VBEnc_It::read_cid(it,end);
//
//         if (id.val <= last_id) error("IDs must be in increasing order " + to_string(id.val) + " (last: "+to_string(last_id)+")");
//
//         if (!first_lemma_id) first_lemma_id = id.val;
//
//         // Read clause
//         size_t ofs = read_clause<VBEnc_It>(it,end);
//
//         // Register that clause, with current iterator as start of proof
//         cid_map.set(id.val, {ofs,it});
//
//         last_id=id.val;
//
//         // Skip over proof
//         skip_to_zero_scid(it,end);
//       } else if (c=='d') {
//         // Ignore deletions
//         skip_to_zero_scid(it,end);
//       }
//     }
//   }
//
//   uint32_t get_maxvar() {return maxvar; }
//
//   cid_t::val_t get_lastid() {return last_id;}
//   cid_t::val_t get_first_lemma_id() {return first_lemma_id;}
//
//
//   inline bool is_valid_id(cid_t id) {
//     return cid_map.get(id.val).is_valid();
//   }
//
//   inline entry lookup(cid_t id) {return cid_map.get(id.val); }
//
//   inline lit_t* get_clause(size_t ofs) { return db.data() + ofs; }
//
//
// };
//
// class Checker {
//   ClauseDB_Par &db;
//   Assignment_CharV ass;
//
// public:
//     Checker(ClauseDB_Par &_db) : db(_db), ass(_db.get_maxvar()) {
//
//     }
//
//
//     void check(charit_t end) {
//
//       size_t cnt=0;
//
//       for (cid_t::val_t id=db.get_first_lemma_id();id<=db.get_lastid();++id) {
//         ClauseDB_Par::entry e = db.lookup({id});
//
//         ass.reset_all();
//
//         // Negate literals of clause
//         for (lit_t *l=db.get_clause(e.db_ofs);*l;++l) {
//           ass.set(-*l);
//         }
//
//         // Check proof
//         charit_t p = e.prf;
//
//         bool invalid=false; // Will be set to true if something was odd with proof
//
//         while (!invalid) {
//           // Get next unit clause
//           scid_t uid = VBEnc_It::read_scid(p,end); // Note: we could assume that mapped memory does not change, and check earlier that each lemma ends with 0
//
//           if (!db.is_valid_id(uid.cid())) { // Check for valid id ... if we ever read 0 here (proof ended before conflict), this will also count as invalid id
//             invalid=true;
//           } else {
//             // Find unit literal
//             lit_t ulit=lit_t::zero();
//
//             for (lit_t *l=db.get_clause(e.db_ofs);*l;++l) {
//               ++cnt;
//               if (!ass.get(-*l)) {
//                 if (ulit) invalid=true;
//                 ulit=*l;
//               }
//             }
//
//             if (!ulit) break; // Found conflict, we're done
//             ass.set(ulit);
//           }
//         }
//
//         if (invalid) error("Invalid proof, for clause " + to_string(id));
//
//
//       }
//
//
//       MSG("Cnt " + to_string(cnt));
//
//     }
//
//
//
//
// };
