#include <vector>
#include <cassert>
#include <cstdlib>

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



class ClauseDB_Par {

public:
  struct entry {
    size_t db_ofs=0;    // Clause offset in db
    charit_t prf=nullptr;     // Pointer to (encoded) proof

    entry() {}
    entry(size_t _o, charit_t _p) : db_ofs(_o), prf(_p) {}

    bool is_valid() {return db_ofs!=0; }

  };

private:

  nat_map<entry> cid_map = nat_map<entry>();

  vector<lit_t> db = vector<lit_t>();

  cid_t::val_t last_id = 0;
  cid_t::val_t first_lemma_id=0;

  uint32_t maxvar = 0;



  template<typename R> inline size_t read_clause(charit_t &it, charit_t end) {
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


  void skip_to_zero_scid(charit_t &it, charit_t end) {
    while (it!=end) {
      if (!VBEnc_It::read_scid(it,end)) break;
    }
  }


public:


  ClauseDB_Par() {
    db.push_back(lit_t::zero()); // Push a dummy
  }

  void read_cnf(charit_t it, charit_t end) {
    cid_t::val_t id = 0;

    CNF_It::parse_dimacs_header(it,end);

    while (it!=end) {
      size_t ofs = read_clause<CNF_It>(it,end);
      // Register that clause
      ++id;
      cid_map.set(id, {ofs,nullptr});
    }
    last_id=id;
  }


  void read_proof(charit_t it, charit_t end) {

    while (it != end) {

      char c = *(it++);

      if (c=='a') {
        // Read Id
        cid_t id = VBEnc_It::read_cid(it,end);

        if (id.val <= last_id) error("IDs must be in increasing order " + to_string(id.val) + " (last: "+to_string(last_id)+")");

        if (!first_lemma_id) first_lemma_id = id.val;

        // Read clause
        size_t ofs = read_clause<VBEnc_It>(it,end);

        // Register that clause, with current iterator as start of proof
        cid_map.set(id.val, {ofs,it});

        last_id=id.val;

        // Skip over proof
        skip_to_zero_scid(it,end);
      } else if (c=='d') {
        // Ignore deletions
        skip_to_zero_scid(it,end);
      }
    }
  }

  uint32_t get_maxvar() {return maxvar; }

  cid_t::val_t get_lastid() {return last_id;}
  cid_t::val_t get_first_lemma_id() {return first_lemma_id;}


  inline bool is_valid_id(cid_t id) {
    return cid_map.get(id.val).is_valid();
  }

  inline entry lookup(cid_t id) {return cid_map.get(id.val); }

  inline lit_t* get_clause(size_t ofs) { return db.data() + ofs; }


  inline lit_t* lookup_clause(cid_t id) {
    assert(is_valid_id(id));
    return get_clause(lookup(id).db_ofs);
  }


};

uint64_t cnt=0;


class Checker {
  ClauseDB_Par &db;
  Assignment_CharV ass;

public:
    Checker(ClauseDB_Par &_db) : db(_db), ass(_db.get_maxvar()) {

    }


    void check(charit_t end) {
      bool empty_clause=false; // True, if empty clause has been added

      for (cid_t::val_t id=db.get_first_lemma_id();id<=db.get_lastid();++id) {
        ClauseDB_Par::entry e = db.lookup({id});

        ass.reset_all();

        {
          lit_t *l = db.get_clause(e.db_ofs);

          if (!*l) empty_clause=true;

          // Negate literals of clause
          for (;*l;++l) ass.set(-*l);
        }

        // Check proof
        charit_t p = e.prf;

        bool invalid=false; // Will be set to true if something was odd with proof

        while (!invalid) {
          // Get next unit clause
          scid_t uid = VBEnc_It::read_scid(p,end); // Note: we could assume that mapped memory does not change, and check earlier that each lemma ends with 0


          if (!db.is_valid_id(uid.cid())) { // Check for valid id ... if we ever read 0 here (proof ended before conflict), this will also count as invalid id
            invalid=true;
          } else {
            // Find unit literal
            lit_t ulit=lit_t::zero();

            for (lit_t *l=db.lookup_clause(uid.cid());*l;++l) {
              if (!ass.get(-*l)) {
                if (ulit) invalid=true;
                ulit=*l;
              }
            }

            if (!ulit) break; // Found conflict, we're done

            ass.set(ulit);
          }
        }

        if (invalid) error("Invalid proof, for clause " + to_string(id));


        if (empty_clause) break;
      }

      if (!empty_clause) error("Proof contains no empty clause");


    }




};

/*
  find item boundary heuristics:


  0 'a' [^0]* 0 [^ad]  -- this must be an add item. found.

  0 'd' [^0]* 0 -- Definitely at start of item here.
  0 [^ad] [^0]* 0 -- Definitely at start of item here

*/

void find_boundary(charit_t &it, charit_t end) {
  // Search for zero
  for (;it!=end && *it;++it);

  while (it!=end) {
    char c=*(it++);
    // Advance to next zero
    for (;it!=end && *it;++it);

    if (c!='a') return; // If character was not an 'a', we are definitely at item boundary
  }
}







int main(int argc, char**argv) {


  if (argc!=3) error("usage: check <cnf-file> <lrat-file>");

  MSG("Mapping cnf file");
  MMFile cnf(argv[1]);
  MSG("Mapping proof file");
  MMFile prf(argv[2]);

  /*
  size_t x = 0;

  MSG("Test read");
  for (charit_t i=cnf.begin(); i!=cnf.end();++i) x+= *i;
  for (charit_t i=prf.begin(); i!=prf.end();++i) x+= *i;
  MSG("Done " + to_string(x));

  return 0;
  */


  ClauseDB_Par db;

  MSG("Reading CNF");
  db.read_cnf(cnf.begin(),cnf.end());

  MSG("maxvar = " + to_string(db.get_maxvar()) + " last_id = " + to_string(db.get_lastid()));

  MSG("Reading Proof");
  db.read_proof(prf.begin(),prf.end());

  MSG("maxvar = " + to_string(db.get_maxvar()) + " last_id = " + to_string(db.get_lastid()));

  #ifdef PROFILING
  ProfilerStart("prof_ss.out");
  #endif


  MSG("Checking");

  Checker chk(db);

  chk.check(prf.end());

  MSG("COUNT: " + to_string(cnt));

  MSG("s VERIFIED UNSAT");

  #ifdef PROFILING
  ProfilerStop();
  #endif

  return 0;
}

