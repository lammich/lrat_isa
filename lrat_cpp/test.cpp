#include <iostream>
#include <vector>
#include <cassert>
#include <cstdlib>

#include <boost/timer/timer.hpp>


#include "MMFile.h"
#include "Logging.h"

using namespace std;
using namespace boost::timer;


inline void skip_to(char c,char const *&it, char const *end) {
  while (it != end) {
    if (*(it++) == c) break;
  }
}

inline bool is_whitespace(char c) {
  return c==' ' || (10<=c && c<=15);
}

inline void skip_over_whitespace(char const *&it, char const *end) {
  while (it!=end && is_whitespace(*it)) ++it;
}


uint32_t scan_literal(char const *&it, char const *end) {
  assert(it!=end);

  uint64_t res=0;
  bool sign = false;

  if (*it == '-') { ++it; sign=true; }

  if (it==end) error("Parse error, incomplete literal");

  auto it0 = it;
  bool zero = *it=='0';

  while (it!=end) {
    char c = *it;
    if (is_whitespace(c)) break;

    if (c<'0' || c>'9') error("Parse error, invalid character in literal");

    res += 10*res + (c-'0');
    ++it;
  }

  uint64_t n = it-it0;

  if (!n) error("Parse error, incomplete literal");
  if (zero && n!=1) error("Parse error, leading zero");
  if (zero && sign) error("Parse error, -0");


  return (res*2) + (sign?1:0);
}

template <typename F> void iterate_dimacs_naive(char const *begin, char const *end, F f) {

  auto it = begin;

  // Ignore headers and comments
  while (it!=end) {
    skip_over_whitespace(it,end);
    if (it==end) break;
    if (*it == 'c' || *it == 'p') skip_to('\n',it,end); else break;
  }

  // Scan numbers and whitespace. Assume we have skipped whitespace here

  assert(it==end || !is_whitespace(*it));

  while (it!=end) {
    // Scan literal
    uint32_t l = scan_literal(it,end);
    f(l);

    skip_over_whitespace(it,end);
  }

}


template <typename F> void iterate_chars_naive(char const *begin, char const *end, F f) {
  assert(begin<=end);

  for (char const* i=begin;i!=end;++i) f(*i);
}

template <typename F> void iterate_chars(char const *begin, char const *end, F f) {
  assert(begin<=end);

  size_t sz = end-begin;

  size_t sz1 = sz / sizeof(uint64_t);

  uint64_t const *i = (uint64_t const *)begin;
  uint64_t const *end2 = i + sz1;

  for (;i!=end2;++i) {
    uint64_t w = *i;
    for (size_t shift=0; shift<sizeof(uint64_t);++shift) {
      char c = w&0xFF;
      w = w >> 8;
      f(c);
    }
  };

  char const *j = (char const*)end2;
  for (;j<end;++j) f(*j);
}



void decode_vc_naive(char const *begin, char const *end, vector<uint32_t> &dst) {

    uint32_t acc=0;
    uint32_t shift=0;
    for (char const* i=begin;i!=end;++i) {
      char c = *i;

      acc |= (c & 0x7F) << shift;
      shift = (shift + 7) % (8*sizeof(uint32_t)); // Just a quick way to avoid undefined behaviour by over-shifting
      if ((c&0x80) == 0) {
        dst.push_back(acc);
        acc=0;
        shift=0;
      };
    }
}

void decode_vc_naive2(char const *begin, char const *end, vector<uint32_t> &dst) {

    cpu_timer timer;

    uint32_t acc=0;
    uint32_t shift=0;

    iterate_chars_naive(begin,end,[&](char c) {
      acc |= (c & 0x7F) << shift;
      shift = (shift + 7) % (8*sizeof(uint32_t)); // Just a quick way to avoid undefined behaviour by over-shifting
      if ((c&0x80) == 0) {
        dst.push_back(acc);
        acc=0;
        shift=0;
      };
    });

    cout<<"Decoded lrat "<<timer.format();
}


void decode_vc(char const *begin, char const *end, vector<uint32_t> &dst) {

    uint32_t acc=0;
    uint32_t shift=0;

    iterate_chars(begin,end,[&](char c) {
      acc |= (c & 0x7F) << shift;
      shift = (shift + 7) % (8*sizeof(uint32_t)); // Just a quick way to avoid undefined behaviour by over-shifting
      if ((c&0x80) == 0) {
        dst.push_back(acc);
        acc=0;
        shift=0;
      };
    });

}


template<typename I> size_t skip_to_zero(I &i, I end) {
  size_t res=0;
  while (i!=end) {
      if (*(i++)==0) break;
      ++res;
  }
  return res;
}


template<typename V> size_t skip_to_zeroidx(V const &data, size_t &i, size_t end) {
  size_t res=0;
  while (i!=end) {
      if (data[i++]==0) break;
      ++res;
  }
  return res;
}


inline int32_t to_signed(uint32_t x) {
  if (x&0x1) return -(x>>1); else return x>>1;
}

// Do not return negative number
inline uint32_t to_signed_id(uint32_t x) {
  return x>>1;
}


template<typename I> uint32_t read1(I &i, I end) {
  if (i!=end) return *(i++); else return 0;
}

template<typename I> int32_t reads1(I &i, I end) {
  return to_signed(read1(i,end));
}

template<typename V> uint32_t read1idx(V const &data, size_t &i, size_t end) {
  if (i!=end) return data[i++]; else return 0;
}

template<typename V> int32_t reads1idx(V const &data, size_t &i, size_t end) {
  return to_signed(read1idx(data,i,end));
}



void lrat_stats(vector<uint32_t> &lrat) {

  auto i = lrat.begin();

  size_t adds=0;
  size_t dels=0;
  size_t invalids=0;
  size_t num_dcs = 0;

  cpu_timer timer;

  auto end = lrat.end();

  while (i != end) {
    uint32_t cmd = read1(i,end);

    if (cmd == 'a') {
      adds++;
      read1(i,end);
      skip_to_zero(i,end);
      skip_to_zero(i,end);
    } else if (cmd == 'd') {
      dels++;
      num_dcs+=skip_to_zero(i,end);
    } else {
      invalids++;
      skip_to_zero(i,end);
    }

  }

  cout<<adds<<" additions, "<<num_dcs<<" deletions in "<<dels<<" blocks , "<<invalids<<" unrecognized commands"<<endl;
  cout<<num_dcs/dels <<" ids / deletion"<<endl;

  cout<<"Time "<<timer.format()<<endl;
}



template<typename I> void dump(I i, I end, size_t max_block) {
  enum {
    Init,Add1,Add2,Add3,Del
  } state = Init;

  size_t blocks=0;

  for (;i!=end && blocks<max_block;++i) {
    uint32_t d = *i;
    switch (state) {
      case Init:
        if (d=='a') {
          cout<<"a ";
          state=Add1;
        } else if (d=='d') {
          cout<<"d ";
          state=Del;
        } else {
          cout<<"?("<<d<<")"<<endl;
          ++blocks;
        }
        break;
      case Add1: {
        int32_t l=to_signed(d);
        cout<<l<<" ";
        if (l==0) state=Add2;
        break;
      }
      case Add2: {
        int32_t id=to_signed(d);
        cout<<id<<" ";
        if (id==0) state=Add3;
        break;
      }
      case Add3:
        cout<<d<<endl;
        ++blocks;
        state=Init;
        break;

      case Del:
        cout<<d;
        if (d==0) {
          cout<<endl;
          ++blocks;
          state=Init;
        } else {
          cout<<" ";
        }
        break;
    }
  }
}

/*
  Backwards readable format

  - move id of clause to end (thus we can read it, and then decide whether to mark ids)
    for forward checking, we only need id after clause has been checked.


  a 0 lits 0 uids 0 id a


  d 0 uids 0 d



*/

/*
==> NOT yet backward readable! we cannot skip backwards to start of a/d, because a/d may be valid clauses/ids!

-> for backward readable (and quickly jumpable) format, we could create id->ofs index.

ctd here: instead of converting to bwlrat, create an id/ofs index (this could be done also for compressed format).


Other options:
one-pass backward checkable format:
-> on deletions, both clause-id and clause is mentioned???
How can we achieve checking with one backward pass?
  relevant clauses need to be in memory.
  we could require deletions with id+literals for all (used) clauses.
  On addition, we would just mention the ids.

  then, we would load the clauses on deletion, and remove them when they are added (and justified via clauses still loaded).

  to generate such an output format directly from sat-solver, we have to output literals of clause on deletion.

  -> generate such a format as experiment, and play with backward checking over it!
*/




template<typename I> void to_bwlrat(I it, I end) {
  cpu_timer timer;

  while (it!=end) {
    uint32_t cmd = read1(it,end);

    if (cmd == 'a') {
      uint32_t id=read1(it,end);

      // Shift
      do { if (it==end) break; *it = *(it+1); ++it; } while (*it);
      do { if (it==end) break; *it = *(it+1); ++it; } while (*it);

      // Place id last
      if (it!=end) {
        *it=id;
        ++it;
      }
    } else if (cmd == 'd') {
      skip_to_zero(it,end);
    }
  }

  cout<<"Converted "<<timer.format();
}


template<typename E> void set(vector<E> &v, size_t i, E x) {
  if (i>=v.size()) v.resize(i+1);
  v[i]=x;
}

template<typename E> E get(vector<E> const &v, size_t i) {
  if (i<v.size()) return v[i]; else return 0;
}

// Only the additions
template<typename V> void mk_item_map(V const &data, size_t it, size_t end, vector<size_t> &items) {

  cpu_timer timer;

  while (it!=end) {
    uint32_t cmd = read1idx(data,it,end);

    if (cmd == 'a') {
      items.push_back(it);
      skip_to_zeroidx(data,it,end);
    }
    skip_to_zeroidx(data,it,end);
  }

  cout<<"Built item map "<<timer.format();
  cout<<"Stored "<<items.size()<<" items. Overhead "<<items.size()*sizeof(uint32_t const*)/1024.0/1024<<" MiB"<<endl;

}


template<typename I> void dump_us(I &it) {
  for (;*it;++it) cout<<*it<<" ";
  cout<<*it;
  ++it;
}

template<typename I> void dump_s(I &it) {
  for (;*it;++it) cout<<to_signed(*it)<<" ";
  cout<<*it;
  ++it;
}

template<typename I> void dump_add(I it) {
  cout<<*(it++)<<" ";
  dump_s(it);
  cout<<" ";
  dump_s(it);
  cout<<endl;
}

template<typename V> void bwd_trimmer(V const &data, vector<size_t> const &items, vector<bool> &marked) {
  if (!items.size()) return;

  cpu_timer timer;

  // Mark last id
  set(marked,data[items.back()],true);

  // Now run backwards through items
  {
    auto iit=items.end();
    while (iit!=items.begin()) {
      --iit;

      size_t it = *iit;  // it points to start of add item, e.g.,  id lits 0 uids 0
      // We assume that there are actually two zeros! TODO not yet checked, but check while creating items!

      // dump_add(it);

      uint32_t id = data[it]; // Id of this item

      if (get(marked,id)) {
        // Id of this item is marked. Mark other ids
        for (;data[it++]; ); // Skip over id and lits. TODO rearranging the format could help us omitting this step!

        for (;data[it]; ++it) {
          uint32_t did = to_signed_id(data[it]); // Id of dependency
          set(marked,did,true);
        }
      }
    }
  }

  cout<<"Marking done "<<timer.format();
}


template<typename V> void fwd_checker(V const &data, vector<size_t> const &items, vector<bool> const marked, vector<size_t> &id_map) {
  // Map literals to value
  // Current encoding: ass[l] == true iff l is FALSE.
  vector<bool> ass; // TODO, try char (i.e., non bit-packed)


  // Iterate over items
  for (auto it : items) {
    uint32_t id = data[it];
    if (get(marked,id)) {
      ++it;
      // Check
      auto lits = it;

      // Assign literals
      for (;data[it];++it) set(ass,data[it],true);

      ++it;
      // Iterate over unit clause ids
      for (;data[it];++it) {
        uint32_t id = to_signed_id(data[it]);

        // Check if unit
        uint32_t ulit=0;




      }




    }
  }







}





// Expecting dlrat
// template<typename I> void simple_trimmer(I begin, I it, vector<bool> &marked) {
//   if (it==begin) return;
//   --it;
//
//   // Last one should be addition (of empty clause). We mark that
//   if (!*it) error("Expected addition as last item");
//   set(marked,*it);
//
//   do {
//     bool is_add = *it;
//
//     if (is_add) {
//
//     } else {}
//
//
//
//   } while (it!=begin);
//
//
// }



void decode_cnf(char const *begin, char const *end, vector<uint32_t> &data, vector<size_t> &id_map) {
  cpu_timer timer;
  size_t id=1;
  if (!data.size()) data.push_back(0); // Make zero an invalid index, to mark invalid ids in id-map
  size_t last_c = data.size();

  iterate_dimacs_naive(begin,end,[&](uint32_t l) {
    // cout<<"lit "<<l<<endl;
    data.push_back(l);

    if (!l) {
      set(id_map,id,last_c);
      ++id;
      last_c=data.size();
    }
  });

  cout<<"Decoded cnf "<<timer.format();
  cout<<id-1<<" clauses, and "<<data.size()<<" literals "<<endl;

  size_t mem = (data.size() + id_map.size())*sizeof(uint32_t);

  cout<<"Memory "<<mem/1024.0/1024<<"MiB"<<endl;
}






int main(int argc, char** argv) {

  if (argc!=3) error("Usage test <cnf-file> [<lrat-file>]");

  vector<uint32_t> cdata;
  vector<size_t> id_map;
  {
    MMFile cnf(argv[1]);
    decode_cnf(cnf.begin(),cnf.end(),cdata,id_map);
  }

  size_t lrat_begin = cdata.size();

  {
    MMFile lrat(argv[2]);
    decode_vc_naive2(lrat.begin(), lrat.end(),cdata);
  }

  {
    size_t mem = (cdata.size() + id_map.size())*sizeof(uint32_t);
    cout<<"Memory "<<mem/1024.0/1024<<"MiB"<<endl;
  }

  vector<size_t> items;
  mk_item_map(cdata,lrat_begin,cdata.size(),items);

  vector<bool> marked;
  bwd_trimmer(cdata,items,marked);


  {
    size_t nm=0;
    for (auto m : marked) if (m) ++nm;
    cout<<nm<<" marked clauses"<<endl;
  }


//   {
//     for (uint32_t id=1;id<id_map.size();++id) {
//       uint32_t i = id_map[id];
//       assert(i);
//
// //       cout<<"idx "<<i<<endl;
//
//       while (true) {
//         uint32_t l = cdata[i++];
//         if (l==0) break;
//         cout<<to_signed(l)<<" ";
//       }
//       cout<<"0"<<endl;
//     }
//
//   }

  // MMFile lrat(argv[3]);






/*
  vector<uint32_t> dec;

  cpu_timer t_decode;

  if (string(argv[1]) == "naive") {
    decode_vc_naive2(f.begin(), f.end(),dec);
  } else if (string(argv[1]) == "64") {
    decode_vc(f.begin(), f.end(),dec);
  } else error("Unknown mode");


  cout<<"Decoded  "<<t_decode.format();

  cout<<"Compressed size "<<f.size()/1024.0/1024<<" MiB"<<endl;
  cout<<"Decoded size    "<<dec.size()*sizeof(uint32_t)/1024.0/1024<<" MiB"<<endl;

  cout<<"Size ratio decoded/compressed: "<<dec.size()*sizeof(uint32_t)*1.0/f.size()<<endl;

  vector<vector<uint32_t>::iterator> items;
  mk_item_map(dec.begin(),dec.end(),items);

  vector<bool> marked;
  bwd_trimmer(items,marked);
*/

  // to_bwlrat(dec.begin(),dec.end());
  // dump(dec.begin(),dec.end(),5);

//   {
//     size_t blk=0;
//     for (size_t i=0;i<dec.size() && blk<5;++i) {
//       cout<<dec[i];
//
//       if (dec[i] == 0) { ++blk; cout<<endl;}
//       else cout<<" ";
//     }
//
//     cout<<endl;
//   }

  // Compute a checksum
  // lrat_stats(dec);
//   uint64_t res=0;
//   for (auto v : dec) res+=v;


//   cout<<"Checksum "<<res<<"  ("<< dec.size() <<" words )"<<endl;

  return 0;
}







