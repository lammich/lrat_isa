#include <algorithm>
#include <iostream>

#include <boost/iostreams/device/mapped_file.hpp>

#include <cstdio>

extern "C" {
  #include "lrat_isa_export.h"
  // #include <sys/mman.h>
}


FILE *proof_file = nullptr;

extern "C" {
  size_t fread_from_proof(void *p, size_t n) {
    if (!proof_file) return 0;

    return fread(p,1,n,proof_file);
  }
}


class MMFile {
    boost::iostreams::mapped_file mf;
    const char* mbegin = nullptr;
    size_t msize = 0;

    MMFile(const MMFile&) = delete;

    MMFile &operator=(const MMFile&) = delete;

public:
    MMFile(std::string name) : mf() {
        boost::iostreams::mapped_file_params params;
        params.path = name;
        //params.length = 512; // default: complete file
        //params.new_file_size = pow(1024, 2); // 1 MB
        params.flags = boost::iostreams::mapped_file::mapmode::readonly;

        mf.open(params);

        mbegin = mf.const_data();
        msize = mf.size();
    }

    ~MMFile() {
        mf.close();
    }

    inline size_t size() {return msize; }

    inline const char * begin() { return mbegin; }
};







using namespace std;


int main(int argc, char**argv) {

  if (argc!=2 && argc!=3) {
    cerr<<"usage: check <cnf-file> [<lrat-file>]"<<endl;
    cerr<<"  if lrat-file is not specified, it is read from standard input"<<endl;
    return 1;
  }

  string cnf_name = argv[1];

  const char* prf_name = argc==3?argv[2]:nullptr;

  MMFile cnf(cnf_name);
  // MMFile prf(prf_name);

  // posix_madvise((void*)cnf.begin(),cnf.size(),POSIX_MADV_SEQUENTIAL);
  // posix_madvise((void*)prf.begin(),prf.size(),POSIX_MADV_SEQUENTIAL);

  if (prf_name) {
    proof_file = fopen(prf_name,"r");
  } else {
    proof_file = stdin;
  }

  if (!proof_file) {
    cerr<<"Error opening proof file '"<<proof_file<<"'"<<endl;
    return 1;
  }


  bool res = lrat_checker((uint8_t*)cnf.begin(),cnf.size());

  fclose(proof_file);
  proof_file=NULL;


  if (res) {
    cout<<"s VERIFIED UNSAT"<<endl;
    return 0;
  } else {
    cout<<"c ERROR"<<endl;
    return 1;
  }
}
