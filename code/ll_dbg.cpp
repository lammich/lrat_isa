#include <iostream>
#include <stdint.h>

using namespace std;


const int64_t PARSED_CNF_LIT  = 0x1;
const int64_t PARSED_LRAT_ADD = 0x2;
const int64_t PARSED_LRAT_LIT = 0x3;
const int64_t PARSED_LRAT_ID  = 0x4;

int64_t decode_lit(int64_t l) { if (l&0x1) return -(l/2); else return l/2; }


extern "C" {

void LRAT_Checker_Impl_ll_dbg_fun_parsed_cnf_impl(char x) {
  cout<<"LL_DBG: parsed CNF "<<(int)x<<endl;
}

void Debugging_Tools_ll_dbg_fun_err_code_impl(int64_t code, int64_t extra) {
  cout<<"LL_DBG: error code "<<code<<"  (extra: "<<extra<<")"<<endl;
}

void Debugging_Tools_ll_dbg_fun_info_code_impl(int64_t code, int64_t extra) {
  cout<<"LL_DBG: info code "<<code<<"  (extra: "<<extra<<")"<<endl;
}



void Debugging_Tools_ll_dbg_fun_parsed_impl(int64_t code, int64_t info) {
  switch (code) {
    case PARSED_CNF_LIT:
      cout<<decode_lit(info);
      if (info) cout<<" "; else cout<<endl;
      break;
    case PARSED_LRAT_ADD:
      cout<<"a "<<info<<" ";
      break;
    case PARSED_LRAT_LIT:
      cout<<decode_lit(info)<<" ";
      break;
    case PARSED_LRAT_ID:
      cout<<info;
      if (info) cout<<" "; else cout<<endl;
      break;

    default:
      cout<<endl<<"?? "<<code<<"  "<<info<<endl;
  }


}




}
