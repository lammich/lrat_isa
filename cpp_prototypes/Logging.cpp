#include "Logging.h"
#include <boost/stacktrace.hpp>
#include <cstdlib>
#include <iostream>

using namespace std;

void log_aux(string msg) {
    clog<<"c "<<msg<<endl;
}

unsigned int loglevel=1;

[[noreturn]] void error(string msg) {
    cerr<<"c ERROR: "<<msg<<endl;
    cerr<< boost::stacktrace::stacktrace();
    exit(1);
}


