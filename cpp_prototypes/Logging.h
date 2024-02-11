#pragma once

#include <string>

void log_aux(std::string msg);

extern unsigned int loglevel;

#define LOG(l,msg) do {if ((l)<loglevel) log_aux(msg);} while (0)

const unsigned int LL_MSG = 0;
const unsigned int LL_VMSG = 1;
const unsigned int LL_DBG = 2;

#define MSG(msg) LOG(LL_MSG,msg)
#define VMSG(msg) LOG(LL_VMSG,msg)
#define DBG(msg) LOG(LL_DBG,msg)


[[noreturn]] void error(std::string msg);

#define CHECK(c,msg) do {if (!(c)) error(msg);} while (0)

// inline void check(bool c, std::string msg) {
//     if (!c) error(msg);
// }

