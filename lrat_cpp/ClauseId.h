#pragma once

#include <string>
#include <cstdlib>


struct cid_t {
    typedef uint32_t val_t;
    val_t val;
    explicit operator bool() {return val!=0;}

    bool is_pos() {return val>0;}

};

std::string to_string(cid_t l) {return std::to_string(l.val);}


struct scid_t {
    typedef int32_t val_t;

    val_t val;

    explicit operator bool() {return val!=0;}

    cid_t cid() {
        return {static_cast<cid_t::val_t>(abs(val))};
    }

    bool is_negative() {return val<0;}

};

std::string to_string(scid_t l) {return std::to_string(l.val);}
