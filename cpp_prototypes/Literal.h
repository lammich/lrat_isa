#pragma once

#include <string>
#include <cstdlib>

struct lit_t {

    typedef int32_t val_t;

    val_t val;

    explicit operator bool() {return val!=0;}
    lit_t operator -() {return {-val}; }

    uint32_t var() {return abs(val);}
    bool is_pos() {return val>=0;}

    static lit_t zero() {return {0};}

    // Set literal if s==1. Do nothing if s==0. Used for branch-free unit-check loop.
    lit_t setZ(uint32_t s, lit_t l) { return {val | ((int32_t)s)*l.val}; }

    static lit_t from_lit(lit_t l) {return l;}


};


std::string to_string(lit_t l) {return std::to_string(l.val);}

// Unsigned encoding
struct ulit_t {
    typedef uint32_t val_t;

    val_t val = 0;

    ulit_t() {}
    ulit_t &operator =(ulit_t const&) = default;
    ulit_t(ulit_t const&) = default;
    ulit_t(bool pos, uint32_t v) : val(2*v | !pos) {}

    explicit operator bool() {return val!=0;}
    ulit_t operator -() {return {val ^ 0x1}; }

    bool is_pos() {return (val & 0x1) == 0; }

    uint32_t var() {return val/2;}

    static ulit_t zero() {return {0};}

    static ulit_t from_raw_unsigned(uint32_t v) {return {v};}

    static ulit_t from_lit(lit_t l) {return ulit_t(l.is_pos(),l.var());}


    // Set literal, unless l is zero, in which case nothing is done. Used for branch-free unit-check loop.
    ulit_t setZ(uint32_t s, ulit_t l) { return {val | s*l.val}; }

private:
    ulit_t(uint32_t _val) : val(_val) {}



};

std::string to_string(ulit_t l) {
    if (l.is_pos()) return std::to_string(l.var());
    else return "-"+std::to_string(l.var());
}






