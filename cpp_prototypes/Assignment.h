#pragma once

#include <vector>
#include <cassert>

#include "Literal.h"



class Assignment {
    bool *data = nullptr;
    bool *mid = nullptr;
    size_t nvar = 0;

    std::vector<lit_t> trail;

    void clear() {
        if (data) delete[] data;
        data=nullptr;
        mid=nullptr;
        nvar=0;
    }

    inline void reset(lit_t l) {
        assert(l.var()<=nvar);
        mid[l.val]=false;
    }


public:
    Assignment() : trail() {}

    Assignment(size_t _nvar) : trail() {
        resize(_nvar);
    };

    Assignment(const Assignment& a) = delete;

    Assignment& operator=(const Assignment&a) = delete;

    ~Assignment() {
        clear();
    }


    void resize_aux(size_t nnvar) {
        assert(nnvar>nvar);

        bool *ndata = new bool[2*nnvar+1]();
        bool *nmid = ndata + nnvar;

        if (mid) {
            // Copy over data
            for (lit_t::val_t l=-nvar;l<=(lit_t::val_t)nvar;++l) nmid[l]=mid[l];

            // Free old
            delete[] data;
        }

        // Set new values
        data=ndata;
        mid=nmid;
        nvar=nnvar;
    }

    inline void resize(size_t _nvar) {
        if (_nvar>nvar) resize_aux(std::max(_nvar, 3*nvar/2));
    }

    inline bool get(lit_t l) {
        assert(l.var()<=nvar);
        return mid[l.val];
    }

    inline void set(lit_t l) {
        assert(l.var()<=nvar);
        trail.push_back(l);
        mid[l.val]=true;
    }

    // Set, extend size if necessary
    inline void set_ext(lit_t l) {
        resize(l.var());
        set(l);
    }



    inline void reset_all() {
        for (auto l : trail) reset(l);
        trail.clear();
    }


};

class Assignment_BV { // Assignment based on bit-vector (vector<bool>)
    std::vector<bool> bv;
    size_t nvar = 0;

    std::vector<lit_t> trail;

    inline void reset(lit_t l) {
        assert(l.var()<=nvar);
        bv[nvar+l.val]=false;
    }


public:
    Assignment_BV() : bv(), trail() {}

    Assignment_BV(size_t _nvar) : bv(), trail() {
        resize(_nvar);
    };

    Assignment_BV(const Assignment_BV& a) = delete;

    Assignment_BV& operator=(const Assignment_BV& a) = delete;



    void resize_aux(size_t nnvar) {
        assert(nnvar>nvar);

        bv.clear();
        bv.resize(nnvar*2+1);
        nvar=nnvar;

        for (auto l : trail) set(l);
    }

    inline void resize(size_t _nvar) {
        if (_nvar>nvar) resize_aux(std::max(_nvar, 3*nvar/2));
    }

    inline bool get(lit_t l) {
        assert(l.var()<=nvar);
        return bv[nvar+l.val];
    }

    inline void set(lit_t l) {
        assert(l.var()<=nvar);
        trail.push_back(l);
        bv[nvar+l.val]=true;
    }

    // Set, extend size if necessary
    inline void set_ext(lit_t l) {
        resize(l.var());
        set(l);
    }


    inline void reset_all() {
        for (auto l : trail) reset(l);
        trail.clear();
    }


};

class Assignment_CharV {
    std::vector<char> bv;
    size_t nvar = 0;

    std::vector<lit_t> trail;

    inline void reset(lit_t l) {
        assert(l.var()<=nvar);
        bv[nvar+l.val]=false;
    }


public:
    Assignment_CharV() : bv(), trail() {}

    Assignment_CharV(size_t _nvar) : bv(), trail() {
        resize(_nvar);
    };

    Assignment_CharV(const Assignment_CharV& a) = delete;

    Assignment_CharV& operator=(const Assignment_CharV& a) = delete;



    void resize_aux(size_t nnvar) {
        assert(nnvar>nvar);

        bv.clear();
        bv.resize(nnvar*2+1);
        nvar=nnvar;

        for (auto l : trail) set(l);
    }

    inline void resize(size_t _nvar) {
        if (_nvar>nvar) resize_aux(std::max(_nvar, 3*nvar/2));
    }

    inline bool get(lit_t l) {
        assert(l.var()<=nvar);
        return bv[nvar+l.val];
    }

    inline void set(lit_t l) {
        assert(l.var()<=nvar);
        trail.push_back(l);
        bv[nvar+l.val]=true;
    }

    // Set, extend size if necessary
    inline void set_ext(lit_t l) {
        resize(l.var());
        set(l);
    }


    inline void reset_all() {
        for (auto l : trail) reset(l);
        trail.clear();
    }


};


// Assignment that uses epoch counter for constant-time clearing
class Assignment2 {

    typedef uint32_t epoch_t;

    epoch_t *data = nullptr;
    epoch_t *mid = nullptr;
    size_t nvar = 0;

    epoch_t epoch = 1;


    void clear() {
        if (data) delete[] data;
        data=nullptr;
        mid=nullptr;
        nvar=0;
        epoch=1;
    }

    inline void reset(lit_t l) {
        assert(l.var()<=nvar);
        mid[l.val]=0;
    }



public:

    Assignment2() {}

    Assignment2(size_t _nvar) {
        resize(_nvar);
    };

    Assignment2(const Assignment2& a) = delete;

    Assignment2& operator=(const Assignment2 &a) = delete;

    ~Assignment2() {
        clear();
    }


    void resize_aux(size_t nnvar) {
        assert(nnvar>nvar);

        epoch_t *ndata = new epoch_t[2*nnvar+1]();
        epoch_t *nmid = ndata + nnvar;

        if (mid) {
            // Copy over data
            for (lit_t::val_t l=-nvar;l<=(lit_t::val_t)nvar;++l) nmid[l]=mid[l];

            // Free old
            delete[] data;
        }

        // Set new values
        data=ndata;
        mid=nmid;
        nvar=nnvar;
    }

    inline void resize(size_t _nvar) {
        if (_nvar>nvar) resize_aux(std::max(_nvar, 3*nvar/2));
    }


    inline bool get(lit_t l) {
        assert(l.var()<=nvar);
        return mid[l.val] >= epoch;
    }

    inline void set(lit_t l) {
        assert(l.var()<=nvar);
        mid[l.val] = epoch;
    }

    // Set, extend size if necessary
    inline void set_ext(lit_t l) {
        resize(l.var());
        set(l);
    }

    inline void reset_all() {
        ++epoch;
    }


};




class Assignment_PosEnc {
    std::vector<char> bv;
    size_t nvar = 0;

    std::vector<lit_t> trail;


    inline char mask(lit_t l) {
        // if (l.val<0) return 0x2; else return 0x1;
        return 0x1 + (l.val<0);
    }

/*    inline size_t idx(lit_t l) {
        assert(l);
        return (2*l.var() - (l.val<0));
    }
*/


    inline void reset(lit_t l) {
        assert(l.var()<=nvar);
        bv[l.var()] &= ~mask(l);
    }


public:
    Assignment_PosEnc() : bv(), trail() {}

    Assignment_PosEnc(size_t _nvar) : bv(), trail() {
        resize(_nvar);
    };

    Assignment_PosEnc(const Assignment_PosEnc& a) = delete;

    Assignment_PosEnc& operator=(const Assignment_PosEnc& a) = delete;



    void resize_aux(size_t nnvar) {
        bv.resize(nnvar+1);
        nvar=nnvar;
    }

    inline void resize(size_t _nvar) {
        if (_nvar>nvar) resize_aux(_nvar);
    }

    inline bool get(lit_t l) {
        assert(l.var()<=nvar);
        return bv[l.var()] & mask(l);
    }

    inline void set(lit_t l) {
        assert(l.var()<=nvar);
        trail.push_back(l);
        bv[l.var()] |= mask(l);
    }

    // Set, extend size if necessary
    inline void set_ext(lit_t l) {
        resize(l.var());
        set(l);
    }


    inline void reset_all() {
        for (auto l : trail) reset(l);
        trail.clear();
    }


};






class Assignment_Ulit {
    std::vector<char> bv;
    size_t bv_size = 0;
    size_t nvar = 0;

    std::vector<ulit_t> trail;

    inline void reset(ulit_t l) {
        assert(l.val<bv_size);
        bv[l.val] = 0;
    }


public:
    Assignment_Ulit() : bv(), trail() {}

    Assignment_Ulit(size_t _nvar) : bv(), trail() {
        resize(_nvar);
    };

    Assignment_Ulit(const Assignment_Ulit& a) = delete;

    Assignment_Ulit& operator=(const Assignment_Ulit& a) = delete;



    void resize_aux(size_t nnvar) {
        nvar=nnvar;
        bv_size=2*nnvar+2;
        bv.resize(bv_size);
    }

    inline void resize(size_t _nvar) {
        if (_nvar>nvar) resize_aux(_nvar);
    }

    inline bool get(ulit_t l) {
        //if (! (l.val<bv_size)) return false;
        assert(l.val<bv_size);
        return bv[l.val];
    }

    inline void set(ulit_t l) {
        // resize(l.var());
        assert(l.val<bv_size);
        trail.push_back(l);
        bv[l.val] = 1;
    }

    // Set, extend size if necessary
    inline void set_ext(ulit_t l) {
        resize(l.var());
        set(l);
    }


    inline void reset_all() {
        for (auto l : trail) reset(l);
        trail.clear();
    }


};




class Assignment_Ulit_LL {
    std::vector<size_t> bv;
    size_t bv_size = 0;
    size_t nvar = 0;

    size_t last_set=1; // Unused, non-zero index


public:
    Assignment_Ulit_LL() : bv() {}

    Assignment_Ulit_LL(size_t _nvar) : bv() {
        resize(_nvar);
    };

    Assignment_Ulit_LL(const Assignment_Ulit_LL& a) = delete;

    Assignment_Ulit_LL& operator=(const Assignment_Ulit_LL& a) = delete;



    void resize_aux(size_t nnvar) {
        nvar=nnvar;
        bv_size=2*nnvar+2;
        bv.resize(bv_size);
    }

    inline void resize(size_t _nvar) {
        if (_nvar>nvar) resize_aux(_nvar);
    }

    inline bool get(ulit_t l) {
        if (! (l.val<bv_size)) return false;
        assert(l.val<bv_size);
        return bv[l.val];
    }

    inline void set(ulit_t l) {
        resize(l.var());
        assert(2<=l.val && l.val<bv_size);

        if (!bv[l.val]) {
            bv[l.val] = last_set;
            last_set = l.val;
        }
    }

    // Set, extend size if necessary
    inline void set_ext(ulit_t l) {
//        resize(l.var());
        set(l);
    }


    inline void reset_all() {
        while (last_set != 1) {
            assert(2<=last_set && last_set<bv_size);
            size_t t = bv[last_set];
            bv[last_set]=0;
            last_set=t;
        }
    }


};


class Assignment_Ulit_CLR {
    std::vector<bool> bv;
    size_t bv_size = 0;
    size_t nvar = 0;

public:
    Assignment_Ulit_CLR() : bv() {}

    Assignment_Ulit_CLR(size_t _nvar) : bv() {
        resize(_nvar);
    };

    Assignment_Ulit_CLR(const Assignment_Ulit_CLR& a) = delete;

    Assignment_Ulit_CLR& operator=(const Assignment_Ulit_CLR& a) = delete;



    void resize_aux(size_t nnvar) {
        nvar=nnvar;
        bv_size=2*nnvar+2;
        bv.resize(bv_size);
    }

    inline void resize(size_t _nvar) {
        if (_nvar>nvar) resize_aux(_nvar);
    }

    inline bool get(ulit_t l) {
        if (! (l.val<bv_size)) return false;
        assert(l.val<bv_size);
        return bv[l.val];
    }

    inline void set(ulit_t l) {
        resize(l.var());
        assert(2<=l.val && l.val<bv_size);

        bv[l.val] = 1;
    }

    // Set, extend size if necessary
    inline void set_ext(ulit_t l) {
//        resize(l.var());
        set(l);
    }


    inline void reset_all() {
        bv.clear();
        bv_size=0;
        nvar=0;
    }


};



