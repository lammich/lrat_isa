#pragma once

#include "MMFile.h"
#include "Literal.h"
#include "ClauseId.h"





class VBEnc_It {

public:
    static uint32_t read_unsigned(charit_t &it, charit_t end) {
        uint32_t res=0;
        uint32_t shift=0;

        while (it<end && shift<8*sizeof(res)) {
            char c = *(it++);
            res |= (c & 0x7F) << shift;
            if ((c&0x80) == 0) break;
            shift += 7;
        }

        if (shift >= 8*sizeof(res)) error("Binary encoding: value overflow");

        return res;
    }

    static int32_t read_signed(charit_t &it, charit_t end) {
        uint32_t ul = read_unsigned(it,end);

        int32_t res;

        if ((ul&0x01) != 0) res=-(static_cast<int32_t>(ul>>1));
        else res=static_cast<int32_t>(ul>>1);

        return res;
    }


    static cid_t read_cid(charit_t &it, charit_t end) {
        return {read_unsigned(it,end)};
    }

    static scid_t read_scid(charit_t &it, charit_t end) {
        return {read_signed(it,end)};
    }

    static lit_t read_lit(charit_t &it, charit_t end) {return {read_signed(it,end)};}

    static ulit_t read_ulit(charit_t &it, charit_t end) {return ulit_t::from_raw_unsigned(read_unsigned(it,end));}



private:
    cc_it it;


public:
    VBEnc_It(cc_it &&_it) : it(std::forward<cc_it>(_it)) {
        CHECK (it.zero_terminated(), "Proof must end with 0");
    }


    inline char read_char_checked() { return it.next(); }
    inline char read_char() { return it.next_unchecked(); }

    uint32_t read_unsigned_checked() {
        uint32_t res=0;
        uint32_t shift=0;


        while (!it.is_eof() && shift<8*sizeof(res)) {
            char c = it.next_unchecked();
            res |= (c & 0x7F) << shift;
            if ((c&0x80) == 0) break;
            shift += 7;
        }

        if (shift >= 8*sizeof(res)) error("Binary encoding: value overflow");

        return res;
    }

    // Skipping the eof-checks, if we know that there must be a 0 before EOF
    uint32_t read_unsigned() {
        uint32_t res=0;
        uint32_t shift=0;


        while (shift<8*sizeof(res)) {
            char c = it.next_unchecked();
            res |= (c & 0x7F) << shift;
            if ((c&0x80) == 0) break;
            shift += 7;
        }

//          No need to check for value overflow. Will just cause mis-read (i.e. failing) certificate
//         if (shift >= 8*sizeof(res)) error("Binary encoding: value overflow");

        return res;
    }


    int32_t read_signed_checked() {
        uint32_t ul = read_unsigned_checked();

        int32_t res;

        if ((ul&0x01) != 0) res=-(static_cast<int32_t>(ul>>1));
        else res=static_cast<int32_t>(ul>>1);

        return res;
    }

    int32_t read_signed() {
        uint32_t ul = read_unsigned();

        int32_t res;

        if ((ul&0x01) != 0) res=-(static_cast<int32_t>(ul>>1));
        else res=static_cast<int32_t>(ul>>1);

        return res;
    }



    cid_t read_cid_checked() {
        return {read_unsigned_checked()};
    }

    scid_t read_scid_checked() {
        return {read_signed_checked()};
    }

    cid_t read_cid() {
        return {read_unsigned()};
    }

    scid_t read_scid() {
        return {read_signed()};
    }


    lit_t read_lit_checked() {return {read_signed_checked()};}
    lit_t read_lit() {return {read_signed()};}

    ulit_t read_ulit() {return ulit_t::from_raw_unsigned(read_unsigned());}
    ulit_t read_ulit_checked() {return ulit_t::from_raw_unsigned(read_unsigned_checked());}



    bool is_eof() {return it.is_eof();}

};
