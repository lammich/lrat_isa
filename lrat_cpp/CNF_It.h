#pragma once

#include "MMFile.h"
#include "Literal.h"


struct dimacs_header {
  size_t num_vars = 0;
  size_t num_clauses = 0;
};


class CNF_It {
    // Parser stuff
    static inline bool is_ws(char c) {return c==' ' || c=='\t' || c=='\n' || c=='\r';}


    static void skip_to_eol(charit_t &it, charit_t end) {
        while (it!=end) {
            char c=*it;
            ++it;
            if (c=='\n') break;
        }
    }

    // Whitespace policy: skipping over whitespace after parsing, such that eof == it.eof
    static void skip_whitespace(charit_t &it, charit_t end) {
        while (it!=end) {
            char c=*it;
            if (is_ws(c)) ++it;
            else if (c=='c') skip_to_eol(it,end);
            else break;
        }

        // while (!it.is_eof() && is_ws(*it)) ++it;
    }

    static void skip_whitespace_no_comments(charit_t &it, charit_t end) {
        while (it!=end && is_ws(*it)) ++it;
    }


    static void parse_exact(std::string w, charit_t &it, charit_t end) {
        for (char c : w) {
            if (it==end) error("Expected " + w + " but found end of file");
            if (*it != c) error("Expected " + w + "("+ c +") but got " + *it);
            ++it;
        }

        skip_whitespace_no_comments(it,end);
    }


    static uint64_t parse_unsigned(charit_t &it, charit_t end) {
        uint64_t res = 0;

        bool seen_one_char=false;

        while (it!=end) {
            char c=*it; ++it;
            seen_one_char=true;
            if (!(c>='0' && c<='9')) break;

            res = 10*res + (c-'0');
        }

        if (!seen_one_char) error("error parsing unsigned");

        skip_whitespace(it,end);

        return res;
    }

    static lit_t parse_lit(charit_t &it, charit_t end) {
        lit_t::val_t sign=1;
        if (*it == '-') {++it; sign=-1;}

        lit_t::val_t res=0;
        bool seen_one_char=false;

        while (it!=end) {
            char c=*it; ++it;
            seen_one_char=true;
            if (!(c>='0' && c<='9')) break;

            res = 10*res + (c-'0');
        }

        if (!seen_one_char) error("error parsing literal");

        skip_whitespace(it,end);

        return { sign*res };
    }



public:

    static inline lit_t read_lit(charit_t &it, charit_t end) {return parse_lit(it,end);}

    static dimacs_header parse_dimacs_header(charit_t &it, charit_t end) {
        dimacs_header h;

        skip_whitespace(it,end);

        parse_exact("p",it,end);
        parse_exact("cnf",it,end);

        skip_whitespace(it,end);

        h.num_vars=parse_unsigned(it,end);
        h.num_clauses=parse_unsigned(it,end);

        return h;
    }



private:
    cc_it it;



    void skip_to_eol() {
        while (!it.is_eof()) {
            char c=*it;
            ++it;
            if (c=='\n') break;
        }
    }

    // Whitespace policy: skipping over whitespace after parsing, such that eof == it.eof
    void skip_whitespace() {
        while (!it.is_eof()) {
            char c=*it;
            if (is_ws(c)) ++it;
            else if (c=='c') skip_to_eol();
            else break;
        }

        // while (!it.is_eof() && is_ws(*it)) ++it;
    }

    void parse_dimacs_header() {
        if (!it.is_eof() && *it == 'p') skip_to_eol();
        skip_whitespace();
    }

    lit_t parse_lit() {
        lit_t::val_t sign=1;
        if (*it == '-') {++it; sign=-1;}

        lit_t::val_t res=0;
        bool seen_one_char=false;

        while (!it.is_eof()) {
            char c=*it; ++it;
            seen_one_char=true;
            if (!(c>='0' && c<='9')) break;

            res = 10*res + (c-'0');
        }

        if (!seen_one_char) error("error parsing literal");

        skip_whitespace();

        return { sign*res };
    }



public:
    CNF_It (cc_it &&_it) :it(std::forward<cc_it>(_it)) {
        skip_whitespace();
        parse_dimacs_header();

        if (is_eof()) VMSG("empty CNF");
    }


    inline bool is_eof() {return it.is_eof();}

    inline lit_t read_lit() {return parse_lit();}



};
