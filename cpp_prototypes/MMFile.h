#pragma once

#include <boost/iostreams/device/mapped_file.hpp>

#include <string>

#include "Logging.h"

typedef const char * charit_t;

class cc_it {
    charit_t current;
    charit_t end;

public:

    cc_it(cc_it const&) = delete;
    cc_it &operator=(cc_it const&) = delete;

    cc_it(cc_it &&) = default;
    cc_it &operator=(cc_it&&) = default;


    cc_it(const char * b, const char * e) : current(b), end(e) {
        // if (size==0) DBG("Size for it is 0");
    }

    inline bool is_eof() {return current==end;}


    cc_it &operator ++() {
        if (is_eof()) error("Parsed beyond EOF");
        ++current;
        return *this;
    }

    char operator *() {
        if (is_eof()) error("Parsed beyond EOF");
        return *current;
    }

    inline char next() {
        if (is_eof()) error("Parsed beyond EOF");
        return *(current++);
    }

    inline char next_unchecked() {
        assert(!is_eof());
        return *(current++);
    }

    // True, if there's a zero at the end.
    // This knowledge can keep out EOF-checks of inner loops, if we know this loop will terminate on a zero
    inline bool zero_terminated() {
        return current!=end && end[-1]==0;
    }


};





class MMFile {
    boost::iostreams::mapped_file mf;
    charit_t beginp = nullptr;
    charit_t endp = nullptr;

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

        beginp = mf.const_data();
        endp = mf.const_data() + mf.size();

    }

    ~MMFile() {
        mf.close();
    }

    inline size_t size() {return endp-beginp; }

    inline charit_t begin() { return beginp; }
    inline charit_t end() { return endp; }

    inline cc_it iterator() {
        return cc_it(begin(),end());
    }


};
