#pragma once

#include <vector>
#include <cassert>

#include "Literal.h"
#include "ClauseId.h"

#include "Logging.h"



template<typename LIT> class ClauseDB_malloc {

    std::vector<LIT*> cmap; // Maps clause ids to clauses

    std::vector<LIT> buffer;

    uint32_t maxvar=0;


public:

    ClauseDB_malloc() : cmap(), buffer() {
    }

    ~ClauseDB_malloc() {
        for (auto p : cmap) if (p) delete [] p;
    }


    // Add new clause.
    template<typename I> LIT* add_clause(I &cit) {
        LIT l;
        do {
            l=LIT::from_lit(cit.read_lit());
            buffer.push_back(l);
            maxvar=std::max(maxvar,l.var());
        } while (l);

        return buffer.data();
    }


    size_t get_maxvar() {return maxvar;}

    // Commit last clause
    void commit_clause(cid_t id) {
        assert(buffer.size());

        // Check for valid id
        CHECK(id.is_pos(),"Invalid id");
        CHECK(id.val<=INT32_MAX,"id overflow");  // Note: we overflow already at signed max value

        // If clause if exists: delete it
        if (id.val<cmap.size() && cmap[id.val]) delete_cid(id);

        // Resize if necessary
        if (id.val>=cmap.size()) cmap.resize(id.val+1,nullptr);

        // Copy buffer to own array
        size_t sz = buffer.size();
        LIT *a = new LIT[sz];
        for (size_t i=0; i<sz;++i) a[i]=buffer[i];

        buffer.clear();
        cmap[id.val] = a;

    }

    // Check is clause is valid and committed
    inline bool is_valid_cid(cid_t cid) { return cid.val<cmap.size() && cmap[cid.val]; }

    // Weaker check if cid is safe to delete (ignoring double-deletion)
    inline bool is_cid_deletable(cid_t cid) { return cid.val<cmap.size(); }


    // Get clause. Validity of id not checked
    LIT* get_cit_unchecked(cid_t cid) {
        assert(is_valid_cid(cid));
        return cmap[cid.val];
    }


    // Get clause, check if id is valid
    LIT* get_cit(cid_t cid) {
        if (!is_valid_cid(cid)) error("Invalid cid: " + to_string(cid));
        return get_cit_unchecked(cid);
    }

    // Delete clause (ignores invalid ids)
    void delete_cid(cid_t cid) {
        if (is_cid_deletable(cid) && cmap[cid.val]) {
            delete [] cmap[cid.val];
            cmap[cid.val]=nullptr;
        }
    }


    std::string string_of_cid(cid_t cid) {
        std::string res=to_string(cid)+": ";
        if (is_valid_cid(cid)) {
            res+=string_of_clause(get_cit(cid));
        } else {
            res+="invalid";
        }

        return res;
    }




};
