#pragma once

#include <vector>
#include <cassert>

#include "Literal.h"
#include "ClauseId.h"

#include "Logging.h"


template<typename LIT> std::string string_of_clause(LIT *l) {
    std::string res;
    for (;*l;++l) res+=to_string(*l)+" ";
    res+="0";
    return res;
}


template<typename LIT> class ClauseDB {

    std::vector<LIT> db; // Clause database, clauses are zero-terminated. First entry is unused.

    std::vector<size_t> cmap; // Maps clause ids to start offsets in db


    uint32_t maxvar=0;

    size_t committed_end=0; // Offset one beyond last committed clause


public:

    ClauseDB() : db(), cmap() {
        // First entry in db is unused (such that default cmap entries point there)
        db.push_back(LIT::zero());
        committed_end = db.size();
    }

    // True if last clause has been committed
    bool all_committed() {return committed_end == db.size();}

    // Add new clause. The previous clause must have been committed
    template<typename I> LIT* add_clause(I &cit) {
        assert(all_committed());

        size_t res = db.size();
        LIT l;
        do {
            l=LIT::from_lit(cit.read_lit());
            db.push_back(l);
            maxvar=std::max(maxvar,l.var());
        } while (l);

        return db.data()+res;
    }


    size_t get_maxvar() {return maxvar;}

    // Commit last clause
    void commit_clause(cid_t id) {
        assert(!all_committed());

        // Check for valid id
        CHECK(id.is_pos(),"Invalid id");
        CHECK(id.val<=INT32_MAX,"id overflow");  // Note: we overflow already at signed max value

        // We cannot overwrite existing clause IDs
        if (id.val<cmap.size() && cmap[id.val]!=0) error("Overwriting existing clause id: " + to_string(id));

        // Resize if necessary
        if (id.val>=cmap.size()) cmap.resize(id.val+1,0);

        // Create cmap entry
        cmap[id.val] = committed_end;

        // New committed end
        committed_end=db.size();

    }

    // Check is clause is valid and committed
    inline bool is_valid_cid(cid_t cid) { return cid.val<cmap.size() && cmap[cid.val]!=0; }

    // Weaker check if cid is safe to delete (ignoring double-deletion)
    inline bool is_cid_deletable(cid_t cid) { return cid.val<cmap.size(); }


    // Get clause. Validity of id not checked
    LIT* get_cit_unchecked(cid_t cid) {
        assert(is_valid_cid(cid));
        return db.data() + cmap[cid.val];
    }


    // Get clause, check if id is valid
    LIT* get_cit(cid_t cid) {
        if (!is_valid_cid(cid)) error("Invalid cid: " + to_string(cid));
        return get_cit_unchecked(cid);
    }

    // Delete clause (ignores invalid ids)
    void delete_cid(cid_t cid) {
        if (is_cid_deletable(cid)) cmap[cid.val]=0;
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
