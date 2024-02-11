#define NDEBUG

// #define PROFILING
#undef PROFILING


#include <boost/iostreams/device/mapped_file.hpp>
#include <boost/stacktrace.hpp>
#include <iostream>
#include <fstream>
#include <vector>
#include <cassert>
#include <cstdlib>

#include <chrono>

extern "C" {
    #include <sys/mman.h>
}

#include "Literal.h"
#include "ClauseId.h"
#include "Logging.h"
#include "ClauseDB.h"
#include "ClauseDB_malloc.h"

#include "Assignment.h"

#include "MMFile.h"

#include "CNF_It.h"

#include "VBEnc_It.h"

#ifdef PROFILING
#include <gperftools/profiler.h>
#endif

using namespace std;

/*typedef int32_t lit_t;
typedef size_t cid_t;
*/



uint64_t timeMillis() {
  using namespace std::chrono;
  return duration_cast<milliseconds>(system_clock::now().time_since_epoch()).count();
}




/*
    Clause iterator:
      provides method next
      Iterator has reached end if next returns 0

*/

















class Lrat_Checker {
    ClauseDB<lit_t> db;
    Assignment_PosEnc ass;

    bool found_conflict = false; // Indicates that we have found conflict, when in proof

    bool contains_empty_clause = false; // Indicates that the empty clause has been added. If not in proof, that means the formula is unsat


    void rup_step2(cid_t cid) {
        if (found_conflict) return;  // Nothing to check if conflict clause already found

        lit_t *li = db.get_cit(cid);

        lit_t ulit = lit_t::zero();

        for (;*li;++li) {
            lit_t l = *li;

            if (!ass.get(-l)) {
                if (ulit) {
                    diagnose_non_unit(cid);
                    error("Clause is not unit " + to_string(cid));
                }

                ulit=l;
            }
        }


        if (ulit) {
            ass.set({ulit});
        } else {
            found_conflict=true;
        }

    }


    void rup_step3(cid_t cid) {
        if (found_conflict) return;  // Nothing to check if conflict clause already found

        bool err=false;

        lit_t *li = db.get_cit(cid);

        lit_t ulit = lit_t::zero();

        for (;*li && !err;++li) {
            lit_t l = *li;

            if (!ass.get(-l)) {
                if (ulit) err=true;

                ulit=l;
            }
        }

        if (err) {
            diagnose_non_unit(cid);
            error("Clause is not unit " + to_string(cid));
        }

        if (ulit) {
            ass.set({ulit});
        } else {
            found_conflict=true;
        }

    }



    void rup_step(cid_t cid) {

        if (found_conflict) return;  // Nothing to check if conflict clause already found

        DBG("RUP step " + db.string_of_cid(cid));

        lit_t *li = db.get_cit(cid);

        lit_t::val_t ulit = 0;
        size_t count = 0;


        for (;*li;++li) {
            lit_t l = *li;
            lit_t::val_t nbl = 1 - ass.get(-l); // 0 if *li is false, 1 otherwise

            // assert(nbl==0 || nbl==1);
            count+=nbl;

            ulit |= nbl*l.val;
        }

        if (count==0) {
            DBG("RUP yielded conflict clause");
            found_conflict=true;
        } else if (count==1) {
            // Set the found unit literal. Note: it does not matter if it is already set
            assert(ulit);

            DBG("RUP yielded unit " + to_string(ulit));

            ass.set({ulit});
        } else {
            diagnose_non_unit(cid);
            error("Clause is not unit " + to_string(cid) + " (" + to_string(count) + ")");
        }

    }


    void diagnose_non_unit(cid_t cid) {

        VMSG("Diagnosing status of clause " + db.string_of_cid(cid));

        lit_t *li = db.get_cit(cid);

        for (;*li;++li) {
            lit_t l=*li;

            if (ass.get(l) && ass.get(-l)) VMSG("CONFL " + to_string(l));
            else if (ass.get(l)) VMSG("TRUE  " + to_string(l));
            else if (!ass.get(-l)) VMSG("UNDEC " + to_string(l));
        }

    }



public:

    // True if proof is open
    bool in_proof() {
        return !db.all_committed();
    }

    bool unsat_proved() {
        return !in_proof() && contains_empty_clause;
    }


    void commit_proof(cid_t cid) {
        assert(in_proof());
        if (!found_conflict) error("Proof not finished");

        // Restore assignment
        //ass.restore();
        ass.reset_all();

        // Commit clause
        db.commit_clause(cid);

        // Reset found-conflict flag
        found_conflict=false;

        assert(!in_proof());

        DBG("Committed as id " + to_string(cid));


    }


    Lrat_Checker() : db(), ass() {

    }

    template<typename I> void add_clause(cid_t cid, I &cit) {
        assert(!in_proof());

        lit_t *ci = db.add_clause(cit);

        contains_empty_clause = contains_empty_clause || (!*ci);

        db.commit_clause(cid);

        DBG("clause " + db.string_of_cid(cid));

    }


    template<typename I> void add_lemma(I &cit) {
        assert(!in_proof());

        lit_t *ci = db.add_clause(cit);
        ass.resize(db.get_maxvar());

        DBG("Proving lemma " + string_of_clause(ci));

        // Check if we add the empty clause
        contains_empty_clause = contains_empty_clause || (!*ci);

        // Mark position in assignment, assign negative literals of clause
        //ass.mark();
        for (auto i=ci;*i;++i) ass.set(-*i);

        found_conflict=false;
        assert(in_proof());
    }

    void del_clause(cid_t cid) {
        db.delete_cid(cid);
    }


    template<typename I> void rup_steps(I &iit) {
        assert(in_proof());

        while (true) {
            scid_t id = iit.read_scid();

            if (id.is_negative()) error("RAT clauses not supported");
            if (!id) break;

            rup_step3(id.cid());
        }

    }


    size_t get_maxvar() {return db.get_maxvar();}



    /*

    xxx, ctd here: just did mark/restore in assignment


    xxx, ctd here: shall we decouple checking logic from parser completely, i.e., phrase this class as state-,achine that gets checking instructions?

    Interface would be:

      // Add a lemma. not yet proved
      add_lemma(lit_iterator)

      // Perform unit propagations.
      // If conflict clause is found, proof can be committed
      // Iterator is always read until end
      proof_uprop(id_iterator)

      // proof_init_rat(lit) // set literal for rat proof
      // proof_rat(id, id_iterator) // add rat candidate proof

      // Commit current proof (it must be finished), and await next lemma
      commit_proof()






    void add_cnf() {



    }

    */



};



class Lrat_Ctrl {
    CNF_It cnf;
    VBEnc_It prf;

    Lrat_Checker chk;

public:
    Lrat_Ctrl(cc_it &&_cnf_it, cc_it &&_prf_it) : cnf(std::forward<cc_it>(_cnf_it)), prf(std::forward<cc_it>(_prf_it)), chk() {


    }


    void check() {
        // Load initial formula
        MSG("Loading clauses from initial formula");
        cid_t::val_t id=1;
        while (!cnf.is_eof()) {
            chk.add_clause({id},cnf);
            ++id;
        }

        VMSG("Maxvar after clauses: " + to_string(chk.get_maxvar()));

        MSG("Iterating over proof clauses");

        // Iterate through proof
        while (!prf.is_eof()) {

            char type = prf.read_char();

            if (type=='a') {
                cid_t id = prf.read_cid();
                chk.add_lemma(prf);

                chk.rup_steps(prf);

                chk.commit_proof(id);
            } else if (type=='d') {
                while (true) {
                    scid_t id=prf.read_scid();
                    if (!id) break;
                    if (id.is_negative()) error("Negative id in deletion: " + to_string(id));

                    chk.del_clause(id.cid());
                }
            } else {
                error("Unknown item type " + to_string(type));
            }
        }

        MSG("Checking if empty clause was proved");

        if (!chk.unsat_proved()) error("No empty clause added");

    }


};


class Lrat_CheckerU {
    ClauseDB<ulit_t> db;
    Assignment_Ulit ass;

    bool found_conflict = false; // Indicates that we have found conflict, when in proof

    bool contains_empty_clause = false; // Indicates that the empty clause has been added. If not in proof, that means the formula is unsat


    void rup_step2(cid_t cid) {
        if (found_conflict) return;  // Nothing to check if conflict clause already found

        ulit_t *li = db.get_cit(cid);

        ulit_t ulit = ulit_t::zero();

        for (;*li;++li) {
            ulit_t l = *li;

            if (!ass.get(-l)) {
                if (ulit) {
                    diagnose_non_unit(cid);
                    error("Clause is not unit " + to_string(cid));
                }

                ulit=l;
            }
        }


        if (ulit) {
            ass.set({ulit});
        } else {
            found_conflict=true;
        }

    }


    void rup_step3(cid_t cid) {
        if (found_conflict) return;  // Nothing to check if conflict clause already found

        bool err=false;

        ulit_t *li = db.get_cit(cid);

        ulit_t ulit = ulit_t::zero();

        for (;*li && !err;++li) {
            ulit_t l = *li;

            if (!ass.get(-l)) {
                if (ulit) err=true;

                ulit=l;
            }
        }

        if (err) {
            diagnose_non_unit(cid);
            error("Clause is not unit " + to_string(cid));
        }

        if (ulit) {
            ass.set({ulit});
        } else {
            found_conflict=true;
        }

    }



    void rup_step(cid_t cid) {

        if (found_conflict) return;  // Nothing to check if conflict clause already found

        DBG("RUP step " + db.string_of_cid(cid));

        ulit_t *li = db.get_cit(cid);

        ulit_t ulit = ulit_t::zero();
        size_t count = 0;


        for (;*li;++li) {
            ulit_t l = *li;
            uint32_t nbl = 1 - ass.get(-l); // 0 if *li is false, 1 otherwise

            // assert(nbl==0 || nbl==1);
            count+=nbl;

            ulit = ulit.setZ(nbl,l);
        }

        if (count==0) {
            DBG("RUP yielded conflict clause");
            found_conflict=true;
        } else if (count==1) {
            // Set the found unit literal. Note: it does not matter if it is already set
            assert(ulit);

            DBG("RUP yielded unit " + to_string(ulit));

            ass.set({ulit});
        } else {
            diagnose_non_unit(cid);
            error("Clause is not unit " + to_string(cid) + " (" + to_string(count) + ")");
        }

    }


    void diagnose_non_unit(cid_t cid) {

        VMSG("Diagnosing status of clause " + db.string_of_cid(cid));

        ulit_t *li = db.get_cit(cid);

        for (;*li;++li) {
            ulit_t l=*li;

            if (ass.get(l) && ass.get(-l)) VMSG("CONFL " + to_string(l));
            else if (ass.get(l)) VMSG("TRUE  " + to_string(l));
            else if (!ass.get(-l)) VMSG("UNDEC " + to_string(l));
        }

    }



public:

    // True if proof is open
    bool in_proof() {
        return !db.all_committed();
    }

    bool unsat_proved() {
        return !in_proof() && contains_empty_clause;
    }


    void commit_proof(cid_t cid) {
        assert(in_proof());
        if (!found_conflict) error("Proof not finished");

        // Restore assignment
        //ass.restore();
        ass.reset_all();

        // Commit clause
        db.commit_clause(cid);

        // Reset found-conflict flag
        found_conflict=false;

        assert(!in_proof());

        DBG("Committed as id " + to_string(cid));


    }


    Lrat_CheckerU() : db(), ass() {

    }

    template<typename I> void add_clause(cid_t cid, I &cit) {
        assert(!in_proof());

        ulit_t *ci = db.add_clause(cit);

        contains_empty_clause = contains_empty_clause || (!*ci);

        db.commit_clause(cid);

        DBG("clause " + db.string_of_cid(cid));

    }


    template<typename I> void add_lemma(I &cit) {
        assert(!in_proof());

        ulit_t *ci = db.add_clause(cit);
        ass.resize(db.get_maxvar());

        DBG("Proving lemma " + string_of_clause(ci));

        // Check if we add the empty clause
        contains_empty_clause = contains_empty_clause || (!*ci);

        // Mark position in assignment, assign negative literals of clause
        //ass.mark();
        for (auto i=ci;*i;++i) ass.set(-*i);

        found_conflict=false;
        assert(in_proof());
    }

    void del_clause(cid_t cid) {
        db.delete_cid(cid);
    }


    template<typename I> void rup_steps(I &iit) {
        assert(in_proof());

        while (true) {
            scid_t id = iit.read_scid();

            if (id.is_negative()) error("RAT clauses not supported");
            if (!id) break;

            rup_step3(id.cid());
        }

    }


    size_t get_maxvar() {return db.get_maxvar();}



    /*

    xxx, ctd here: just did mark/restore in assignment


    xxx, ctd here: shall we decouple checking logic from parser completely, i.e., phrase this class as state-,achine that gets checking instructions?

    Interface would be:

      // Add a lemma. not yet proved
      add_lemma(lit_iterator)

      // Perform unit propagations.
      // If conflict clause is found, proof can be committed
      // Iterator is always read until end
      proof_uprop(id_iterator)

      // proof_init_rat(lit) // set literal for rat proof
      // proof_rat(id, id_iterator) // add rat candidate proof

      // Commit current proof (it must be finished), and await next lemma
      commit_proof()






    void add_cnf() {



    }

    */



};


class Lrat_CtrlU {
    CNF_It cnf;
    VBEnc_It prf;

    Lrat_CheckerU chk;

public:
    Lrat_CtrlU(cc_it &&_cnf_it, cc_it &&_prf_it) : cnf(std::forward<cc_it>(_cnf_it)), prf(std::forward<cc_it>(_prf_it)), chk() {


    }


    void check() {
        // Load initial formula
        auto t1 = timeMillis();
        MSG("Loading clauses from initial formula");
        cid_t::val_t id=1;
        while (!cnf.is_eof()) {
            chk.add_clause({id},cnf);
            ++id;
        }

        auto loadTime = timeMillis()-t1;

        MSG("Loading clauses: " + to_string(loadTime) + "ms");

        VMSG("Maxvar after clauses: " + to_string(chk.get_maxvar()));

        MSG("Iterating over proof clauses");

        // Iterate through proof
        while (!prf.is_eof()) {

            char type = prf.read_char();

            if (type=='a') {
                cid_t id = prf.read_cid();
                chk.add_lemma(prf);

                chk.rup_steps(prf);

                chk.commit_proof(id);
            } else if (type=='d') {
                while (true) {
                    scid_t id=prf.read_scid();
                    if (!id) break;
                    if (id.is_negative()) error("Negative id in deletion: " + to_string(id));

                    chk.del_clause(id.cid());
                }
            } else {
                error("Unknown item type " + to_string(type));
            }
        }

        MSG("Checking if empty clause was proved");

        if (!chk.unsat_proved()) error("No empty clause added");

    }


};













class Lrat_CheckerM {
    ClauseDB_malloc<ulit_t> db;
    Assignment_Ulit ass;

    bool found_conflict = false; // Indicates that we have found conflict, when in proof

    bool contains_empty_clause = false; // Indicates that the empty clause has been added. If not in proof, that means the formula is unsat

    bool is_in_proof = false;

    void rup_step2(cid_t cid) {
        if (found_conflict) return;  // Nothing to check if conflict clause already found

        ulit_t *li = db.get_cit(cid);

        ulit_t ulit = ulit_t::zero();

        for (;*li;++li) {
            ulit_t l = *li;

            if (!ass.get(-l)) {
                if (ulit) {
                    diagnose_non_unit(cid);
                    error("Clause is not unit " + to_string(cid));
                }

                ulit=l;
            }
        }


        if (ulit) {
            ass.set({ulit});
        } else {
            found_conflict=true;
        }

    }


    void rup_step3(cid_t cid) {
        if (found_conflict) return;  // Nothing to check if conflict clause already found

        bool err=false;

        ulit_t *li = db.get_cit(cid);

        ulit_t ulit = ulit_t::zero();

        for (;*li && !err;++li) {
            ulit_t l = *li;

            if (!ass.get(-l)) {
                if (ulit) err=true;

                ulit=l;
            }
        }

        if (err) {
            diagnose_non_unit(cid);
            error("Clause is not unit " + to_string(cid));
        }

        if (ulit) {
            ass.set({ulit});
        } else {
            found_conflict=true;
        }

    }



    void rup_step(cid_t cid) {

        if (found_conflict) return;  // Nothing to check if conflict clause already found

        DBG("RUP step " + db.string_of_cid(cid));

        ulit_t *li = db.get_cit(cid);

        ulit_t ulit = ulit_t::zero();
        size_t count = 0;


        for (;*li;++li) {
            ulit_t l = *li;
            uint32_t nbl = 1 - ass.get(-l); // 0 if *li is false, 1 otherwise

            // assert(nbl==0 || nbl==1);
            count+=nbl;

            ulit = ulit.setZ(nbl,l);
        }

        if (count==0) {
            DBG("RUP yielded conflict clause");
            found_conflict=true;
        } else if (count==1) {
            // Set the found unit literal. Note: it does not matter if it is already set
            assert(ulit);

            DBG("RUP yielded unit " + to_string(ulit));

            ass.set({ulit});
        } else {
            diagnose_non_unit(cid);
            error("Clause is not unit " + to_string(cid) + " (" + to_string(count) + ")");
        }

    }


    void diagnose_non_unit(cid_t cid) {

        VMSG("Diagnosing status of clause " + db.string_of_cid(cid));

        ulit_t *li = db.get_cit(cid);

        for (;*li;++li) {
            ulit_t l=*li;

            if (ass.get(l) && ass.get(-l)) VMSG("CONFL " + to_string(l));
            else if (ass.get(l)) VMSG("TRUE  " + to_string(l));
            else if (!ass.get(-l)) VMSG("UNDEC " + to_string(l));
        }

    }



public:

    // True if proof is open
    bool in_proof() {
        return is_in_proof;
    }

    bool unsat_proved() {
        return !in_proof() && contains_empty_clause;
    }


    void commit_proof(cid_t cid) {
        assert(in_proof());
        if (!found_conflict) error("Proof not finished");

        is_in_proof=false;

        // Restore assignment
        //ass.restore();
        ass.reset_all();

        // Commit clause
        db.commit_clause(cid);

        // Reset found-conflict flag
        found_conflict=false;

        assert(!in_proof());

        DBG("Committed as id " + to_string(cid));


    }


    Lrat_CheckerM() : db(), ass() {

    }

    template<typename I> void add_clause(cid_t cid, I &cit) {
        assert(!in_proof());

        ulit_t *ci = db.add_clause(cit);

        contains_empty_clause = contains_empty_clause || (!*ci);

        db.commit_clause(cid);

        DBG("clause " + db.string_of_cid(cid));

    }


    template<typename I> void add_lemma(I &cit) {
        assert(!in_proof());
        is_in_proof=true;

        ulit_t *ci = db.add_clause(cit);
        ass.resize(db.get_maxvar());

        DBG("Proving lemma " + string_of_clause(ci));

        // Check if we add the empty clause
        contains_empty_clause = contains_empty_clause || (!*ci);

        // Mark position in assignment, assign negative literals of clause
        //ass.mark();
        for (auto i=ci;*i;++i) ass.set(-*i);

        found_conflict=false;
        assert(in_proof());
    }

    void del_clause(cid_t cid) {
        db.delete_cid(cid);
    }


    template<typename I> void rup_steps(I &iit) {
        assert(in_proof());

        while (true) {
            scid_t id = iit.read_scid();

            if (id.is_negative()) error("RAT clauses not supported");
            if (!id) break;

            rup_step3(id.cid());
        }

    }


    size_t get_maxvar() {return db.get_maxvar();}




};


class Lrat_CtrlM {
    CNF_It cnf;
    VBEnc_It prf;

    Lrat_CheckerM chk;

public:
    Lrat_CtrlM(cc_it &&_cnf_it, cc_it &&_prf_it) : cnf(std::forward<cc_it>(_cnf_it)), prf(std::forward<cc_it>(_prf_it)), chk() {


    }


    void check() {
        // Load initial formula
        auto t1 = timeMillis();
        MSG("Loading clauses from initial formula");
        cid_t::val_t id=1;
        while (!cnf.is_eof()) {
            chk.add_clause({id},cnf);
            ++id;
        }

        auto loadTime = timeMillis()-t1;

        MSG("Loading clauses: " + to_string(loadTime) + "ms");

        VMSG("Maxvar after clauses: " + to_string(chk.get_maxvar()));

        MSG("Iterating over proof clauses");

        // Iterate through proof
        while (!prf.is_eof()) {

            char type = prf.read_char();

            if (type=='a') {
                cid_t id = prf.read_cid();
                chk.add_lemma(prf);

                chk.rup_steps(prf);

                chk.commit_proof(id);
            } else if (type=='d') {
                while (true) {
                    scid_t id=prf.read_scid();
                    if (!id) break;
                    if (id.is_negative()) error("Negative id in deletion: " + to_string(id));

                    chk.del_clause(id.cid());
                }
            } else {
                error("Unknown item type " + to_string(type));
            }
        }

        MSG("Checking if empty clause was proved");

        if (!chk.unsat_proved()) error("No empty clause added");

    }


};

























/*
xxx, ctd here:
  use set_ext upon verification of clauses.
  Assume that clauses in clause db are within maxvar.
  => put maxvar variable into ClauseDB, updated when adding clause


*/

// Testing stuff

void read_dump_cnf(string file) {
    MMFile cnf_mm(file);

    CNF_It cnf(cnf_mm.iterator());


    while (!cnf.is_eof()) {
        lit_t l = cnf.read_lit();
        cout<<to_string(l);
        if (!l) cout<<endl; else cout<<" ";
    }


}


void dump_deletions(scid_t id, vector<scid_t> const &dels, ostream &out) {
    out<<to_string(id)<<" d";
    for (auto i : dels) out<<" "<<to_string(i);
    out<<" 0"<<endl;
}

/*
    Convert binary lrat to ascii.

    There's one complication:
        the ascii lrat format requires ascending identifiers for each line, where a deletion can re-use the identifier of the previous addition line.
        however, a deletion on the first line is expected to use the identifier of the last clause of the formula, and we do not know the formula at this point.

        We solve this pragmatically (similar to lrat-trim), and use the identifier of the first clause added in the proof minus 1.
        For this, we buffer the first clause deletions, until this identifier is known.

 */
void read_dump_lrat(string infile, ostream &out) {
    MMFile prf_mm(infile);

    VBEnc_It prf(prf_mm.iterator());

    vector<scid_t> buffered_deletions; // Buffer deleted clauses until next addition step.
    scid_t last_id = {0};   // Identifier of last clause added. Used to identify successive deletion lines


    while (!prf.is_eof()) {
        char c = prf.read_char();

        if (c=='a') {
            scid_t id = prf.read_scid();

            // Write out buffered deletions
            if (buffered_deletions.size()) {
                // If no last-id yet, obtain one from this id
                if (!last_id) {
                    if (id.val <= 1) error("Added clause cannot have id 1");
                    last_id = {id.val - 1};
                }

                dump_deletions(last_id,buffered_deletions,out);

                buffered_deletions.clear();
            }

            last_id=id;


            out<<to_string(id);

            while (true) {
                lit_t l=prf.read_lit();
                out<<" "<<to_string(l);
                if (!l) break;
            }

            while (true) {
                scid_t i=prf.read_scid();
                out<<" "<<to_string(i);
                if (!i) break;
            }

            out<<endl;

        } else if (c=='d') {
            // Buffer deletions until next addition is read

            while (true) {
                scid_t i=prf.read_scid();
                if (!i) break;
                buffered_deletions.push_back(i);
            }
        } else {
            error("Unknown item " + to_string(c));
        }

    }

    // Should the file end with clause deletions, we write them out now, provided we have a last id
    if (buffered_deletions.size()) {
        if (!last_id) error("Binary lrat file contains only deletions. We cannot obtain identifier for them.");

        dump_deletions(last_id,buffered_deletions,out);
    }

}


uint64_t test_csum(char *it,char *end) {
    uint64_t csum = 0;

    for (;it!=end;++it) {
        csum+=*it;
    }

    return csum;
}


namespace test_parser {


    inline bool is_ws(char c) {return c==' ' || c=='\t' || c=='\n' || c=='\r';}


    void skip_to_eol(charit_t &it, charit_t end) {
        while (it!=end) {
            char c=*it;
            ++it;
            if (c=='\n') break;
        }
    }

    // Whitespace policy: skipping over whitespace after parsing, such that eof == it.eof
    void skip_whitespace(charit_t &it, charit_t end) {
        while (it!=end) {
            char c=*it;
            if (is_ws(c)) ++it;
            else if (c=='c') skip_to_eol(it,end);
            else break;
        }

        // while (!it.is_eof() && is_ws(*it)) ++it;
    }

    inline void skip_whitespace_no_comments(charit_t &it, charit_t end) {
        while (it!=end && is_ws(*it)) ++it;
    }

    void parse_exact(std::string w, charit_t &it, charit_t end) {
        for (char c : w) {
            if (it==end) error("Expected " + w + " but found end of file");
            if (*it != c) error("Expected " + w + "("+ c +") but got " + *it);
            ++it;
        }

        skip_whitespace_no_comments(it,end);
    }


    uint64_t parse_unsigned(charit_t &it, charit_t end) {
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

    inline int32_t parse_lit(charit_t &it, charit_t end) {
        assert(it!=end);

        int32_t sign=1;
        if (*it == '-') {++it; sign=-1;}

        uint64_t res=0;

        CHECK(it!=end,"EOF while parsing literal");

        char first_digit = *it;
        ++it;

        if (first_digit==0) {
            CHECK(it==end || is_ws(*it), "No leading zeroes allowed");
            skip_whitespace_no_comments(it,end);
            return 0;
        } else {
            CHECK(first_digit>='0' && first_digit<='9',"error parsing literal");
            res=first_digit-'0';

            size_t digits=1;

            while (it!=end) {
                char c=*it; ++it;
                ++digits;
                if (!(c>='0' && c<='9')) break;

                res = 10*res + (c-'0');
            }

            CHECK(res <= INT32_MAX && digits<=10,"Literal integer overflow");

            skip_whitespace_no_comments(it,end);

            return (sign*(int32_t)res);
        }

    }

    inline bool is_digit(char c) {return '0' <= c && c <= '9';}

    inline int32_t parse_lit2(bool &err, charit_t &it, charit_t end) {
        assert(it!=end);

        err=false;

        int32_t sign=1;
        if (*it == '-') {++it; sign=-1;}

        size_t res=0;

        if (it==end) {
            err=true;
        } else if (*it == '0') {
            // Parse a single zero
            ++it;
            if (it!=end && is_digit(*it)) err=true;
            skip_whitespace_no_comments(it,end);
        } else if (is_digit(*it)) {

            // Parse a number that does not start with leading zero.

            charit_t end2 = min(end,it+10);
            do {
                res = 10*res + (size_t)(*it-'0');
                ++it;
            } while (it!=end2 && is_digit(*it));

            skip_whitespace_no_comments(it,end);

//             // Parse a number that does not start with leading zero.
//             while (it!=end && is_digit(*it) && res<=INT_MAX) {
//                 res = 10*res + (size_t)(*it-'0');
//                 ++it;
//             }

            err |= res>INT32_MAX;
        } else err=true;


        return err?0:(sign * (int32_t)res);


    }


    inline int32_t parse_lit_unroll(charit_t &it, charit_t end) {
        assert(it!=end);

        int32_t sign=1;
        if (*it == '-') {++it; sign=-1;}

        uint64_t res=0;

        CHECK(it!=end,"EOF while parsing literal");

        char first_digit = *it;
        ++it;

        if (first_digit==0) {
            CHECK(it==end || is_ws(*it), "No leading zeroes allowed");
            skip_whitespace_no_comments(it,end);
            return 0;
        } else {
            CHECK(first_digit>='0' && first_digit<='9',"error parsing literal");
            res=first_digit-'0';

            size_t cnt=0;
            for (charit_t it2=it; it2!=end && *it2>='0' && *it2<='9'; ++it2) ++cnt;

            CHECK(cnt<10,"Literal integer overflow");

            for (size_t i=0;i<cnt;++i) {
                char c=it[i];
                res = 10*res + (c-'0');
            }

            CHECK(res <= INT32_MAX,"Literal integer overflow");

            it+=cnt;

            skip_whitespace_no_comments(it,end);

            return (sign*(int32_t)res);
        }

    }



    dimacs_header parse_dimacs_header(charit_t &it, charit_t end) {
        dimacs_header h;

        skip_whitespace(it,end);

        parse_exact("p",it,end);
        parse_exact("cnf",it,end);

        skip_whitespace(it,end);

        h.num_vars=parse_unsigned(it,end);
        h.num_clauses=parse_unsigned(it,end);

        return h;
    }





    uint64_t test_cnf_csum(charit_t it, charit_t end) {

        parse_dimacs_header(it,end);

        uint64_t csum = 0;

        bool err=false;
        while (it!=end && !err) {
            auto l = parse_lit2(err,it,end);
            csum += abs(l);
        }

        return csum;
    }


    char *test_cnf_cpy(MMFile &mm) {
        char* cpy = new char[mm.size()];
        memcpy(cpy,mm.begin(),mm.size());

        return cpy;
    }



}

uint64_t test_cnf_csum_old(MMFile &mm) {
    CNF_It cnf(mm.iterator());

    uint64_t csum = 0;

    while (!cnf.is_eof()) {

        lit_t l = cnf.read_lit();
        csum += abs(l.val);
    }

    return csum;
}


template<typename R,typename T> R timeit(string name, T op, size_t size=0) {
    MSG("Starting " + name);
    auto t = timeMillis();
    R res = op();
    t = timeMillis()-t;
    MSG("Done " + name + ": " + to_string(t) +" ms");

    if (size && t) {
        auto tp = size*1000/t/1024/1024;
        MSG("Throughput " + to_string(tp)+" MiB/s");
    }

    return res;
}


void test_parse_cnf(string name) {
    MSG("Mapping cnf file");
    MMFile cnf_mm(name);

    char *begin = timeit<char *>("Copy",[&] {return test_parser::test_cnf_cpy(cnf_mm);},cnf_mm.size());
    char *end = begin+cnf_mm.size();


    MSG("Parse1");

    auto t1 = timeMillis();
    auto cs1 = test_csum(begin,end);
    t1 = timeMillis()-t1;


    MSG("Parse2");

//     #ifdef PROFILING
//     ProfilerStart("prof.out");
//     #endif

    auto t2 = timeMillis();
    auto cs2 = test_parser::test_cnf_csum(begin,end);
    t2 = timeMillis()-t2;

//     #ifdef PROFILING
//     ProfilerStop();
//     #endif

    MSG("Parse3");
    auto t3 = timeMillis();
    auto cs3 = test_cnf_csum_old(cnf_mm);
    t3 = timeMillis()-t3;



    cout<<"CSum: " << cs1 << " " << cs2 << " " << cs3 << endl;
    cout<<"Time: " << t1 << " " << t2 << " " << t3 << " ms"<<endl;

    cout<<"Throughput: "
        << cnf_mm.size()*1000/t1/1024/1024
        << " "
        << cnf_mm.size()*1000/t2/1024/1024
        << " "
        << cnf_mm.size()*1000/t3/1024/1024
        << " MiB/s" << endl;
}


namespace test_benc {

    uint64_t read_unsigned_checked(charit_t &it, charit_t end) {
        uint64_t res=0;
        uint64_t shift=0;

        while (it!=end && shift < 8*sizeof(uint64_t)) {
            char c = *it;
            ++it;

            res |= (c & 0x7F) << shift;
            if ((c&0x80) == 0) break;
            shift += 7;
        }

        return res;
    }

    uint64_t read_unsigned_rev(charit_t &it, charit_t end) {
        uint64_t res=0;

        while (it!=end) {
            char c = *it;
            ++it;

            res = (res<<7) | (c & 0x7F);
            if ((c&0x80) == 0) break;
        }

        return res;
    }


    uint64_t read_unsigned_unchecked(charit_t &it, charit_t end [[maybe_unused]]) {
        uint64_t res=0;
        uint64_t shift=0;

        while (true) {
            char c = *it;
            ++it;

            res |= (c & 0x7F) << shift;
            if ((c&0x80) == 0) break;
            shift += 7;
        }

        return res;
    }



    // Forward, to change reader quickly
    // inline uint64_t read_unsigned_dflt(charit_t &it, charit_t end) {return read_unsigned_checked(it,end);}

    template <typename T> uint64_t test_read_lrat(T rd, charit_t it, charit_t end) {

        uint64_t csum=0;

        while (it!=end) {
            char c = *(it++);

            csum+=c;

            if (c=='a') {
                if (it==end) break;
                // Read Id
                csum+=rd(it,end);

                // Read Literals
                while (it!=end) {
                    uint64_t l=rd(it,end);
                    csum+=l;
                    if (!l) break;
                }

                // Read Proof
                while (it!=end) {
                    uint64_t l=rd(it,end);
                    csum+=l;
                    if (!l) break;
                }
            } else if (c=='d') {

                // Read Ids
                while (it!=end) {
                    uint64_t l=rd(it,end);
                    csum+=l;
                    if (!l) break;
                }
            } else {
                error("Unknown item " + to_string(c));
            }


        }

        return csum;

    }






}


void test_parse_lrat(string name) {
    MSG("Mapping file");
    MMFile mm(name);

    charit_t it = mm.begin();
    charit_t end = mm.end();

    uint64_t csum=0;

    csum = timeit<uint64_t>("Parse b-enc (rev)", [&]{return test_benc::test_read_lrat(test_benc::read_unsigned_rev,it,end);}, mm.size());
    MSG("Csum =" + to_string(csum));

    csum = timeit<uint64_t>("Parse b-enc (rev)", [&]{return test_benc::test_read_lrat(test_benc::read_unsigned_rev,it,end);}, mm.size());
    MSG("Csum =" + to_string(csum));

    csum = timeit<uint64_t>("Parse b-enc (checked)", [&]{return test_benc::test_read_lrat(test_benc::read_unsigned_checked,it,end);}, mm.size());
    MSG("Csum =" + to_string(csum));

    csum = timeit<uint64_t>("Parse b-enc (unchecked)", [&]{return test_benc::test_read_lrat(test_benc::read_unsigned_unchecked,it,end);}, mm.size());
    MSG("Csum =" + to_string(csum));



//     char *begin = timeit<char *>("Copy",[&] {return test_parser::test_cnf_cpy(cnf_mm);},cnf_mm.size());
//     char *end = begin+cnf_mm.size();

}



int main(int argc, char **argv) {

    if (argc==3 && string(argv[1])=="parse_cnf") {
        test_parse_cnf(argv[2]);
        return 0;
    }

    if (argc==3 && string(argv[1])=="parse_lrat") {
        test_parse_lrat(argv[2]);
        return 0;
    }

    if (argc==3 && string(argv[1])=="dump") {
        read_dump_lrat(argv[2],cout);
        return 0;
    }

    if (argc==4 && string(argv[1])=="dump") {
        ofstream out(argv[3]);
        read_dump_lrat(argv[2],out);
        return 0;
    }


    bool M_checker=false;
    string cnf_name;
    string prf_name;

    if (argc==3) {
        cnf_name=argv[1];
        prf_name=argv[2];
    } else if (argc==4 && string(argv[1])=="mcheck") {
        M_checker=true;
        cnf_name=argv[2];
        prf_name=argv[3];
    } else error("usage: check [mcheck] <cnf-file> <lrat-file>");

/*    if (argc!=2) error("usage: dump <lrat-file>");
    read_dump_lrat(argv[1]);
*/


/*    if (argc!=2) error("usage: dump <cnf-file>");
    read_dump_cnf(argv[1]);
*/

    #ifdef PROFILING
    ProfilerStart("prof.out");
    #endif


    MSG("Mapping cnf file");
    MMFile cnf(cnf_name);
    MSG("Mapping proof file");
    MMFile prf(prf_name);

    posix_madvise((void*)cnf.begin(),cnf.size(),POSIX_MADV_SEQUENTIAL);
    posix_madvise((void*)prf.begin(),prf.size(),POSIX_MADV_SEQUENTIAL);

    if (M_checker) {
        Lrat_CtrlM ctrl(cnf.iterator(),prf.iterator());
        ctrl.check();
    } else {
        Lrat_CtrlU ctrl(cnf.iterator(),prf.iterator());
        ctrl.check();
    }

    cout<<"c VERIFIED UNSAT"<<endl;

    #ifdef PROFILING
    ProfilerStop();
    #endif

    return 0;
}
