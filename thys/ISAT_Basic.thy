theory ISAT_Basic
imports SAT_Basic
begin

  definition "consistent L \<equiv> \<forall>l\<in>L. neg_lit l\<notin>L"

  definition "set_lits F L \<equiv> { C - neg_lit`L | C. C\<in>F \<and> L \<inter> C = {} }"
  
  lemma set_lits_singleton: "set_lits F {l} = set_lit F l"
    unfolding set_lits_def set_lit_def 
    by clarsimp
  
  
  lemma set_lits_empty[simp]: "set_lits F {} = F"
    unfolding set_lits_def by auto

  lemma set_lits_insert': "consistent (insert l L) \<Longrightarrow> set_lits F (insert l L) = (set_lits (set_lit F l) L)"
    unfolding set_lits_def set_lit_def 
    apply safe
    apply clarsimp
    apply (metis Diff_insert2 Int_Diff empty_Diff)
    apply clarsimp
    subgoal for C
      by (metis Diff_insert2 consistent_def disjoint_insert(2) insertCI insert_Diff_single)
    done          
      
  lemma set_lits_insert[simp]: "consistent (insert l L) \<Longrightarrow> set_lits F (insert l L) = (set_lit (set_lits F L) l)"
    unfolding set_lits_def set_lit_def 
    apply (safe; clarsimp)
    subgoal by (metis DiffD1 Diff_insert)
    subgoal by blast
    by (simp add: consistent_def)
  
    
  lemma set_lit_swap: "l1\<noteq>neg_lit l2 \<Longrightarrow> set_lit (set_lit F l1) l2 = set_lit (set_lit F l2) l1"
    by (smt (verit) consistent_def insert_iff neg_lit_neq(1) neg_neg_lit set_lits_insert set_lits_insert' set_lits_singleton singletonD)


  datatype 'l IItem = 
      I "'l clause" 
    | Q "'l literal set" 
    | A_SAT "'l literal set" (* Formula mod model must be sat *)
    | A_UNSAT "'l literal set" (* Subset of query, and makes formula unsat already *)


  type_synonym 'l IState = "'l cnf * 'l literal set option"



  inductive isat_step where
    "isat_step (F,q) (I C) (insert C F,q)"
  | "consistent ls \<Longrightarrow> isat_step (F,None) (Q ls) (F, Some ls)"
  | "consistent (ls\<union>qls) \<Longrightarrow> sat (set_lits F (ls \<union> qls)) \<Longrightarrow> isat_step (F,Some qls) (A_SAT ls) (F,None)"
  | "\<lbrakk>consistent ls; ls\<subseteq>qls; \<not>sat(set_lits F ls)\<rbrakk> \<Longrightarrow> isat_step (F,Some qls) (A_UNSAT ls) (F,None)"


  fun isat_stepf where
    "isat_stepf (I C) (F,q) = Some (insert C F, q)"
  | "isat_stepf (Q ls) (F,None) = (if consistent ls then Some (F,Some ls) else None)"  
  | "isat_stepf (A_SAT ls) (F,Some qls) = (if consistent (ls\<union>qls) \<and> sat (set_lits F (ls \<union> qls)) then Some (F,None) else None)"
  | "isat_stepf (A_UNSAT ls) (F,Some qls) = (if consistent ls \<and> ls\<subseteq>qls \<and> \<not>sat(set_lits F ls) then Some (F,None) else None)"
  | "isat_stepf _ _ = None"
  
  lemma "isat_step s l s' \<longleftrightarrow> isat_stepf s l = Some s'"
    apply (cases "(s,l)" rule: isat_stepf.cases)
    by (auto simp: isat_step.simps)
  
  
  find_consts "_ option" name: fold
  
  fun fold_option where
    "fold_option f [] s = Some s"
  | "fold_option f (x#xs) s = (Option.bind (f x s) (fold_option f xs))"

  definition "ISound iis \<equiv> fold_option isat_stepf iis ({},None)"
    
  xxx, next step: formalize checker LTS, with read actions from interaction protocol and proof. (see paper)
  
  
  oops  xxx: phrase that as mfold over option monad!
  
  
  
  
  
  
  

end
