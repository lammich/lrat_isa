section \<open>Relaxed Partial Assignments\<close>
theory Relaxed_Assignment
imports Unit_Propagation
begin
  (* TODO: Move *)      
  lemma sat_add_taut[simp]: "is_syn_taut C \<Longrightarrow> sat (insert C F) = sat F"
    by (simp add: sat_def)  
    
  lemma sat_antimono: "F\<subseteq>F' \<Longrightarrow> sat F' \<Longrightarrow> sat F"
    unfolding sat_def sem_cnf_def by auto  
        
  
    
  subsection \<open>Abstract Ideas of LRUP (for paper)\<close>
  text \<open>These theorems back the description of the abstract idea behind LRUP in the paper\<close>

  definition neg_clause :: "'a clause \<Rightarrow> 'a cnf" where
    "neg_clause C \<equiv> { {neg_lit l} | l. l\<in>C }"

  lemma sem_neg_clause[simp]: "sem_cnf (neg_clause C) A \<longleftrightarrow> \<not>sem_clause C A"  
    unfolding neg_clause_def sem_cnf_def sem_clause_def 
    apply (safe; simp)
    using sem_neg_lit by blast
    
  text \<open>Equisatisfiability when inserting clause can be checked by showing that formula and negated clause is unsatisfiable. \<close>
  theorem pres_sat_by_conj_negated: "(\<not>sat (F \<union> neg_clause C)) \<Longrightarrow> (sat F \<longleftrightarrow> sat (insert C F))"
    by (auto simp: sat_def)

  text \<open>Abstract idea of unit propagation\<close>  
  theorem abs_unit_propagation:
    assumes "{l}\<in>F"  
    shows "sat F \<longleftrightarrow> sat ({ C - {neg_lit l} | C. C\<in>F \<and> l \<notin> C })"
  proof -
    from assms obtain F' where [simp]: "F = insert {l} F'" by blast
  
    have [simp]: "set_lit (insert {l} F') l = set_lit F' l"
      unfolding set_lit_def by blast
    
    have [simp]: "sem_lit l (\<sigma>(var_of_lit l := is_pos l))" for \<sigma>
      by (cases l; simp)
      
    have "sat F \<longleftrightarrow> sat (set_lit F l)"
      unfolding sat_def
      apply (safe; clarsimp)
      subgoal for \<sigma>
        apply (rule exI[where x=\<sigma>])
        unfolding sem_cnf_def sem_clause_def set_lit_def
        by fastforce
      subgoal for \<sigma>
        apply (rule exI[where x="\<sigma>(var_of_lit l := is_pos l)"])
        apply (simp add: sem_cnf_set)
        done
      done
      
    thus ?thesis unfolding set_lit_def by auto
  qed  
    
      
  lemma sat'_and_not_C_conv: "\<not>is_syn_taut C \<Longrightarrow> sat' F (and_not_C (\<lambda>_. None) C) \<longleftrightarrow> sat (F \<union> neg_clause C)"
    apply rule
    subgoal
      unfolding sat_iff_sat' is_syn_taut_conv sat'_def models'_def
      apply (clarsimp simp: sem_clause_def)
      using compat_lit sem_lit_and_not_C_conv by blast
    subgoal
      unfolding sat'_def models'_def sat_iff_sat'
      apply clarsimp
      using compat_and_not_C compat_assignment_empty by blast
    done
    
    
    
  text \<open>May be inconsistent, i.e., assigning a literal to true and false at the same time.\<close>

  subsection \<open>Definitions\<close>  
  type_synonym 'a rp_ass = "'a literal \<Rightarrow> bool"
  
  abbreviation (input) rpa_empty :: "'a rp_ass" where "rpa_empty \<equiv> \<lambda>_. False"
  
  
  definition is_true :: "'a rp_ass \<Rightarrow> 'a literal \<Rightarrow> bool" where "is_true A l \<equiv> A l"
  abbreviation "is_false A l \<equiv> is_true A (neg_lit l)"
  
  definition assign_lits :: "'a rp_ass \<Rightarrow> 'a literal set \<Rightarrow> 'a rp_ass" where
    "assign_lits A ls l \<equiv> if l\<in>ls then True else A l" 
    
  context 
    notes [simp] = assign_lits_def fun_eq_iff is_true_def
  begin  
    lemma assign_lits_empty[simp]: "assign_lits A {} = A" by auto
    lemma assign_lits_insert[simp]: "assign_lits A (insert l ls) = (assign_lits A ls)(l:=True)" by auto

    lemma assign_lits_union[simp]: "assign_lits A (ls\<^sub>1 \<union> ls\<^sub>2) = assign_lits (assign_lits A ls\<^sub>2) ls\<^sub>1" by auto
            
    lemma is_true_upd[simp]: "is_true (A(l:=True)) l' \<longleftrightarrow> l'=l \<or> is_true A l'" by auto
    
    lemma is_true_assign[simp]: "is_true (assign_lits A ls) l \<longleftrightarrow> l\<in>ls \<or> is_true A l" by auto
    
    lemma is_true_empty[simp]: "\<not>is_true rpa_empty l" by auto
    
  end  

  subsection \<open>Refinement to Partial Assignment\<close>        

  definition "rpa_consistent A \<equiv> \<forall>l. \<not>(is_true A l \<and> is_false A l)"
  definition "rpa_\<alpha> A \<equiv> \<lambda>v. if is_true A (Pos v) then Some True else if is_false A (Pos v) then Some False else None"  
  
  (* For Paper *)
  lemma "rpa_consistent A \<longleftrightarrow> (\<forall>l. \<not> (A l \<and> A (neg_lit l)))"
    unfolding rpa_consistent_def is_true_def
    by auto
  
    
  lemma rpa_empty_refine[simp]: 
    "rpa_consistent rpa_empty" 
    "rpa_\<alpha> rpa_empty = Map.empty"
    unfolding rpa_consistent_def rpa_\<alpha>_def by auto

  lemma rpa_is_true_refine[simp]: 
    assumes "rpa_consistent A" 
    shows "is_true A l \<longleftrightarrow> sem_lit' l (rpa_\<alpha> A) = Some True"  
    using assms
    unfolding rpa_consistent_def rpa_\<alpha>_def
    apply (cases l)
    by auto
    
  lemma rpa_set_\<alpha>[simp]:
    assumes "rpa_consistent A"
    assumes "sem_lit' l (rpa_\<alpha> A) \<noteq> Some False"
    shows
      "rpa_consistent (A(l := True))" 
      "rpa_\<alpha> (A(l:=True)) = assign_lit (rpa_\<alpha> A) l" 
    subgoal 
      using assms rpa_consistent_def by fastforce
    subgoal
      using assms 
      unfolding rpa_\<alpha>_def
      by (cases l; auto 0 4) 
    done  
  
      
  lemma rpa_consistent_taut: "\<not>is_syn_taut C \<Longrightarrow> rpa_consistent (assign_lits rpa_empty C)"
    unfolding rpa_consistent_def is_syn_taut_conv
    by auto
    
  lemma rpa_consistent_upd: "\<lbrakk> rpa_consistent A; \<not>is_false A l \<rbrakk> \<Longrightarrow> rpa_consistent (A(l:=True))"
    unfolding rpa_consistent_def
    by auto

  definition "rpa_and_not_C A C \<equiv> assign_lits A (neg_lit`C)"
  lemma is_true_rpa_and_not_C: "is_true (rpa_and_not_C A C) l \<longleftrightarrow> neg_lit l\<in>C \<or> is_true A l"
    by (cases l; auto simp: rpa_and_not_C_def)

  definition "rpa_is_blocked A C \<equiv> (\<exists>l\<in>C. is_true A l) \<or> is_syn_taut C"
  
  lemma rpa_is_blocked_refine[simp]: "rpa_consistent A \<Longrightarrow> rpa_is_blocked A C \<longleftrightarrow> is_blocked (rpa_\<alpha> A) C"
    unfolding is_blocked_def rpa_is_blocked_def sem_clause'_def
    by (auto simp: split: if_splits)
    
  lemma rpa_and_not_C_consistent:
    assumes "rpa_consistent A"
    assumes "\<not> rpa_is_blocked A C"
    shows "rpa_consistent (rpa_and_not_C A C)"
    using assms unfolding rpa_consistent_def rpa_and_not_C_def is_syn_taut_conv rpa_is_blocked_def
    by auto
    
  lemma rpa_and_not_C_refine'[simp]: 
    assumes C: "rpa_consistent A"
    assumes NB: "\<not>is_blocked (rpa_\<alpha> A) C"
    shows "rpa_consistent (rpa_and_not_C A C)"
      and "rpa_\<alpha> (rpa_and_not_C A C) = and_not_C (rpa_\<alpha> A) C"
  proof -
    
    from C NB show [simp]: "rpa_consistent (rpa_and_not_C A C)" 
      using rpa_and_not_C_consistent by force

    from NB have NTAUT: "Pos x \<in> C \<Longrightarrow> Neg x \<notin> C" for x
      unfolding is_blocked_def is_syn_taut_conv by auto   
      
    from NB have NTRUE: "l \<in> C \<Longrightarrow> sem_lit' l (rpa_\<alpha> A) \<noteq> Some True" for l
      unfolding is_blocked_def sem_clause'_def by metis
        
    show "rpa_\<alpha> (rpa_and_not_C A C) = and_not_C (rpa_\<alpha> A) C"
      unfolding rpa_\<alpha>_def rpa_and_not_C_def and_not_C_def
      by (auto simp: fun_eq_iff C dest: NTAUT NTRUE)
  qed    
    
    
  definition "rpa_is_conflict_clause A C \<equiv> (\<forall>l\<in>C. is_false A l)"  

  (* For paper *)
  lemma "rpa_is_conflict_clause A C = (\<forall>l\<in>C. A (neg_lit l))"  
    unfolding is_true_def rpa_is_conflict_clause_def ..
  
  
  lemma rpa_is_conflict_clause_refine'[simp]:
    assumes "rpa_consistent A"
    shows "rpa_is_conflict_clause A C \<longleftrightarrow> is_conflict_clause (rpa_\<alpha> A) C"
    using assms
    unfolding rpa_is_conflict_clause_def sem_clause'_def
    by (auto simp add: boolopt_neq_simps)
    

  subsection \<open>Unit or True Literal\<close>    
  text \<open>When doing a RUP proof, it does not matter if the clause is unit, 
    or if the found literal is just already assigned to true\<close>
  
  definition "is_uot_lit A C l 
    \<equiv> l\<in>C \<and> sem_lit' l A \<noteq> Some False \<and> (sem_clause' (C-{l}) A = Some False)"
  definition "is_uot_clause A C \<equiv> \<exists>l. is_uot_lit A C l"
  definition "the_uot_lit A C \<equiv> THE l. is_uot_lit A C l"

  lemma is_uot_lit_inj: "is_uot_lit A C l \<Longrightarrow> is_uot_lit A C l' \<Longrightarrow> l=l'"
    unfolding is_uot_lit_def 
    by (force simp: sem_clause'_def split!: if_splits)
    
  lemma is_uot_clause_alt: "is_uot_clause A C \<longleftrightarrow> is_uot_lit A C (the_uot_lit A C)"
    by (metis is_uot_clause_def is_uot_lit_inj theI the_uot_lit_def)
  
  
  lemma is_uot_cases:
    assumes "is_uot_lit A C l"
    obtains 
      "l\<in>C" "sem_lit' l A = Some True"  
    | "is_unit_lit A C l"
    using assms unfolding is_uot_lit_def is_unit_lit_def
    by force
    
  lemma uot_propagation: "\<lbrakk>C\<in>F; is_uot_lit A C l\<rbrakk> \<Longrightarrow> equiv' F A (assign_lit A l)"
    by (auto elim!: is_uot_cases simp: unit_propagation)


  subsubsection \<open>Refinement\<close>    
  definition "rpa_is_uot_lit A C l \<equiv> l\<in>C \<and> \<not>is_false A l \<and> (\<forall>l'\<in>C-{l}. is_false A l')"
  (* For paper *)
  lemma "rpa_is_uot_lit A C l \<longleftrightarrow> l\<in>C \<and> \<not>A(neg_lit l) \<and> (\<forall>l'\<in>C-{l}. A(neg_lit l'))"
    unfolding rpa_is_uot_lit_def is_true_def by blast

  lemma rpa_is_uot_lit_inj: "rpa_is_uot_lit A C l \<Longrightarrow> rpa_is_uot_lit A C l' \<Longrightarrow> l=l'"
    unfolding rpa_is_uot_lit_def
    by auto

  definition "rpa_is_uot_clause A C \<equiv> \<exists>l. rpa_is_uot_lit A C l"    
  definition "rpa_the_uot_lit A C \<equiv> THE l. rpa_is_uot_lit A C l"
  
  lemma rpa_is_uot_lit: "rpa_is_uot_clause A C \<Longrightarrow> rpa_is_uot_lit A C (rpa_the_uot_lit A C)"
    unfolding rpa_is_uot_clause_def rpa_the_uot_lit_def using rpa_is_uot_lit_inj
    by (metis theI)
  
  lemma rpa_is_uot_lit_refine[simp]:
    assumes "rpa_consistent A"
    shows "rpa_is_uot_lit A C l = is_uot_lit (rpa_\<alpha> A) C l"
    using assms
    unfolding rpa_is_uot_lit_def is_uot_lit_def
    by (auto 2 3 simp: sem_clause'_def)

  lemma rpa_is_uot_clause_refine[simp]:  
    assumes "rpa_consistent A" 
    shows "rpa_is_uot_clause A C \<longleftrightarrow> is_uot_clause (rpa_\<alpha> A) C"
    by (simp add: assms is_uot_clause_def rpa_is_uot_clause_def)
    
  lemma rpa_the_uot_lit_refine[simp]:  
    assumes "rpa_consistent A" "is_uot_clause (rpa_\<alpha> A) C"
    shows "rpa_the_uot_lit A C = the_uot_lit (rpa_\<alpha> A) C"
    using assms is_uot_clause_alt rpa_is_uot_clause_refine rpa_is_uot_lit rpa_is_uot_lit_inj rpa_is_uot_lit_refine by blast

  lemma is_uot_lit_not_False[simp]: "is_uot_lit A C l \<Longrightarrow> sem_lit' l A \<noteq> Some False"
    using is_uot_lit_def by blast
    
    
    
  subsection \<open>Abstract LRUP Checker\<close>        
    
  datatype 'a checker_state = 
      CNF "'a cnf" 
    | PREP_LEMMA "'a cnf" "'a clause" "'a rp_ass"  
    | PROOF "'a cnf" "'a clause" "'a rp_ass"
    | PROOF_DONE "'a cnf" "'a clause"
    | UNSAT
    | FAIL 

    
  inductive checker_trans :: "'a checker_state \<Rightarrow> 'a checker_state \<Rightarrow> bool" where
    ct_start_lemma: "checker_trans (CNF F) (PREP_LEMMA F {} rpa_empty)"
  | ct_add_lit: "checker_trans (PREP_LEMMA F C A) (PREP_LEMMA F (insert l C) (A(neg_lit l:=True)))"  
  | ct_start_proof: "checker_trans (PREP_LEMMA F C A) (PROOF F C A)"
  | ct_add_unit: "\<lbrakk> uC\<in>F; rpa_is_uot_lit A uC ul \<rbrakk> \<Longrightarrow> checker_trans (PROOF F C A) (PROOF F C (A(ul:=True)))"
  | ct_add_conflict: "\<lbrakk> uC\<in>F; rpa_is_conflict_clause A uC \<rbrakk> \<Longrightarrow> checker_trans (PROOF F C A) (PROOF_DONE F C)"
  | ct_del_clauses: "\<lbrakk> F' \<subseteq> F \<rbrakk> \<Longrightarrow> checker_trans (CNF F) (CNF F')" 
  | ct_finish_proof: "C\<noteq>{} \<Longrightarrow> checker_trans (PROOF_DONE F C) (CNF (insert C F))"
  | ct_finish_proof_unsat: "checker_trans (PROOF_DONE F {}) (UNSAT)"
  | ct_fail: "checker_trans s FAIL"
  | ct_refl: "checker_trans s s"   


  fun checker_invar :: "'a cnf \<Rightarrow> 'a checker_state \<Rightarrow> bool" where
    "checker_invar F\<^sub>0 (CNF F) \<longleftrightarrow> (sat F\<^sub>0 \<longrightarrow> sat F)"
  | "checker_invar F\<^sub>0 (PREP_LEMMA F C A) \<longleftrightarrow> 
        (sat F\<^sub>0 \<longrightarrow> sat F) 
      \<and> (is_syn_taut C \<or> rpa_consistent A \<and> rpa_\<alpha> A = and_not_C (\<lambda>_. None) C)"  
(*  | "checker_invar F\<^sub>0 (PROOF F C A) \<longleftrightarrow> 
        (sat F\<^sub>0 \<longrightarrow> sat F) 
      \<and> ( is_syn_taut C \<or> 
          (rpa_consistent A \<and> equiv' F (and_not_C (\<lambda>_. None) C) (rpa_\<alpha> A)) )"  
*)          
  | "checker_invar F\<^sub>0 (PROOF F C A) \<longleftrightarrow> 
        (sat F\<^sub>0 \<longrightarrow> sat F) 
      \<and> ( is_syn_taut C \<or> 
          (rpa_consistent A \<and> sat' F (and_not_C (\<lambda>_. None) C) = sat' F (rpa_\<alpha> A)) )"  
  | "checker_invar F\<^sub>0 (PROOF_DONE F C) \<longleftrightarrow> (sat F\<^sub>0 \<longrightarrow> sat (insert C F))"        
  | "checker_invar F\<^sub>0 (UNSAT) \<longleftrightarrow> \<not>sat F\<^sub>0"
  | "checker_invar _ FAIL \<longleftrightarrow> True"  

  
  (* For Paper *)
  experiment
  begin

    lemma rpa_\<alpha>_emp_and_not_C: "\<lbrakk> \<not>is_syn_taut C \<rbrakk> \<Longrightarrow> rpa_\<alpha> (\<lambda>l. neg_lit l \<in> C) = and_not_C (\<lambda>_. None) C"
      unfolding is_syn_taut_def
      by (auto simp: fun_eq_iff rpa_\<alpha>_def is_true_def and_not_C_def)
    
    lemma rpa_\<alpha>_eq_alt: "\<lbrakk>\<not>is_syn_taut C; rpa_consistent A\<rbrakk> \<Longrightarrow> rpa_\<alpha> A = and_not_C (\<lambda>_. None) C \<longleftrightarrow> A = (\<lambda>l. neg_lit l\<in>C)"
      unfolding is_syn_taut_def rpa_consistent_def
      apply (rule iffI; rule ext)
      subgoal for l
        apply (drule fun_cong[where x="var_of_lit l"])
        apply (cases l)
        by (auto simp: rpa_\<alpha>_def and_not_C_def is_true_def split: if_splits)
      subgoal for v
        unfolding rpa_\<alpha>_def and_not_C_def is_true_def by auto
      done
      
    lemma checker_invar_PREP_LEMMA_alt:
      "checker_invar F\<^sub>0 (PREP_LEMMA F C A) \<longleftrightarrow> 
          (sat F\<^sub>0 \<longrightarrow> sat F) 
        \<and> (is_syn_taut C \<or> rpa_consistent A \<and> A = (\<lambda>l. neg_lit l\<in>C))"    
        by (auto simp: rpa_\<alpha>_eq_alt)
  
    definition rpa_is_completion :: "'a rp_ass \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" 
      where "rpa_is_completion A \<sigma> \<equiv> \<forall>x. (A (Pos x) \<longrightarrow> \<sigma> x) \<and> (A (Neg x) \<longrightarrow> \<not>\<sigma> x)"
        
    lemma rpa_completion_implies_consistent: "rpa_is_completion A \<sigma> \<Longrightarrow> rpa_consistent A"  
      unfolding rpa_is_completion_def rpa_consistent_def is_true_def 
      by (metis neg_lit_neq(1) var_of_lit.elims var_of_lit_neg_eq)
      
    thm sat'_def  
      
      
    definition "rpa_models' F A \<equiv> { \<sigma>. rpa_is_completion A \<sigma> \<and> sem_cnf F \<sigma>}"
        
    lemma rpa_models_\<alpha>: "rpa_consistent A \<Longrightarrow> rpa_models' F A = models' F (rpa_\<alpha> A)"
      unfolding rpa_consistent_def rpa_models'_def models'_def rpa_is_completion_def compat_assignment_def rpa_\<alpha>_def is_true_def
      by clarsimp fastforce
    
    definition "rpa_sat' F A \<equiv> rpa_models' F A \<noteq> {}"  
    
    lemma rpa_sat'_\<alpha>: "rpa_consistent A \<Longrightarrow> rpa_sat' F A = sat' F (rpa_\<alpha> A) "
      unfolding rpa_sat'_def sat'_def by (simp add: rpa_models_\<alpha>)
      
    lemma "rpa_sat' F A \<longleftrightarrow> (\<exists>\<sigma>. sem_cnf F \<sigma> \<and> (\<forall>l. A l \<longrightarrow> sem_lit l \<sigma>))"
      unfolding rpa_models'_def rpa_sat'_def rpa_is_completion_def
      apply (safe; clarsimp)
      subgoal by (metis sem_lit.elims(3))
      subgoal by (metis sem_lit.simps(1) sem_lit.simps(2))
      done
    
    definition "rpa_equiv' F A A' \<equiv> rpa_models' F A = rpa_models' F A'"
        
    lemma "rpa_equiv' F A A' \<longleftrightarrow> (\<forall>\<sigma>. sem_cnf F \<sigma> \<longrightarrow> (rpa_is_completion A \<sigma> \<longleftrightarrow> rpa_is_completion A' \<sigma>))"
      unfolding rpa_equiv'_def rpa_models'_def by blast
    
    lemma rpa_emp_and_not_C_consistent: "rpa_consistent (\<lambda>l. neg_lit l\<in>C) \<longleftrightarrow> \<not>is_syn_taut C"
      unfolding is_true_def rpa_consistent_def is_syn_taut_conv neg_neg_lit
      by blast
    
    lemma equiv'_and_not_C_rpa_conv: "\<lbrakk> \<not>is_syn_taut C; rpa_consistent A \<rbrakk> \<Longrightarrow> equiv' F (and_not_C (\<lambda>_. None) C) (rpa_\<alpha> A) \<longleftrightarrow> rpa_equiv' F (\<lambda>l. neg_lit l\<in>C) A"    
      unfolding rpa_equiv'_def equiv'_def 
      by (simp add: rpa_models_\<alpha> rpa_emp_and_not_C_consistent rpa_\<alpha>_emp_and_not_C)
  
    lemma checker_invar_PROOF_alt: "checker_invar F\<^sub>0 (PROOF F C A) \<longleftrightarrow> 
        (sat F\<^sub>0 \<longrightarrow> sat F) 
      \<and> ( is_syn_taut C \<or> 
          (rpa_consistent A \<and> rpa_sat' F (\<lambda>l. neg_lit l\<in>C) = rpa_sat' F A))"  
      by (auto simp: rpa_sat'_\<alpha> rpa_emp_and_not_C_consistent rpa_\<alpha>_emp_and_not_C)
    
      
    lemma and_not_C_pres_models:
      assumes "models (F \<union> { {neg_lit l} | l. l\<in>C }) = {}"
      shows "models (insert C F) = models F"  
      using assms unfolding models_def sem_cnf_def sem_clause_def
      by fastforce
        
    lemma rup_step_correct:
      assumes "rpa_equiv' F (\<lambda>l. neg_lit l\<in>C) A" "E\<in>F" "\<forall>l\<in>E. A (neg_lit l)"
      assumes "sat F"
      shows "sat (insert C F)"
    proof -
      
      have "models (F \<union> { {neg_lit l} | l. l\<in>C }) = rpa_models' F (\<lambda>l. neg_lit l\<in>C)"
        unfolding rpa_models'_def  models_def rpa_is_completion_def
        unfolding sem_cnf_def sem_clause_def
        apply safe
        apply simp
        apply (metis (mono_tags, lifting) Un_iff mem_Collect_eq sem_lit.simps(2) sem_neg_lit singletonD)
        apply simp
        apply (metis (mono_tags, lifting) Un_iff mem_Collect_eq sem_lit.simps(1) sem_neg_lit singletonD)
        apply simp
        apply auto []
        apply auto [] 
        apply (metis sem_lit.elims(2))
        done
      
      moreover have "rpa_models' F A = {}" using \<open>E\<in>F\<close> \<open>\<forall>l\<in>E. A (neg_lit l)\<close>
        unfolding rpa_models'_def rpa_is_completion_def sem_cnf_def sem_clause_def
        apply clarsimp
        by (metis neg_lit.simps(1) neg_lit.simps(2) sem_lit.elims(2))
        
      ultimately show ?thesis 
        using assms(1) \<open>sat F\<close> and_not_C_pres_models[of F C]
        unfolding rpa_equiv'_def sat_iff_has_models  
        by simp
    qed    
      
    
    lemma rpa_uot_propagation:
      assumes "rpa_consistent A" "rpa_is_uot_lit A uC ul" "uC\<in>F" 
      shows "rpa_consistent (A(ul := True))" (is ?G1) 
        and "rpa_equiv' F A (A(ul := True))" (is ?G2)
    proof -  
      from assms show G1: "?G1" by auto
      
      from assms show "?G2"
        by (metis (no_types, lifting) G1 equiv'_def is_uot_lit_def rpa_equiv'_def 
          rpa_is_uot_lit_refine rpa_models_\<alpha> rpa_set_\<alpha>(2) uot_propagation)
          
    qed      


    lemma rpa_empty_sat: "rpa_sat' F (\<lambda>_. False) = sat F"
      by (simp add: rpa_sat'_\<alpha>)
        
    lemma "\<not>is_syn_taut C \<Longrightarrow> rpa_sat' F (rpa_and_not_C (\<lambda>_. False) C) = sat (F \<union> neg_clause C)" 
      by (simp add: rpa_sat'_\<alpha> rpa_and_not_C_consistent is_blocked_empy_taut sat'_and_not_C_conv)
      
    lemma rpa_uot_pres_sat:
      assumes "rpa_consistent A" "rpa_is_uot_lit A uC ul" "uC\<in>F" 
      shows "rpa_consistent (A(ul := True))" (is ?G1) 
        and "rpa_sat' F A = rpa_sat' F (A(ul := True))" (is ?G2)
    proof -  
      from assms show G1: "?G1" by auto
      
      from assms show "?G2"
        apply (simp add: rpa_sat'_\<alpha>)
        by (simp add: sat'_equiv uot_propagation)
          
    qed      
    
    lemma rpa_conflict_unsat:
      assumes "rpa_consistent A" "rpa_is_conflict_clause A cC" "cC\<in>F"
      shows "\<not>rpa_sat' F A"
      using assms
      apply (simp add: rpa_sat'_\<alpha>)
      by (simp add: conflict_clause_imp_no_models sat'_def)

    (* The consistency assumption is actually not needed here *)  
    lemma 
      assumes  "rpa_is_conflict_clause A cC" "cC\<in>F"
      shows "\<not>rpa_sat' F A"
      using assms
      by (metis (no_types, lifting) Collect_empty_eq conflict_clause_imp_no_models 
        rpa_completion_implies_consistent rpa_is_conflict_clause_refine' rpa_models'_def rpa_sat'_\<alpha> 
        rpa_sat'_def sat'_def)
      
      
          
          
  end
  
  
    
    
    
    
      
    
  lemma checker_invar_init[simp]: "checker_invar F (CNF F)" by auto  

  (* TODO: Move *)
  lemma is_syn_taut_insert[simp]: "is_syn_taut (insert l C) \<longleftrightarrow> is_syn_taut C \<or> neg_lit l\<in>C"
    unfolding is_syn_taut_def by auto
  
    
    
  lemma sem_and_Not_C_conv: "\<not>is_syn_taut C 
    \<Longrightarrow> sem_lit' l (and_not_C Map.empty C) 
      = (if l\<in>C then Some False else if neg_lit l\<in>C then Some True else None)"  
    unfolding is_syn_taut_def and_not_C_def
    apply (cases l) by auto
  
    
  lemma and_not_C_insert: "\<lbrakk>\<not>is_syn_taut C; neg_lit l \<notin> C\<rbrakk> 
    \<Longrightarrow> and_not_C Map.empty (insert l C) = assign_lit (and_not_C Map.empty C) (neg_lit l)"  
    unfolding and_not_C_def assign_lit_def is_syn_taut_def
    by (cases l; auto simp: fun_eq_iff split!: if_splits)
    
  lemma checker_trans_pres_invar:
    assumes "checker_invar F\<^sub>0 cs"
    assumes "checker_trans cs cs'"
    shows "checker_invar F\<^sub>0 cs'"
    using assms(2,1)
    apply cases
    apply simp_all
    subgoal by (auto simp: sem_and_Not_C_conv and_not_C_insert) 
    subgoal using is_blocked_empy_taut by fastforce 
    subgoal by (metis is_uot_lit_def rpa_consistent_upd rpa_is_uot_lit_def rpa_is_uot_lit_refine rpa_set_\<alpha>(2) sat'_equiv uot_propagation)
    subgoal for uC F A C
      apply (cases "is_syn_taut C"; simp)
      apply safe
      subgoal by (simp add: conflict_clause_imp_no_models sat'_def)
      subgoal by (auto simp add: sat'_and_not_C_conv dest: pres_sat_by_conj_negated)
      done  
    subgoal using sat_antimono by blast 
    subgoal by (simp add: unsat_empty_clause)
    done
    
  lemmas [simp del] = checker_invar.simps

  (* For paper *)
  
  theorem checker_trans_rtrancl_unsatI: "checker_trans\<^sup>*\<^sup>* (CNF F) UNSAT \<Longrightarrow> \<not>sat F"
    by (smt (verit, best) checker_invar.simps(1) checker_invar.simps(5) checker_trans_pres_invar rtranclp_induct)
  
      
  (*
  datatype 'a fbuilder_state = 
    FB_CNF "'a cnf"
  | FB_PREP_CLAUSE "'a cnf" "'a clause"  
  *)



end
