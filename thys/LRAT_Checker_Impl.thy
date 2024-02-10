section \<open>Implementation of Checker\<close>
theory LRAT_Checker_Impl
imports
  SAT_Basic 
  Relaxed_Assignment 
  "Isabelle_LLVM.IICF" 
  "Nat_Array_Dfun" 
  Unsigned_Literal 
  Trailed_Assignment 
  Zero_Term
  
  Debugging_Tools
  
  CNF_Parser_Impl
  LRAT_Parsers
begin

    
    
  term array_assn
  thm array_assn_def
  
  thm LLVM_DS_NArray.narray_assn_def
  
  thm LLVM_DS_Array.array_assn_def
  
  find_consts name: slice
  
  thm LLVM_DS_NArray.array_slice_assn_def
  
      

  (* TODO: Move, this version has better behaviour in automation! *)
  lemma if_bind_cond_refine': 
    assumes "ci \<le> \<Down>Id (RETURN b)"
    assumes "b \<Longrightarrow> ti\<le>\<Down>R t"
    assumes "\<not>b \<Longrightarrow> ei\<le>\<Down>R e"
    shows "do {b\<leftarrow>ci; if b then ti else ei} \<le> \<Down>R (if b then t else e)"
    using assms
    by (auto simp add: refine_pw_simps pw_le_iff)
    
  (* TODO: Move.  
    This is an ad-hoc concept to stop the VCG, thus that we can instantiate existentials, before
    further rules introduce new schematics too early. A vcg-mode that instantiates 
    existentials automatically before steps might be better suited here!
  *)  
  definition "VCG_STOP x \<equiv> x"  
  
  lemma VCG_STOP: "m \<le> m' \<Longrightarrow> VCG_STOP m \<le> m'"
    unfolding VCG_STOP_def by auto

    

  (* TODO: Move
    TODO: Generalizes IICF_Indexed_Array_List.b_rel_Id_list_rel_conv
  *)      
  lemma b_rel_list_rel_conv: "\<langle>b_rel S P\<rangle>list_rel = b_rel (\<langle>S\<rangle>list_rel) (\<lambda>xs. \<forall>x\<in>set xs. P x)"  
  proof -
    have "(xs,xs')\<in>\<langle>b_rel S P\<rangle>list_rel \<longleftrightarrow> (xs,xs')\<in>b_rel (\<langle>S\<rangle>list_rel) (\<lambda>xs. \<forall>x\<in>set xs. P x)" for xs xs'
      apply (cases "length xs = length xs'")
      subgoal 
        apply (induction xs xs' rule: list_induct2)
        by auto
      subgoal by (auto dest: list_rel_imp_same_length)
      done
    thus ?thesis by auto  
  qed
    
  
    
  (* TODO: Move *)    
  lemmas [refine del] = FOREACHcd_refine
  lemma FOREACHcd_refine_stronger[refine]:
    assumes [simp]: "finite s \<Longrightarrow> finite s'"
    assumes S: "(s',s)\<in>\<langle>S\<rangle>set_rel"
    assumes SV: "single_valued S"
    assumes R0: "(\<sigma>',\<sigma>)\<in>R"
    assumes C: "\<And>\<sigma>' \<sigma>. (\<sigma>',\<sigma>)\<in>R \<Longrightarrow> (c' \<sigma>', c \<sigma>)\<in>bool_rel"
    assumes F: "\<And>x' x \<sigma>' \<sigma>. \<lbrakk>(x', x) \<in> S; (\<sigma>', \<sigma>) \<in> R; x\<in>s\<rbrakk>
       \<Longrightarrow> f' x' \<sigma>' \<le> \<Down> R (f x \<sigma>)"
    shows "FOREACHcd s' c' f' \<sigma>' \<le> \<Down>R (FOREACHcdi I s c f \<sigma>)"
  proof -
    have [refine_dref_RELATES]: "RELATES S" by (simp add: RELATES_def)
  
    from SV obtain \<alpha> I where [simp]: "S=br \<alpha> I" by (rule single_valued_as_brE)
    with S have [simp]: "s=\<alpha>`s'" and [simp]: "\<forall>x\<in>s'. I x" 
      by (auto simp: br_set_rel_alt)
    
    show ?thesis
      unfolding FOREACHcd_def FOREACHcdi_def
      
      find_in_thms nfoldli in refine
      
      find_theorems nfoldli list_rel
      
      
      apply (refine_rcg nfoldli_refine[where S="b_rel S (\<lambda>x. x\<in>s)"])
      
      apply refine_dref_type
      subgoal by simp
      subgoal
        apply (auto simp: pw_le_iff refine_pw_simps)
        using S
        apply (rule_tac x="map \<alpha> x" in exI)
        apply (auto simp: map_in_list_rel_conv)
        done
      subgoal 
        by (simp add: b_rel_list_rel_conv)
      subgoal using R0 by auto
      subgoal using C by auto  
      subgoal using F by force 
      done
  qed    
    
    




  subsection \<open>Abstract Algorithms\<close>

  subsubsection \<open>Checking for Unit or Tautology\<close>
    
  definition "check_uot_invar A \<equiv> \<lambda>C\<^sub>1 _ (ul,err). \<not>err \<longrightarrow> (case ul of 
      None \<Rightarrow> rpa_is_conflict_clause A C\<^sub>1
    | Some l \<Rightarrow> rpa_is_uot_lit A C\<^sub>1 l)"
  
  (*  
  definition "check_uot A C \<equiv> FOREACHcdi (check_uot_invar A) C (\<lambda>_. True) (\<lambda>l (ul,err). doN {
    if is_false A l then RETURN (ul,err)
    else if is_None ul then RETURN (Some l,err)
    else RETURN (ul,True)
  }) (None,False)"
  *)
    
  lemma rpa_is_conflict_clause_empty[simp]: "rpa_is_conflict_clause A {}" 
    unfolding rpa_is_conflict_clause_def by auto 
    
  lemma rpa_is_conflict_clause_insert[simp]: "rpa_is_conflict_clause A (insert l C) \<longleftrightarrow> is_false A l \<and> rpa_is_conflict_clause A C"  
    unfolding rpa_is_conflict_clause_def by auto
  
  lemma rpa_is_uot_lit_insert_false[simp]: "is_false A l' \<Longrightarrow> rpa_is_uot_lit A (insert l' C) l \<longleftrightarrow> rpa_is_uot_lit A C l"  
    unfolding rpa_is_uot_lit_def by blast
    
  lemma rpa_is_uot_lit_insert_nfalseI: "\<not>is_false A l \<Longrightarrow> rpa_is_conflict_clause A C \<Longrightarrow> rpa_is_uot_lit A (insert l C) l"  
    unfolding rpa_is_uot_lit_def rpa_is_conflict_clause_def by auto
      
  (*  
  lemma check_uot_correct[refine_vcg]: "finite C \<Longrightarrow> check_uot A C 
    \<le> SPEC (\<lambda>(ul,err). \<not>err 
          \<longrightarrow> (case ul of 
                None \<Rightarrow> rpa_is_conflict_clause A C
              | Some l \<Rightarrow> rpa_is_uot_lit A C l))"
    unfolding check_uot_def
    apply refine_vcg
    apply (clarsimp_all split!: option.split)
    unfolding check_uot_invar_def
    by (auto split!: option.split simp: rpa_is_uot_lit_insert_nfalseI)

  (* For paper: definition shown in paper *)
  term "check_uot :: 'a rp_ass \<Rightarrow> 'a clause \<Rightarrow> ('a literal option \<times> bool) nres"
  lemma "check_uot A C = FOREACHcdi (check_uot_invar A) C (\<lambda>_. True) 
    (\<lambda>l (ul,err). do {
        if A (neg_lit l) then RETURN (ul,err)
        else if ul = None then RETURN (Some l,err)
        else RETURN (ul,True)
      }
    ) (None,False)"
    unfolding check_uot_def is_true_def is_None_def
    apply (fo_rule cong refl)+
    by (auto simp: fun_eq_iff)
    
  *)
  (*
    We now refine the check_uot algorithm to use iteration over a clause in the clause database
    
    For that, we refine the loop body, and then instantiate the clause-db-iterator locale
  *)      
  

  (*
    Step 1: rpan
  *)  

  abbreviation (input) "err_code_mult_undecided \<equiv> 0x2"
  abbreviation (input) "err_code_invalid_id \<equiv> 0x3"
  
    
  definition "check_uot2_body A \<equiv> \<lambda>l (ul,err). doN {
    if\<^sub>N rpan_is_false_unchecked A l then RETURN (ul,err)
    else if is_None ul then RETURN (Some l,err)
    else doN {
      ERROR_lit err_code_mult_undecided l;
      ERROR_lito err_code_mult_undecided ul;
    
      RETURN (ul,True)
    }
  }"  
  
  definition [simp]: "check_uot2_cond _ _ = True"
  

  (*
  definition "check_uot2 A C \<equiv> FOREACHcd C (check_uot2_cond A) (check_uot2_body A) (None,False)"
    
  lemma check_uot2_refine: 
    assumes [simp]: "rpan_invar A"
    assumes VB: "var_of_lit`C \<subseteq> rpan_dom A"
    shows "check_uot2 A C \<le> \<Down>(Id \<times>\<^sub>r bool_rel) (check_uot (rpan_\<alpha> A) C)"  
    unfolding check_uot2_def check_uot2_body_def check_uot_def
    apply (refine_vcg if_bind_cond_refine')
    apply (refine_dref_type)
    apply (simp_all add: VB[THEN set_mp])
    done
  *)  
    
  (*
    Step 2: implement body and condition
  *)
  
  sepref_definition check_uot2_body_impl [llvm_inline] is "uncurry2 check_uot2_body" :: "rpan_assn\<^sup>k *\<^sub>a ulit_assn\<^sup>k *\<^sub>a (ulito_assn \<times>\<^sub>a bool1_assn)\<^sup>d \<rightarrow>\<^sub>a ulito_assn \<times>\<^sub>a bool1_assn"
    unfolding check_uot2_body_def
    by sepref  
  (* Note: we destroy the state, though it is pure. This better matches the locale assumptions *)
  
  sepref_definition check_uot2_cond_impl [llvm_inline] is "uncurry (RETURN oo check_uot2_cond)" :: "rpan_assn\<^sup>k *\<^sub>a (ulito_assn \<times>\<^sub>a bool1_assn)\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding check_uot2_cond_def
    by sepref
    

  (*
    Instantiate locale
  *)  
  interpretation uot: clause_iteration_setup check_uot2_cond_impl check_uot2_cond check_uot2_body_impl check_uot2_body rpan_assn "(ulito_assn \<times>\<^sub>a bool1_assn)"
    apply unfold_locales
    apply (rule check_uot2_cond_impl.refine)
    apply (rule check_uot2_body_impl.refine)
    done
    
    
  (*
    Prove iteration correct
  *)

  lemma "(\<forall>C\<in>ran cdb. var_of_lit`C \<subseteq> rpan_dom A) \<longleftrightarrow> var_of_lit`\<Union>(ran cdb) \<subseteq> rpan_dom A" by auto
  
  lemma uot_cdb_iterate_clause_correct[refine_vcg]:
    assumes [simp]: "rpan_invar A"
    assumes CIDV: "cdb cid = Some C"
    assumes VB: "\<forall>C\<in>ran cdb. var_of_lit`C \<subseteq> rpan_dom A"
    shows "uot.cdb_iterate_clause cdb cid A (ulito_None,False) \<le> SPEC (\<lambda>(ul,err). \<not>err \<longrightarrow> 
      (case ul of 
          None \<Rightarrow> rpa_is_conflict_clause (rpan_\<alpha> A) C
        | Some l \<Rightarrow> rpa_is_uot_lit (rpan_\<alpha> A) C l 
      )
    )"
    unfolding uot.cdb_iterate_clause_def check_uot2_cond_def check_uot2_body_def
    apply (subst FOREACHcdi_def[where I="check_uot_invar (rpan_\<alpha> A)", symmetric])
    apply refine_vcg
    unfolding check_uot_invar_def
    using CIDV VB
    by (auto split!: option.splits simp: rpa_is_uot_lit_insert_nfalseI ran_def)
    
  
  definition cdb_check_uot :: "rpan \<Rightarrow> cdb \<Rightarrow> nat \<Rightarrow> (dv_lit option \<times> bool) nres"
    where "cdb_check_uot A cdb cid \<equiv> do {
    if\<^sub>N cdb_contains cid cdb then do {
      uot.cdb_iterate_clause cdb cid A (ulito_None,False)
    } else doN {
      ERROR_cid err_code_invalid_id cid;
      RETURN (ulito_None,True)
    }
  
  }"
  
  lemma rpan_is_false_unchecked_alt: "rpan_is_false_unchecked A l = doN {
    ASSERT (ulit_of (neg_lit l) < length (fst A));
    RETURN (fst A ! ulit_of (neg_lit l))
  }"
    unfolding rpan_is_true_unchecked_def bla_get_unchecked_def
    apply (cases A; simp)
    done
  
  
  (* For paper: explicit abstract version of check_uot *)  
  lemma "cdb_check_uot A cdb cid = (
    if cid \<in> dom cdb then doN {
      let C = the (cdb cid);
      ASSUME (finite C);
      FOREACHcd C (\<lambda>uv. True) (\<lambda>l (ul, err). doN {
        ASSERT (ulit_of (neg_lit l) < length (fst A));
        if fst A ! ulit_of (neg_lit l) then RETURN (ul, err)
        else if is_None ul then RETURN (Some l, err) 
        else RETURN (ul, True)
      }) (None, False)
    } else RETURN (None, True)
    )"
    unfolding cdb_check_uot_def uot.cdb_iterate_clause_def check_uot2_cond_def check_uot2_body_def Let_def rpan_is_false_unchecked_alt
    apply simp
    apply (fo_rule cong | simp | intro ext impI conjI)+
    done
    
  
  
  
  lemma cdb_check_uot_correct:
    assumes "rpan_invar A"
    assumes "\<forall>C\<in>ran cdb. var_of_lit`C \<subseteq> rpan_dom A"
    shows "cdb_check_uot A cdb cid \<le> SPEC (\<lambda>(ul,err). \<not>err \<longrightarrow> 
      (\<exists>C. cdb cid = Some C \<and> (case ul of 
          None \<Rightarrow> rpa_is_conflict_clause (rpan_\<alpha> A) C
        | Some l \<Rightarrow> rpa_is_uot_lit (rpan_\<alpha> A) C l 
      ))
    )"
  proof -  
    have aux: "cid\<in>dom cdb \<Longrightarrow> cdb cid = Some (the (cdb cid))" by auto
  
    show ?thesis
      unfolding cdb_check_uot_def cdb_contains_def
      apply refine_vcg
      apply (rule assms)
      apply (erule aux)
      using assms
      by (auto split: option.split)
      
  qed
        
  lemma cdb_check_uot_correct_weak[refine_vcg]:
    assumes "rpan_invar A"
    assumes "\<forall>C\<in>ran cdb. var_of_lit`C \<subseteq> rpan_dom A"
    shows "cdb_check_uot A cdb cid \<le> SPEC (\<lambda>(ul,err). \<not>err \<longrightarrow> 
      (\<exists>C\<in>ran cdb. (case ul of 
          None \<Rightarrow> rpa_is_conflict_clause (rpan_\<alpha> A) C
        | Some l \<Rightarrow> rpa_is_uot_lit (rpan_\<alpha> A) C l 
      ))
    )"
    apply (refine_vcg cdb_check_uot_correct)
    using assms
    by (auto 0 3 split: option.splits intro: ranI)
  
  (* Implement *)  
    
  find_theorems ulito_assn hn_refine
  
  sepref_def cdb_check_uot_impl is "uncurry2 cdb_check_uot" :: "rpan_assn\<^sup>k *\<^sub>a cdb_assn\<^sup>k *\<^sub>a cid_assn\<^sup>k \<rightarrow>\<^sub>a ulito_assn \<times>\<^sub>a bool1_assn"
    unfolding cdb_check_uot_def
    by sepref
  
    
        
  (*  
    
  lemma cdb_check_uot_correct[refine_vcg]:
    assumes [simp]: "cdb_invar cdb"
    shows "uot.cdb_iterate_clause A cdb cid \<le> SPEC (\<lambda>(ul,err). \<not>err \<longrightarrow> 
      (\<exists>C\<in>ran cdb. case ul of 
          None \<Rightarrow> rpa_is_conflict_clause A C
        | Some l \<Rightarrow> rpa_is_uot_lit A C l 
      )
    )"
    unfolding cdb_check_uot_def
    apply refine_vcg
    apply simp_all
    by (auto split: option.splits intro: cdb_lookup_correct) 
  
    
      
      
  
  
  (* Step 1: look up the clause in cdb *)
  
  definition "cdb_check_uot A cdb cid \<equiv> do {
    ASSERT(cdb_invar cdb);
    if cdb_id_valid cdb cid then do {
      check_uot A (cdb_lookup cdb cid)
    } else
      RETURN (None,True)
  
  }"
      
  lemma cdb_check_uot_correct[refine_vcg]:
    assumes [simp]: "cdb_invar cdb"
    shows "cdb_check_uot A cdb cid \<le> SPEC (\<lambda>(ul,err). \<not>err \<longrightarrow> 
      (\<exists>C\<in>cdb_\<alpha> cdb. case ul of 
          None \<Rightarrow> rpa_is_conflict_clause A C
        | Some l \<Rightarrow> rpa_is_uot_lit A C l 
      )
    )"
    unfolding cdb_check_uot_def
    apply refine_vcg
    apply simp_all
    by (auto split: option.splits intro: cdb_lookup_correct) 

  (* Step 2: use iterator of clause database *)  
      
  definition "cdb_check_uot2 A cdb cid = do {
      _ \<leftarrow> Refine_Basic.ASSERT (cdb_invar cdb);
      if cdb_id_valid cdb cid
      then cdb_iterate cdb cid (\<lambda>_. True)
            (\<lambda>l (ul, err). do {
                isf \<leftarrow> rpan_is_false_unchecked A l;
                if isf then Refine_Basic.RETURN (ul, err)
                else if is_None ul then Refine_Basic.RETURN (Some l, err) 
                else Refine_Basic.RETURN (ul, True)
             })
            (ulito_None, False)
      else Refine_Basic.RETURN (ulito_None, True)
    }"
  
  
  
  lemma cdb_check_uot2_refine: 
    assumes [simp]: "rpan_invar A"
    assumes VB: "var_of_lit`cdb_lits cdb \<subseteq> rpan_dom A"
    shows "cdb_check_uot2 A cdb cid \<le> \<Down>(Id \<times>\<^sub>r bool_rel) (cdb_check_uot (rpan_\<alpha> A) cdb cid)"  
    unfolding cdb_check_uot2_def check_uot_def cdb_check_uot_def FOREACHcdi_def  
    apply (refine_vcg cdb_iterate_foreach_refine if_bind_cond_refine)
    apply (simp_all add: in_br_conv ulito_rel_def)
    unfolding cdb_invar_def using VB 
    by auto
    

  (* Step 3: Inline cdb-iterator. 
    Code gets more low-level, but we can better see what exactly happens in 
    this performance critical inner loop.
  *)  
    
  abbreviation (input) "err_code_mult_undecided \<equiv> 0x2"
  abbreviation (input) "err_code_invalid_id \<equiv> 0x3"

  definition cdb_check_uot3 :: "rpan \<Rightarrow> clause_db \<Rightarrow> nat \<Rightarrow> (dv_lit option \<times> bool) nres" 
  where "cdb_check_uot3 A cdb cid \<equiv>  doN {
    ASSERT (cdb_invar cdb);
    if cdb_id_valid cdb cid then doN {
      idx \<leftarrow> cdb_lookup_cid cdb cid;
      (_, _, ul, err) \<leftarrow> WHILE\<^sub>T 
        (\<lambda>(brk, _). \<not> brk)
        (\<lambda>(brk, i, ul, err). do {
          ASSERT (i<cdb_db_len cdb);
          l\<leftarrow>cdb_get_db cdb i;
          if is_None l then RETURN (True, i, ul, err)
          else do {
            isf\<leftarrow>rpan_is_false_unchecked A (the l);
            if isf then RETURN (False, Suc i, ul, err) 
            else if is_None ul then RETURN (False, Suc i, l, err)
            else doN {
              ERROR_lito err_code_mult_undecided l;
              ERROR_lito err_code_mult_undecided ul;
              RETURN (False, Suc i, ul, True)
            }
          }
        })
        (False, idx, ulito_None, False);
      RETURN (ul,err)
    } else doN {
      ERROR_cid err_code_invalid_id cid;
      RETURN (ulito_None, True)
    }
  }"  

  lemma cdb_lookup_cid_eq: "cdb_lookup_cid (ml,db,cm,bnd) i = doN {ASSERT (i\<in>zdom 0 cm); RETURN (cm i)}"
    unfolding cdb_lookup_cid_def by auto

  lemma cdb_get_db_eq: "cdb_get_db (ml,db,cm,bnd) i = mop_list_get db i"
    unfolding cdb_get_db_def by auto    
  
    
  lemma indep_double_ASSERT_conv: "doN { ASSERT P; ASSERT P; m } = doN { ASSERT P; m }"
    by (auto simp: pw_eq_iff refine_pw_simps)  
    
  lemma cdb_check_uot3_refine: "cdb_check_uot3 A cdb cid = cdb_check_uot2 A cdb cid"
    unfolding cdb_check_uot3_def cdb_check_uot2_def cdb_iterate_def zseg_fold_def 
    unfolding ulito_is_zero_def ulito_zero_def ulit_wrapo_def ulito_the_def cdb_db_len_def
    apply (cases cdb; 
      simp 
        add: cdb_lookup_cid_eq cdb_get_db_eq indep_double_ASSERT_conv
        split del: if_split 
        cong: if_cong)
    
    apply (repeat_all_new \<open>fo_rule arg_cong fun_cong arg_cong2 | rule ext\<close>)
    apply (clarsimp simp: pw_eq_iff refine_pw_simps)
    by blast
    
  lemma cdb_check_uot3_correct[refine_vcg]:
    assumes CDBI: "cdb_invar cdb"
    assumes AI: "rpan_invar A"
    assumes VB: "var_of_lit`cdb_lits cdb \<subseteq> rpan_dom A"
    shows "cdb_check_uot3 A cdb cid \<le> SPEC (\<lambda>(ul,err). (\<not>err \<longrightarrow> 
      (\<exists>C\<in>cdb_\<alpha> cdb. case ul of 
          None \<Rightarrow> rpa_is_conflict_clause (rpan_\<alpha> A) C
        | Some l \<Rightarrow> rpa_is_uot_lit (rpan_\<alpha> A) C l 
      )
    ))"
  proof -
    note cdb_check_uot3_refine
    also note cdb_check_uot2_refine[OF AI VB]
    also note cdb_check_uot_correct[OF CDBI]
    finally show ?thesis
      apply (rule order_trans)
      by (auto simp: pw_le_iff refine_pw_simps in_br_conv ulito_rel_def) 
    
  qed    
      
  *)
  
  
  
  subsubsection \<open>Checker States\<close>
  
  (*
    Checker state during proof phase:
      err: error flag
      confl: conflict flag (we saw a conflict clause)
      A: assignment
      cbld: clause builder
      cdb: clause database
    
  *)  

  definition "cs_common_invar cap A cbld cdb \<equiv>
      rpan_invar A
    \<and> cbld_invar cbld \<and> cap \<le> cbld_\<alpha>_cap cbld
    \<and> ulit_of`(\<Union>(ran cdb)) \<subseteq> {0..cbld_\<alpha>_maxlit cbld}  
    \<and> (\<forall>C\<in>ran cdb. var_of_lit`C \<subseteq> rpan_dom A)
    \<and> (var_of_lit`cbld_\<alpha>_clause cbld \<subseteq> rpan_dom A)
  "
  
  
  type_synonym checker_state_in_proof = "bool \<times> bool \<times> rpan \<times> cbld \<times> cdb"

  definition cs_ip_invar :: "nat \<Rightarrow> checker_state_in_proof \<Rightarrow> bool" where  
    "cs_ip_invar cap \<equiv> \<lambda>(err,confl,A,cbld,cdb). cs_common_invar cap A cbld cdb \<and> (\<not>err \<longrightarrow> cap + 1 \<le> cbld_\<alpha>_cap cbld) \<and> cap\<le>rpan_cap A"
  
  definition cs_ip_\<alpha> :: "checker_state_in_proof \<Rightarrow> dimacs_var checker_state" where
    "cs_ip_\<alpha> \<equiv> \<lambda>(err,confl,A,cbld,cdb). 
      if err then checker_state.FAIL 
      else if confl then PROOF_DONE (ran cdb) (cbld_\<alpha>_clause cbld)
      else PROOF (ran cdb) (cbld_\<alpha>_clause cbld) (rpan_\<alpha> A)"

  lemma cs_ip_invar_antimono: "cs_ip_invar cap' csip \<Longrightarrow> cap\<le>cap' \<Longrightarrow> cs_ip_invar cap csip"
    unfolding cs_ip_invar_def cs_common_invar_def
    by auto  

    
    
  (*
    Checker state outside proof phase:
  
    error \<times> unsat \<times> clausedb \<times> cbld (unused, empty) \<times> assignment (unused)
    
    Note that the order is different to checker_state_in_proof, to not
    accidentally mix up the two types.
  *)  
  type_synonym checker_state_out_proof = "bool \<times> bool \<times> cdb \<times> cbld \<times> rpan"
  
  definition cs_op_invar :: "nat \<Rightarrow> checker_state_out_proof \<Rightarrow> bool" where  
    "cs_op_invar cap \<equiv> \<lambda>(err,unsat,cdb,cbld,A). 
      cs_common_invar cap A cbld cdb
      \<and> cbld_\<alpha>_clause cbld = {}
      "
  
  definition cs_op_\<alpha> :: "checker_state_out_proof \<Rightarrow> dimacs_var checker_state" where
    "cs_op_\<alpha> \<equiv> \<lambda>(err,unsat,cdb,cbld,A). 
      if err then checker_state.FAIL 
      else if unsat then checker_state.UNSAT
      else CNF (ran cdb)"
      
  lemma cs_op_invar_antimono: "cs_op_invar cap' csop \<Longrightarrow> cap\<le>cap' \<Longrightarrow> cs_op_invar cap csop"
    unfolding cs_op_invar_def cs_common_invar_def
    by auto  

  lemma cs_op_invar_error_antimono: "cs_op_invar cap' (err,unsat,A,cdb) \<Longrightarrow> cap\<le>cap' \<Longrightarrow> cs_op_invar cap (True,unsat,A,cdb)"
    unfolding cs_op_invar_def cs_common_invar_def
    by auto  
    
          
  definition csop_is_unsat :: "checker_state_out_proof \<Rightarrow> bool" where 
    "csop_is_unsat \<equiv> \<lambda>(err,unsat,A,cdb). unsat"    
      
  definition csop_is_error :: "checker_state_out_proof \<Rightarrow> bool" where "csop_is_error \<equiv> \<lambda>(err,_). err"
    
  definition csop_set_error :: "checker_state_out_proof \<Rightarrow> checker_state_out_proof" where
    "csop_set_error \<equiv> \<lambda>(_,rest). (True,rest)"
    
  lemma csop_set_error_error[simp]: "csop_is_error (csop_set_error cs)"  
    unfolding csop_is_error_def csop_set_error_def
    by (auto split: prod.split)
    
  lemma cs_op_invar_set_error[simp]: "cs_op_invar cap cs \<Longrightarrow> cs_op_invar cap (csop_set_error cs)"  
    unfolding cs_op_invar_def csop_set_error_def
    by auto
    
  lemma csop_is_error_correct[simp]: "csop_is_error csop \<longleftrightarrow> cs_op_\<alpha> csop = FAIL"
    unfolding csop_is_error_def cs_op_\<alpha>_def 
    apply (cases csop)
    by simp

  lemma csop_set_error_correct[simp]: "cs_op_\<alpha> (csop_set_error csop) = FAIL"  
    unfolding csop_set_error_def cs_op_\<alpha>_def by (cases csop) auto
    
    
    
  (*
    Checker state while building lemma
  
    err \<times> ass \<times> cbld \<times> cdb
  *)   
  type_synonym checker_state_build_lemma = "bool \<times> rpan \<times> cbld \<times> cdb"
    
  definition cs_bl_invar :: "nat \<Rightarrow> checker_state_build_lemma \<Rightarrow> bool" where
    "cs_bl_invar cap \<equiv> \<lambda>(err,A,cbld,cdb). 
      cs_common_invar cap A cbld cdb
    \<and> rpan_\<alpha> A = rpa_and_not_C rpa_empty (cbld_\<alpha>_clause cbld)  
    \<and> cap\<le>rpan_cap A
    "
    
  lemma cs_bl_invar_antimono: "cs_bl_invar cap' csbl \<Longrightarrow> cap\<le>cap' \<Longrightarrow> cs_bl_invar cap csbl"
    unfolding cs_bl_invar_def cs_common_invar_def
    by auto  
    

  definition cs_bl_\<alpha> :: "checker_state_build_lemma \<Rightarrow> dimacs_var checker_state" where
    "cs_bl_\<alpha> \<equiv> \<lambda>(err,A,cbld,cdb). 
      if err then checker_state.FAIL
      else PREP_LEMMA (ran cdb) (cbld_\<alpha>_clause cbld) (rpan_\<alpha> A)
    "    
    
    
    
    
    
  (*
    Make a proof step
      cid -- id of next unit or conflict clause
  *)    
  definition proof_step :: "nat \<Rightarrow> checker_state_in_proof \<Rightarrow> checker_state_in_proof nres" where 
    "proof_step cid \<equiv> \<lambda>(err,confl,A,cbld,cdb). if err then 
      RETURN (err,confl,A,cbld,cdb)
    else do {
      (ul,err') \<leftarrow> cdb_check_uot A cdb cid;
      if err' then
        RETURN (err',confl,A,cbld,cdb)
      else if is_None ul then 
        RETURN (err,True,A,cbld,cdb)
      else do {
        A \<leftarrow> rpan_set_unchecked A (the ul);
        RETURN (err,confl,A,cbld,cdb)
      }  
    }" 
    
  lemma proof_step_correct[refine_vcg]: "\<lbrakk>cs_ip_invar cap csip; cap>0 \<rbrakk> 
    \<Longrightarrow> proof_step cid csip \<le> SPEC (\<lambda>csip'. 
      cs_ip_invar (cap-1) csip'
    \<and> checker_trans(cs_ip_\<alpha> csip) (cs_ip_\<alpha> csip') 
    )"  
    unfolding proof_step_def
    apply refine_vcg
    apply clarsimp_all
    unfolding cs_ip_invar_def cs_common_invar_def
    apply clarsimp_all 
    apply (all \<open>(intro conjI)?\<close>)
    apply simp_all  (* Solves some linarith-goals, that clarsimp does not solve *)
    subgoal
      by (auto simp add: cs_ip_\<alpha>_def split: option.splits simp: ct_fail)
    subgoal
      by (auto simp add: cs_ip_\<alpha>_def split: option.splits simp: ct_refl ct_fail)
    subgoal
      by (auto simp add: cs_ip_\<alpha>_def simp: ct_refl ct_fail)
    subgoal
      by (auto simp add: cs_ip_\<alpha>_def split: option.splits simp: ct_refl ct_fail ct_add_conflict)
    subgoal
      unfolding rpa_is_uot_lit_def
      by auto
    subgoal
      by (auto simp add: cs_ip_\<alpha>_def simp: ct_refl ct_fail ct_add_unit)
    done  
  

  (*
    Finish proof.
  *)  
  abbreviation (input) "err_code_no_conflict \<equiv> 0x4"
  definition finish_proof :: "nat \<Rightarrow> checker_state_in_proof \<Rightarrow> checker_state_out_proof nres" where
    "finish_proof cid \<equiv> \<lambda>(err,confl,A,cbld,cdb). 
      if err then doN {
        cbld \<leftarrow> cbld_abort_clause cbld;
        RETURN (err,False,cdb,cbld,A)
      } else if \<not>confl then doN {
        ERROR err_code_no_conflict;
        cbld \<leftarrow> cbld_abort_clause cbld;
        RETURN (True,False,cdb,cbld,A)
      } else doN {
        e \<leftarrow> cbld_is_empty cbld;
        (cl,cbld) \<leftarrow> cbld_finish_clause cbld;
        cdb \<leftarrow> cdb_insert cid cl cdb;
        RETURN (False,e,cdb,cbld,A)
      }"
      
      
  lemma in_ran_updD: "\<lbrakk>X \<in> ran (m(k \<mapsto> v))\<rbrakk> \<Longrightarrow> X\<in>ran m \<or> X=v"    
    by (auto simp: ran_def split: if_splits)
    
  lemma finish_proof_correct[refine_vcg]: "\<lbrakk> cs_ip_invar cap csip \<rbrakk> 
    \<Longrightarrow> finish_proof cid csip \<le> SPEC (\<lambda>csop. cs_op_invar cap csop \<and> rtranclp checker_trans (cs_ip_\<alpha> csip) (cs_op_\<alpha> csop))"
    unfolding finish_proof_def cdb_insert_def
    apply refine_vcg
    apply clarsimp_all
    
    unfolding cs_ip_invar_def cs_op_invar_def cs_common_invar_def cs_ip_\<alpha>_def cs_op_\<alpha>_def
    apply (clarsimp_all)

    subgoal
      by (auto intro: ct_fail)
      
    subgoal  
      apply (auto dest!: in_ran_updD simp: cbld_\<alpha>_maxlit_bound)
      apply blast
      done
      
    apply (intro conjI impI)      

    subgoal
      by (auto intro: ct_finish_proof_unsat)      

    subgoal
      apply (auto 
        intro: r2_into_rtranclp[of checker_trans, OF ct_finish_proof ct_del_clauses] 
        dest: in_ran_updD)
      done
    done
    
   
  (*
    Start lemma
  *)
  definition start_lemma :: "nat \<Rightarrow> checker_state_out_proof \<Rightarrow> checker_state_build_lemma nres" where
    "start_lemma cap \<equiv> \<lambda>(err,unsat,cdb,cbld,A). doN {
      A \<leftarrow> rpan_clear cap A;
      RETURN (err,A,cbld,cdb)
    }"  

    
  lemma rpa_and_not_C_empty[simp]: "rpa_and_not_C A {} = A" unfolding rpa_and_not_C_def by auto  
    
  lemma start_lemma_correct[refine_vcg]: "\<lbrakk>cs_op_invar cap csop; \<not>csop_is_unsat csop\<rbrakk> \<Longrightarrow>
    start_lemma cap csop \<le> SPEC (\<lambda>csbl. cs_bl_invar cap csbl \<and> checker_trans (cs_op_\<alpha> csop) (cs_bl_\<alpha> csbl))"      
    unfolding start_lemma_def
    apply refine_vcg
    unfolding cs_op_invar_def cs_bl_invar_def cs_common_invar_def
    apply clarsimp_all
    
    unfolding cs_op_\<alpha>_def cs_bl_\<alpha>_def csop_is_unsat_def
    by (auto simp: ct_fail ct_start_lemma)

  (*
    Add literal
  *)  
        
      
  definition add_literal:: "dv_lit \<Rightarrow> checker_state_build_lemma \<Rightarrow> checker_state_build_lemma nres" where
    "add_literal l \<equiv> \<lambda>(err,A,cbld,cdb). do {
      ASSERT (cbld_invar cbld);
      cbld \<leftarrow> cbld_add_lit l cbld;
      A \<leftarrow> rpan_set_checked A (neg_lit l);
      RETURN (err,A,cbld,cdb)
    }"  
    
  (* TODO: Move *)  
  lemma rpa_and_not_C_insert[simp]: "rpa_and_not_C A (insert l C) = (rpa_and_not_C A C)(neg_lit l:=True)"  
    unfolding rpa_and_not_C_def by auto

  lemma ss_range_maxI: "A \<subseteq> {l..h} \<Longrightarrow> A \<subseteq> {l..max h h'}" for A :: "nat set"
    by (auto simp: max_def)
    
    
  lemma add_literal_correct[refine_vcg]: "\<lbrakk> cs_bl_invar cap csbl; cap\<noteq>0 \<rbrakk> \<Longrightarrow> 
    add_literal l csbl \<le> SPEC (\<lambda>csbl'. cs_bl_invar (cap-1) csbl' \<and> checker_trans (cs_bl_\<alpha> csbl) (cs_bl_\<alpha> csbl'))"  
    unfolding add_literal_def
    apply refine_vcg
    unfolding cs_bl_invar_def cs_common_invar_def Let_def
    apply (clarsimp_all)
    apply (all \<open>(intro conjI)?\<close>)
    apply simp_all
    subgoal by (simp add: ss_range_maxI)
    subgoal by blast
    unfolding cs_bl_\<alpha>_def
    by (auto intro: ct_fail ct_add_lit)


  (*
    Start proof
  *)  
        
  definition start_proof:: "checker_state_build_lemma \<Rightarrow> checker_state_in_proof nres" where
    "start_proof \<equiv> \<lambda>(err,A,cbld,cdb). 
      RETURN (err,False,A,cbld,cdb)
    "
    
  lemma start_proof_correct[refine_vcg]: "\<lbrakk>cs_bl_invar cap csbl; 0<cap\<rbrakk> 
    \<Longrightarrow> start_proof csbl \<le> SPEC (\<lambda>csip. cs_ip_invar (cap-1) csip \<and> checker_trans (cs_bl_\<alpha> csbl) (cs_ip_\<alpha> csip))"  
    unfolding start_proof_def
    apply refine_vcg
    unfolding cs_bl_invar_def cs_ip_invar_def Let_def
    apply clarsimp_all
    subgoal
      unfolding cs_common_invar_def
      by linarith
    subgoal
      unfolding cs_bl_\<alpha>_def cs_ip_\<alpha>_def
      by (auto intro: ct_fail ct_start_proof)
    done
    
  (* Formally start proof (change state type), but just set error flag *)  
  definition start_proof_error:: "checker_state_build_lemma \<Rightarrow> checker_state_in_proof nres" where
    "start_proof_error \<equiv> \<lambda>(err,A,cbld,cdb). do {
      RETURN (True,False,A,cbld,cdb)
    }"

  lemma start_proof_error_correct[refine_vcg]: "\<lbrakk>cs_bl_invar cap csbl\<rbrakk> 
    \<Longrightarrow> start_proof_error csbl \<le> SPEC (\<lambda>csip. cs_ip_invar cap csip \<and> checker_trans (cs_bl_\<alpha> csbl) (cs_ip_\<alpha> csip))"  
    unfolding start_proof_error_def
    apply refine_vcg
    unfolding cs_bl_invar_def cs_ip_invar_def Let_def
    apply clarsimp_all
    unfolding cs_bl_\<alpha>_def cs_ip_\<alpha>_def
    by (auto intro: ct_fail)

        
  (* Delete Clause *)  
    
  definition delete_clause:: "nat \<Rightarrow> checker_state_out_proof \<Rightarrow> checker_state_out_proof nres" where
    "delete_clause cid \<equiv> \<lambda>(err,unsat,cdb,cbld,A). doN {
      cdb \<leftarrow> cdb_delete cid cdb;
      RETURN (err,unsat,cdb,cbld,A)
    }"
  
  lemma ran_del_ss: "ran (m(k:=None)) \<subseteq> ran m"  
    by (auto simp: ran_def)
    
  lemma delete_clause_correct[refine_vcg]: "\<lbrakk> cs_op_invar cap csop  \<rbrakk>
    \<Longrightarrow> delete_clause cid csop \<le> SPEC (\<lambda>csop'. cs_op_invar cap csop' \<and> checker_trans (cs_op_\<alpha> csop) (cs_op_\<alpha> csop'))"
    unfolding delete_clause_def cdb_delete_def
    apply refine_vcg
    apply clarsimp_all
    subgoal
      unfolding cs_op_invar_def cs_common_invar_def cs_op_\<alpha>_def
      by (auto dest!: ran_del_ss[THEN set_mp])
      
    subgoal
      unfolding cs_op_\<alpha>_def 
      by (auto intro: ct_fail ct_refl ct_del_clauses dest: ran_del_ss[THEN set_mp])
    done
    
    


  subsection \<open>Combining Checker with LRAT Parser\<close>  

  (* Skip over uids until a 0 has been read. (no longer) used to ignore deletions. *)
  definition skip_to_zero_uids :: "brd_rs \<Rightarrow> brd_rs nres" where
    "skip_to_zero_uids prf\<^sub>0 \<equiv> do {
      (prf,_) \<leftarrow> WHILEIT (\<lambda>(prf,_). brd_rs_invar prf \<and> brd_rs_remsize prf \<le> brd_rs_remsize prf\<^sub>0)
        (\<lambda>(prf,brk). \<not>brd_rs_no_size_left prf \<and> \<not>brk) 
        (\<lambda>(prf,_). do {
          (cid,prf) \<leftarrow> brd_rs_read_signed_id prf;
          RETURN (prf,dest_cid cid=0) 
        })
        (prf\<^sub>0,False);
      RETURN prf
    }"
  
  lemma skip_to_zero_uids_correct[refine_vcg]: "brd_rs_invar prf \<Longrightarrow> 
    skip_to_zero_uids prf \<le> SPEC (\<lambda>prf'. brd_rs_invar prf' \<and> brd_rs_remsize prf' \<le> brd_rs_remsize prf)"
    unfolding skip_to_zero_uids_def
    apply (refine_vcg WHILEIT_rule[where R="measure (brd_rs_remsize o fst)"])
    by auto

    
  definition delete_clauses :: "checker_state_out_proof \<Rightarrow> brd_rs \<Rightarrow> (checker_state_out_proof \<times> brd_rs) nres" where
    "delete_clauses cs prf\<^sub>0 \<equiv> doN {
      (cs,prf,_) \<leftarrow> monadic_WHILEIT (\<lambda>_. True)
        (\<lambda>(cs,prf,brk). doN { ASSERT(brd_rs_invar prf);  RETURN (\<not>brd_rs_no_size_left prf \<and> \<not>brk)}) 
        (\<lambda>(cs,prf,_). do {
          (cid,prf) \<leftarrow> brd_rs_read_signed_id prf;
          if dest_cid cid = 0 then
            RETURN (cs,prf,True) 
          else doN {
            cs \<leftarrow> delete_clause cid cs;
            RETURN (cs,prf,False)
          }
        })
        (cs,prf\<^sub>0,False);
      RETURN (cs,prf)
    }" 
    

  lemma delete_clauses_correct[refine_vcg]: "\<lbrakk> cs_op_invar cap cs; brd_rs_invar prf \<rbrakk> \<Longrightarrow>
    delete_clauses cs prf \<le> SPEC (\<lambda>(cs',prf'). 
        cs_op_invar cap cs' \<and> rtranclp checker_trans (cs_op_\<alpha> cs) (cs_op_\<alpha> cs') 
      \<and> brd_rs_invar prf' \<and> brd_rs_remsize prf' \<le> brd_rs_remsize prf)"
    unfolding delete_clauses_def
    apply (refine_vcg monadic_WHILEIT_strengthen_invar_rule[where 
          Inew="\<lambda>(cs',prf',_). 
              brd_rs_invar prf' \<and> brd_rs_remsize prf' \<le> brd_rs_remsize prf
            \<and> cs_op_invar cap cs' 
            \<and> rtranclp checker_trans (cs_op_\<alpha> cs) (cs_op_\<alpha> cs')"
          and R="measure (\<lambda>(_,prf,_). brd_rs_remsize prf)"
          ] 
    )  
    by auto
    
        
  (*
    Parse and add literals, until terminating zero has been found
  *)    
  abbreviation (input) "err_code_no_term_zero_lit \<equiv> 0x5"  
  definition add_literals_loop :: "checker_state_build_lemma \<Rightarrow> brd_rs \<Rightarrow> (checker_state_in_proof \<times> brd_rs) nres" where
    "add_literals_loop cs prf \<equiv> doN {
      (cs,prf,ctd)\<leftarrow>monadic_WHILEIT (\<lambda>_. True)
        (\<lambda>(cs,prf,ctd). doN { ASSERT(brd_rs_invar prf); RETURN (\<not>brd_rs_no_size_left prf \<and> ctd) })
        (\<lambda>(cs,prf,_). do {
          (l,prf) \<leftarrow> brd_rs_read_ulito prf;
          PARSED_LRAT_LIT l;
          if is_None l then RETURN (cs,prf,False)
          else doN {
            cs \<leftarrow> add_literal (the l) cs;
            RETURN (cs,prf,True)
          }
        })
        (cs,prf,True);
      
      if ctd then doN {
        ERROR err_code_no_term_zero_lit;
        cs\<leftarrow>start_proof_error cs;  
        RETURN (cs,prf)  
      } else doN {  
        cs\<leftarrow>start_proof cs;  
        RETURN (cs,prf)  
      }
    }"
  
  lemma add_literals_loop_correct[refine_vcg]: "\<lbrakk> cs_bl_invar (brd_rs_remsize prf) cs; brd_rs_invar prf \<rbrakk> 
    \<Longrightarrow> add_literals_loop cs prf \<le> SPEC (\<lambda>(cs',prf'). 
          brd_rs_invar prf' 
        \<and> brd_rs_remsize prf' \<le> brd_rs_remsize prf
        \<and> cs_ip_invar (brd_rs_remsize prf') cs' 
        \<and> rtranclp checker_trans (cs_bl_\<alpha> cs) (cs_ip_\<alpha> cs'))"
    unfolding add_literals_loop_def
    
    apply (refine_vcg monadic_WHILEIT_strengthen_invar_rule[where 
          Inew="\<lambda>(cs',prf',ctd). 
              brd_rs_invar prf'
            \<and> brd_rs_remsize prf' \<le> brd_rs_remsize prf
            \<and> cs_bl_invar (if ctd then brd_rs_remsize prf' else Suc (brd_rs_remsize prf')) cs' 
            \<and> rtranclp checker_trans (cs_bl_\<alpha> cs) (cs_bl_\<alpha> cs')"
          and R="measure (\<lambda>(_,prf,_). brd_rs_remsize prf)"
          ] 
    )  
    
    
    apply clarsimp_all
    apply (all \<open>(erule asm_rl[of "cs_bl_invar _ _"] asm_rl[of "checker_invar _ _"])?\<close>)
    apply (auto elim: cs_bl_invar_antimono cs_ip_invar_antimono)
    done
    
  (*
    Parse clause ids and perform proof steps
  *)    
  definition prove_units_loop :: "checker_state_in_proof \<Rightarrow> brd_rs \<Rightarrow> (checker_state_in_proof \<times> brd_rs) nres" where
    "prove_units_loop cs prf \<equiv> doN {
      (cs,prf,_)\<leftarrow>monadic_WHILEIT (\<lambda>_. True) 
        (\<lambda>(cs,prf,brk). doN { ASSERT(brd_rs_invar prf); RETURN (\<not>brd_rs_no_size_left prf \<and> \<not>brk) })
        (\<lambda>(cs,prf,_). do {
          (cid,prf) \<leftarrow> brd_rs_read_signed_id prf;
          PARSED_LRAT_ID cid;
          if dest_cid cid=0 then RETURN (cs,prf,True)
          else doN {
            cs \<leftarrow> proof_step cid cs;
            RETURN (cs,prf,False)
          }
        })
        (cs,prf,False);
        
      RETURN (cs,prf)  
    }"
    
  lemma prove_units_loop_correct[refine_vcg]: "\<lbrakk> brd_rs_invar prf; cs_ip_invar (brd_rs_remsize prf) cs \<rbrakk> 
    \<Longrightarrow> prove_units_loop cs prf \<le> SPEC (\<lambda>(cs',prf'). 
      brd_rs_invar prf'
      \<and> brd_rs_remsize prf' \<le> brd_rs_remsize prf 
      \<and> cs_ip_invar (brd_rs_remsize prf') cs' 
      \<and> rtranclp checker_trans (cs_ip_\<alpha> cs) (cs_ip_\<alpha> cs'))"
    unfolding prove_units_loop_def
    
    apply (refine_vcg monadic_WHILEIT_strengthen_invar_rule[where 
          Inew="\<lambda>(cs',prf',_). 
                  brd_rs_invar prf' 
                \<and> brd_rs_remsize prf'\<le>brd_rs_remsize prf 
                \<and> cs_ip_invar (brd_rs_remsize prf') cs' 
                \<and> rtranclp checker_trans (cs_ip_\<alpha> cs) (cs_ip_\<alpha> cs')"
          and R="measure (\<lambda>(_,prf,_). brd_rs_remsize prf)"
          ] 
    )  
    apply clarsimp_all
    (* Discharge schematics very specifically. Otherwise, we'll get wrong matches on "0<cap" leading to unprovable goals. *)
    apply (all \<open>(erule asm_rl[of "cs_ip_invar _ _"] asm_rl[of "checker_invar _ _"])?\<close>)
    apply (auto elim: cs_ip_invar_antimono)
    done
    

  (* TODO: Move *)
  synth_definition rdmem_it_free [llvm_inline] is [sepref_frame_free_rules]: "MK_FREE rdmem_it_assn \<hole>"
    unfolding rdmem_it_assn_def rdmem_it_assn_raw_def
    by sepref_dbg_side
    

  (*
    Main proof checker loop, integrating LRAT-parser and checker
  *)        
  definition main_checker_loop :: "checker_state_out_proof \<Rightarrow> brd_rs \<Rightarrow> (bool \<times> brd_rs) nres" where
    "main_checker_loop cs prf \<equiv> doN {
      (cs,prf)\<leftarrow>monadic_WHILEIT (\<lambda>_. True) 
        (\<lambda>(cs,prf). doN { ASSERT(brd_rs_invar prf); RETURN (\<not>csop_is_error cs \<and> \<not>csop_is_unsat cs \<and> \<not>brd_rs_no_size_left prf) }) 
        (\<lambda>(cs,prf). doN {
          (c,prf) \<leftarrow> brd_rs_read prf;
          if c=char_a then do { \<comment> \<open>'a' cid lits 0 cids 0 \<close>
            (cid,prf) \<leftarrow> brd_rs_read_signed_id_ndecr prf;
            
            PARSED_LRAT_ADD cid;
            ASSERT(brd_rs_invar prf);
            cs\<leftarrow>start_lemma (brd_rs_remsize prf) cs;
            (cs,prf)\<leftarrow>add_literals_loop cs prf;
            (cs,prf)\<leftarrow>prove_units_loop cs prf;
            cs \<leftarrow> finish_proof cid cs;
            RETURN (cs,prf)
          } else if c=char_d then doN { \<comment> \<open>'d' uids 0 \<close>
            (cs,prf) \<leftarrow> delete_clauses cs prf;
            RETURN (cs,prf)
          } else doN {
            ERROR err_code_syntax_error;
            let cs = csop_set_error cs;
            RETURN (cs,prf)
          }
        
        }) 
        (cs,prf);
        
      RETURN (\<not>csop_is_error cs \<and> csop_is_unsat cs,prf)  
    }"     
    
    
  (* TODO: The next two lemmas are purely technical, b/c clarsimp splits products too early, and 
    thus prevents more conceptual lemmas on csop_set_error *)  
  lemma cs_op_invar_err: "cs_op_invar cap (err,unsat,A,cdb) \<Longrightarrow> cs_op_invar cap (True,unsat,A,cdb)"  
    unfolding cs_op_invar_def by auto
    
  lemma checker_invar_err: "checker_invar F\<^sub>0 (cs_op_\<alpha> (True, unsat,A,cdb))"
    unfolding cs_op_\<alpha>_def by (auto simp: checker_invar.simps)   
    
  lemma cs_op_\<alpha>_err: "cs_op_\<alpha> (True, unsat,A,cdb) = FAIL"  
    unfolding cs_op_\<alpha>_def by auto
    
  lemma csop_unsat_\<alpha>: "\<lbrakk>csop_is_unsat cs; \<not>csop_is_error cs\<rbrakk> \<Longrightarrow> cs_op_\<alpha> cs = UNSAT"  
    unfolding cs_op_\<alpha>_def csop_is_unsat_def csop_is_error_def 
    by (cases cs; auto) 
    
  lemma csop_unsat_imp_unsat: 
    "\<lbrakk>cs_op_invar cap cs; csop_is_unsat cs; \<not>csop_is_error cs; checker_invar F\<^sub>0 (cs_op_\<alpha> cs) \<rbrakk> \<Longrightarrow> \<not>sat F\<^sub>0" 
    unfolding cs_op_\<alpha>_def csop_is_unsat_def csop_is_error_def
    by (cases cs; auto simp: checker_invar.simps) 
    
  lemma main_checker_loop_correct[refine_vcg]: "\<lbrakk> brd_rs_invar prf; cs_op_invar (brd_rs_remsize prf) cs; rtranclp checker_trans (CNF F\<^sub>0) (cs_op_\<alpha> cs) \<rbrakk> 
    \<Longrightarrow> main_checker_loop cs prf \<le> SPEC (\<lambda>(r,prf). brd_rs_invar prf \<and> (r \<longrightarrow> \<not>sat F\<^sub>0))
  "
    unfolding main_checker_loop_def
    unfolding csop_set_error_def
    apply (refine_vcg monadic_WHILEIT_strengthen_invar_rule[where   
          Inew="\<lambda>(cs,prf). brd_rs_invar prf \<and> cs_op_invar (brd_rs_remsize prf) cs \<and> rtranclp checker_trans (CNF F\<^sub>0) (cs_op_\<alpha> cs)"
      and R="measure (\<lambda>(cs,prf). brd_rs_remsize prf)"
    ])
    
    apply (clarsimp_all simp: cs_op_\<alpha>_err csop_unsat_\<alpha>)
    apply (all \<open>(erule asm_rl[of "cs_ip_invar _ _"] asm_rl[of "cs_op_invar _ _"] asm_rl[of "checker_invar _ _"])?\<close>)
    
    apply (auto 
      simp: parsed1_remsize parsed_remsize 
      elim: cs_op_invar_antimono cs_op_invar_error_antimono 
      intro: ct_fail 
      dest: checker_trans_rtrancl_unsatI)
    done    
    

  subsubsection \<open>Combining CNF Parser with Checker\<close>  

  
  (*
    Convert builder state to checker state
  *)  
  abbreviation (input) "info_code_ncid \<equiv> 0x1"  
  abbreviation (input) "info_code_maxlit \<equiv> 0x2"  
  definition builder_finish_building :: "builder_state \<Rightarrow> checker_state_out_proof nres" where
    "builder_finish_building \<equiv> \<lambda>(ncid,cbld,cdb). doN {
      ml \<leftarrow> cbld_get_maxlit cbld;
    
      INFO_cid info_code_ncid ncid;
      INFO_ulit info_code_maxlit ml;
      
      let A = rpan_empty ml 0;  
      
      RETURN (False, False, cdb, cbld, A)
    }"
    
  lemma builder_finish_building_correct[refine_vcg]: "\<lbrakk> bs_invar cap\<^sub>1 cap\<^sub>2 bs; bs_\<alpha>C bs = {} \<rbrakk> \<Longrightarrow>
    builder_finish_building bs \<le> SPEC (\<lambda>csop. cs_op_invar cap\<^sub>1 csop \<and> cs_op_\<alpha> csop = CNF (bs_\<alpha>F bs))"  
    unfolding builder_finish_building_def
    apply refine_vcg
    subgoal
      unfolding bs_invar_def cbld_invar_def
      by auto
    subgoal
      unfolding bs_invar_def cs_op_invar_def cs_common_invar_def bs_\<alpha>C_def
      apply (auto simp: maxlit_vdom_def) 
      by (metis atLeastAtMost_iff basic_trans_rules(31) image_eqI mem_simps(9) ulit_of_inv(1) ulit_of_inv(2))
    subgoal  
      unfolding cs_op_invar_def cs_op_\<alpha>_def bs_invar_def bs_\<alpha>F_def
      by auto
    done

  (*
    Read a DIMACS file and initialize checker state
  *)  
  definition read_dimacs_cs :: "input \<Rightarrow> (checker_state_out_proof \<times> nat) nres"
  where "read_dimacs_cs dimacs_input \<equiv> doN {
    (bs,cap\<^sub>1,err) \<leftarrow> read_dimacs_file dimacs_input;
    
    cs \<leftarrow> builder_finish_building bs;
    
    if err then RETURN (csop_set_error cs,cap\<^sub>1)
    else RETURN (cs,cap\<^sub>1)
  }"
    
  
  lemma read_dimacs_cs_correct[refine_vcg]: " 
    read_dimacs_cs dimacs_input \<le> SPEC (\<lambda>(cs,cap\<^sub>1). 
      cs_op_invar cap\<^sub>1 cs 
    \<and> (\<not>csop_is_error cs \<longrightarrow> (\<exists>fml. (i_data dimacs_input, fml) \<in> gM_rel cnf_dimacs \<and> cs_op_\<alpha> cs = CNF fml)))"
    unfolding read_dimacs_cs_def
    apply (refine_vcg)
    apply simp_all
    (* Unfortunately, in the below proof, there's an ughly interplay between Isabelle's clarify splitting tuple variables,
      and the re-orientation of equations such as "csop_set_error xa = x1". This required some manual work \<dots> *)
    apply (clarsimp; assumption)
    apply (hypsubst; simp; fail) 
    apply (hypsubst; simp; fail)
    subgoal by simp
    subgoal by blast
    done
  
  (* For paper *)
  lemma " 
    read_dimacs_cs dimacs_input \<le> SPEC (\<lambda>(cs,cap\<^sub>1). 
      cs_op_invar cap\<^sub>1 cs 
    \<and> (cs_op_\<alpha> cs = FAIL \<or> (\<exists>fml. (i_data dimacs_input, fml) \<in> gM_rel cnf_dimacs \<and> cs_op_\<alpha> cs = CNF fml)))"
    apply (refine_vcg)
    apply simp_all
    apply auto
    done
    
    
  definition [simp]: "ll_dbg_tag_parsed_cnf (err::8 word) \<equiv> RETURN ()"  
  lemma [refine_vcg]: "ll_dbg_tag_parsed_cnf x \<le> SPEC (\<lambda>_. True)" by simp 
  sepref_register ll_dbg_tag_parsed_cnf
  sepref_def ll_dbg_tag_parsed_cnf_impl is "ll_dbg_tag_parsed_cnf" :: "word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn"
    unfolding ll_dbg_tag_parsed_cnf_def
    by sepref
      
    
  (*
    Read DIMACS file and run checker
  *)    
  definition read_check_lrat :: "input \<Rightarrow> bool nres" where 
  "read_check_lrat cnf \<equiv> doN {
    (cs,cap) \<leftarrow> read_dimacs_cs cnf;
    if csop_is_error cs then doN {
      ll_dbg_tag_parsed_cnf 0;
      RETURN False
    } else VCG_STOP (doN { 
      let prf = brd_rs_new cap;
      ll_dbg_tag_parsed_cnf 1;
      (res,prf) \<leftarrow> main_checker_loop cs prf;
      RETURN res
    })
  }"
    
  theorem read_check_lrat_correct[refine_vcg]: "read_check_lrat cnf \<le> SPEC (\<lambda>r. 
    r \<longrightarrow> (\<exists>F. (i_data cnf, F) \<in> gM_rel cnf_dimacs \<and> \<not>sat F))"
    unfolding read_check_lrat_def
    apply refine_vcg
    
    (* We need to instantiate existentials at this point, 
      before the VCG introduces more schematic variables, so we have used the 
      VCG_STOP tag to stop the VCG.
    *)
    
    apply clarsimp_all
    
    apply (rule VCG_STOP) (* Resume VCG *)
    
    apply refine_vcg
    by auto
    
  (*  
  (* For Paper *)  
  lemma builder_finish_building_no_err: "builder_finish_building bs \<le> SPEC (\<lambda>cs. \<not>csop_is_error cs)"
    unfolding builder_finish_building_def csop_is_error_def
    apply refine_vcg
    by simp
    
  
  (* Definition of read_check_lrat as presented in paper *)
  lemma "read_check_lrat cnf prf = (
    if i_size cnf + i_size prf \<ge> max_snat size_t_len - 1 then RETURN False
    else do {
      ASSERT (Suc (i_size cnf + i_size prf) \<le> max_snat size_t_len - Suc 0);
      (bs, err) \<leftarrow> read_dimacs_file (i_size prf) cnf;
      cs \<leftarrow> builder_finish_building bs;
      if err then RETURN False else main_checker_loop cs prf
    }
  )"
    unfolding read_check_lrat_def read_dimacs_cs_def VCG_STOP_def

    apply (split if_split; intro conjI impI; simp)  
    using builder_finish_building_no_err
    unfolding csop_set_error_def csop_is_error_def
      
    apply (simp add: pw_eq_iff pw_le_iff)
    apply (simp add:  refine_pw_simps)
    apply safe
    apply simp_all
    apply metis+
    done
  *)  
    
    
  subsection \<open>Refinement to LLVM\<close>  
    
  (* Implementation: Checker *)  

  (*    
  (* This is intermingled with clause database internals.
    Implement cdb_lookup_idx and cdb_get_db_lit as interface operations for more smooth refinement!
  *)
  term cdb_check_uot3
  
  sepref_register cdb_check_uot3
  
  sepref_def cdb_check_uot_impl is "uncurry2 cdb_check_uot3" :: "rpan_assn\<^sup>k *\<^sub>a cdb_assn\<^sup>k *\<^sub>a cid_assn\<^sup>k \<rightarrow>\<^sub>a ulito_assn \<times>\<^sub>a bool1_assn"
    unfolding cdb_check_uot3_def
    by sepref  
    
  *)  
    
  definition "cs_ip_assn = bool1_assn \<times>\<^sub>a bool1_assn \<times>\<^sub>a rpan_assn \<times>\<^sub>a cbld_assn \<times>\<^sub>a cdb_assn"  
  definition "cs_op_assn = bool1_assn \<times>\<^sub>a bool1_assn \<times>\<^sub>a cdb_assn \<times>\<^sub>a cbld_assn \<times>\<^sub>a rpan_assn"  
    
  definition "cs_bl_assn \<equiv> bool1_assn \<times>\<^sub>a rpan_assn  \<times>\<^sub>a cbld_assn \<times>\<^sub>a cdb_assn"
  
  
  sepref_register proof_step csop_set_error csop_is_error csop_is_unsat finish_proof start_lemma
    add_literal start_proof start_proof_error delete_clause
  
  term proof_step
  sepref_def proof_step_impl is "uncurry proof_step" :: "cid_assn\<^sup>k *\<^sub>a cs_ip_assn\<^sup>d \<rightarrow>\<^sub>a cs_ip_assn"  
    unfolding proof_step_def cs_ip_assn_def
    by sepref
  
  sepref_def csop_set_error_impl [llvm_inline] is "RETURN o csop_set_error" :: "cs_op_assn\<^sup>d \<rightarrow>\<^sub>a cs_op_assn" 
    unfolding csop_set_error_def cs_op_assn_def
    by sepref

  sepref_def csop_is_error_impl [llvm_inline] is "RETURN o csop_is_error" :: "cs_op_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn" 
    unfolding csop_is_error_def cs_op_assn_def
    by sepref

  sepref_def csop_is_unsat_impl [llvm_inline] is "RETURN o csop_is_unsat" :: "cs_op_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn" 
    unfolding csop_is_unsat_def cs_op_assn_def
    by sepref

  sepref_def finish_proof_impl is "uncurry finish_proof" :: "cid_assn\<^sup>k *\<^sub>a cs_ip_assn\<^sup>d \<rightarrow>\<^sub>a cs_op_assn"  
    unfolding finish_proof_def cs_ip_assn_def cs_op_assn_def
    by sepref
    
  
  sepref_def start_lemma_impl is "uncurry start_lemma" :: "size_assn\<^sup>k *\<^sub>a cs_op_assn\<^sup>d \<rightarrow>\<^sub>a cs_bl_assn"  
    unfolding start_lemma_def cs_op_assn_def cs_bl_assn_def
    by sepref
    
  sepref_def add_literal_impl is "uncurry add_literal" :: "ulit_assn\<^sup>k *\<^sub>a cs_bl_assn\<^sup>d \<rightarrow>\<^sub>a cs_bl_assn"  
    unfolding add_literal_def cs_bl_assn_def
    by sepref
  
  sepref_def start_proof_impl is "start_proof" :: "cs_bl_assn\<^sup>d \<rightarrow>\<^sub>a cs_ip_assn"
    unfolding start_proof_def cs_bl_assn_def cs_ip_assn_def
    by sepref 
    
  sepref_def start_proof_error_impl is "start_proof_error" :: "cs_bl_assn\<^sup>d \<rightarrow>\<^sub>a cs_ip_assn"
    unfolding start_proof_error_def cs_bl_assn_def cs_ip_assn_def
    by sepref 
      
  sepref_def delete_clause_impl is "uncurry delete_clause" :: "cid_assn\<^sup>k *\<^sub>a cs_op_assn\<^sup>d \<rightarrow>\<^sub>a cs_op_assn"
    unfolding delete_clause_def cs_op_assn_def
    by sepref 

  sepref_register skip_to_zero_uids delete_clauses add_literals_loop prove_units_loop main_checker_loop
    
  sepref_def skip_to_zero_uids_impl is "skip_to_zero_uids" :: "brd_rs_assn\<^sup>d \<rightarrow>\<^sub>a brd_rs_assn"
    unfolding skip_to_zero_uids_def
    apply (annot_snat_const size_T)
    by sepref    

  sepref_def delete_clauses_impl is "uncurry delete_clauses" :: "cs_op_assn\<^sup>d *\<^sub>a brd_rs_assn\<^sup>d \<rightarrow>\<^sub>a cs_op_assn \<times>\<^sub>a brd_rs_assn"
    unfolding delete_clauses_def
    apply (annot_snat_const size_T)
    by sepref    
        
  sepref_def add_literals_loop_impl is "uncurry add_literals_loop" 
    :: "cs_bl_assn\<^sup>d *\<^sub>a brd_rs_assn\<^sup>d \<rightarrow>\<^sub>a cs_ip_assn \<times>\<^sub>a brd_rs_assn"  
    unfolding add_literals_loop_def
    by sepref
      
  sepref_def prove_units_loop_impl is "uncurry prove_units_loop" 
    :: "cs_ip_assn\<^sup>d *\<^sub>a brd_rs_assn\<^sup>d \<rightarrow>\<^sub>a cs_ip_assn \<times>\<^sub>a brd_rs_assn"  
    unfolding prove_units_loop_def
    apply (annot_snat_const size_T)
    by sepref
    

  synth_definition nadf_free [llvm_code] is [sepref_frame_free_rules]: "MK_FREE (cs_op_assn) \<hole>"
    unfolding cs_op_assn_def 
    by sepref_dbg_side (* TODO: Use proper tactic *)
    
    
  sepref_def main_checker_loop_impl is "uncurry main_checker_loop" :: "cs_op_assn\<^sup>d *\<^sub>a brd_rs_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a brd_rs_assn"
    unfolding main_checker_loop_def
    supply [[goals_limit = 1]]
    by sepref
    
    
    
  (* Implementation: Builder *)    
    
  sepref_register 
    builder_finish_building 
    read_dimacs_cs
   
  sepref_def builder_finish_building_impl is builder_finish_building :: "bs_assn\<^sup>d \<rightarrow>\<^sub>a cs_op_assn"
    unfolding builder_finish_building_def bs_assn_def cs_op_assn_def
    apply (annot_snat_const size_T)
    by sepref
    
  sepref_def read_dimacs_cs_impl is "read_dimacs_cs" 
    :: "rdmem_inp_assn\<^sup>k \<rightarrow>\<^sub>a cs_op_assn \<times>\<^sub>a size_assn"
    unfolding read_dimacs_cs_def
    by sepref
    

  sepref_register read_check_lrat  

  sepref_def read_check_lrat_impl is "read_check_lrat" 
    :: "rdmem_inp_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding read_check_lrat_def VCG_STOP_def
    by sepref

    
  (* TODO: Move *)
  definition "make_input_from_array_and_size (xs::8 word list) n \<equiv> doN {
    ASSERT (n = length xs);
    RETURN (INPUT xs)
  }"

  lemma make_input_from_array_and_size_correct[refine_vcg]: 
    "n = length xs \<Longrightarrow> make_input_from_array_and_size xs n \<le> SPEC (\<lambda>r. i_data r = xs)"
    unfolding make_input_from_array_and_size_def
    apply refine_vcg
    by auto
  
  definition mk_rdmem_inp :: "8 word list \<Rightarrow> nat \<Rightarrow> rdmem_inp nres" where "mk_rdmem_inp xs n \<equiv> doN {
    ASSERT (length xs = n);
    RETURN (xs,n)
  }"

  definition rdmem_data :: "rdmem_inp \<Rightarrow> 8 word list" where "rdmem_data \<equiv> \<lambda>(xs,n). xs"
  
  lemma mk_rdmem_inp_refine: "(mk_rdmem_inp,make_input_from_array_and_size) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>rdmem_inp_rel\<rangle>nres_rel"
    unfolding mk_rdmem_inp_def make_input_from_array_and_size_def
    apply refine_vcg
    unfolding rdmem_inp_rel_def in_br_conv
    by auto

  lemma rdmem_data_refine: "(rdmem_data, i_data) \<in> rdmem_inp_rel \<rightarrow> Id" 
    unfolding rdmem_data_def rdmem_inp_rel_def
    by (auto simp: in_br_conv)
    
  sepref_def mk_rdmem_inp_impl is "uncurry mk_rdmem_inp" 
    :: "[\<lambda>_. True]\<^sub>c (array_slice_assn id_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> rdmem_inp_assn_raw [\<lambda>(p,_) (p',_). p'=p]\<^sub>c"  
    unfolding mk_rdmem_inp_def rdmem_inp_assn_raw_def
    by sepref  

  sepref_def rdmem_data_impl is "RETURN o rdmem_data" :: "[\<lambda>_. True]\<^sub>c rdmem_inp_assn_raw\<^sup>d \<rightarrow> array_slice_assn id_assn [\<lambda>(p,_) p'. p'=p]\<^sub>c"
    unfolding rdmem_data_def rdmem_inp_assn_raw_def
    by sepref  
    
    
    
  sepref_register make_input_from_array_and_size
  context
    notes [fcomp_norm_unfold] = rdmem_inp_assn_def[symmetric] 
  begin
    lemmas [sepref_fr_rules] = mk_rdmem_inp_impl.refine[FCOMP mk_rdmem_inp_refine]
    lemmas [sepref_fr_rules] = rdmem_data_impl.refine[FCOMP rdmem_data_refine]
  end  
    
  
  definition "read_check_lrat_wrapper cnfp cnf_size \<equiv> doN {
    cnf \<leftarrow> make_input_from_array_and_size cnfp cnf_size;
    
    res \<leftarrow> read_check_lrat cnf;
    
    let cnfp' = i_data cnf;
    
    unborrow cnfp' cnfp;
    
    if res then RETURN 1 else RETURN 0
  }"
    
  definition lrat_checker_spec :: "8 word list \<Rightarrow> nat \<Rightarrow> nat nres" where
    "lrat_checker_spec cnf cnf_size \<equiv> doN {
      ASSERT(cnf_size = length cnf);
      SPEC (\<lambda>r::nat. r\<noteq>0 \<longrightarrow> ( (\<exists>F. (cnf,F)\<in>gM_rel cnf_dimacs \<and> \<not>sat F)))
    }"
  
  lemma read_check_lrat_wrapper_refine: "(read_check_lrat_wrapper, lrat_checker_spec) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    unfolding read_check_lrat_wrapper_def lrat_checker_spec_def
    apply refine_vcg
    by auto
    
  sepref_def lrat_checker is "uncurry read_check_lrat_wrapper" 
    :: "(array_slice_assn id_assn)\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a (char_assn)"  
    unfolding read_check_lrat_wrapper_def
    apply (annot_unat_const char_T)
    by sepref

  theorem read_check_lrat_wrapper_correct: "(uncurry lrat_checker, uncurry lrat_checker_spec)
    \<in>   (IICF_Array.array_slice_assn (word_assn' char_T))\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn' char_T"
    using lrat_checker.refine[FCOMP read_check_lrat_wrapper_refine]  
    .  
  
  (* Alternative definition of lrat_checker, as presented in paper. *)  
  lemma "lrat_checker p n = do\<^sub>M {
           r \<leftarrow> read_check_lrat_impl (p,n);
           llc_if r (return\<^sub>M 1) (return\<^sub>M 0)
         }"
    unfolding lrat_checker_def mk_rdmem_inp_impl_def rdmem_data_impl_def
    by simp
         
    
  subsection \<open>Generation of LLVM and Correctness Theorem\<close>  
    
  export_llvm lrat_checker is "uint8_t lrat_checker(uint8_t *, int64_t)"  
    file "../code/lrat_isa_export.ll"
              

  (* Low-level correctness theorem as Hoare-Triple *)    
  theorem lrat_checker_correct: "llvm_htriple 
    (raw_array_slice_assn cnf cnf_ptr \<and>* size_assn cnf_size cnf_sizei  
      \<and>* \<up>(cnf_size=length cnf))
      (lrat_checker cnf_ptr cnf_sizei)
    (\<lambda>r. raw_array_slice_assn cnf cnf_ptr \<and>* size_assn cnf_size cnf_sizei  
      \<and>* \<up>(r\<noteq>0 \<longrightarrow> (\<exists>F. (cnf,F)\<in>gM_rel cnf_dimacs \<and> \<not>sat F)))"
      
    apply (rule htriple_pure_preI)
    apply vcg_prepare_external
  proof -
    have AUX1: "array_slice_assn id_assn = raw_array_slice_assn"
      unfolding array_slice_assn_def by simp
  
    have [simp]: "nofail (lrat_checker_spec cnf (length cnf))"  
      unfolding lrat_checker_spec_def by simp
      
    assume [simp]: "cnf_size = length cnf"
      
    have AUX2: "Refine_Basic.RETURN x \<le> lrat_checker_spec cnf (length cnf) 
      \<longleftrightarrow> ((x\<noteq>0 \<longrightarrow> (\<exists>F. (cnf, F) \<in> gM_rel cnf_dimacs \<and> \<not> sat F)))" for x
      unfolding lrat_checker_spec_def
      by simp
    
    note T1[vcg_rules] = read_check_lrat_wrapper_correct[
                THEN hfrefD, THEN hn_refineD, 
                of "(cnf,length cnf)" "(cnf_ptr,cnf_sizei)", 
                unfolded AUX1, simplified]

    thm unat.rel_def                
    have AUX3: "unat_assn x r = \<up>(x = unat r)" for x and r :: "8 word"
      by (auto simp: unat_rel_def unat.rel_def in_br_conv pure_def)
                
    have AUX4: "0<unat r \<longleftrightarrow> r\<noteq>0" for r :: "8 word" 
      by (simp add: unat_gt_0)
      
    note [dest] = AUX2[THEN iffD1, rule_format]  (* TODO/FIXME: Using AUX2 as simp triggers some strange interaction with solver preparing goal to be solved by auto! (VCG_External_Solving.prepare_subgoal_tac) *)
      
    note [simp] = AUX3 AUX4
    show ?thesis by vcg
  qed      
      
  (* Meaning of size_assn *)      
  (* Unsigned interpretation must be < 2^(n-1) *)  
  lemma "size_assn n w = \<up>(n = unat w \<and> unat w < 2^(size_t_len-1))"
    unfolding snat_rel_def snat.rel_def pure_def in_br_conv snat_invar_alt
    by (auto simp: snat_eq_unat_aux1)
  (* Signed interpretation must be \<ge>0 *)
  lemma "size_assn n w = \<up>(n = nat (sint w) \<and> sint w \<ge> 0)"
    unfolding snat_rel_def snat.rel_def pure_def in_br_conv snat_invar_def
    by (auto simp: word_msb_sint snat_def)
  
  
  
    
(*
  TODO:
    If CNF contains empty clause, no lrat proof required?

*)    
    
    
end

