section \<open>Clause Database\<close>  
theory DS_Clause_Database
imports 
  LRAT_Sepref_Base
  DS_Clause_Builder
begin
    
  subsection \<open>Refinement Relation\<close>    
      
  (* Now, we implement the clause database by a list of zclauses and its length *)  
  
  type_synonym cdb = "nat \<rightharpoonup> dv_clause"
  type_synonym cdb_aux = "nat \<times> dv_clause option list"
  
  definition cdb_invar :: "cdb_aux \<Rightarrow> bool" where
    "cdb_invar \<equiv> \<lambda>(l,cl). l = length cl \<and> l>0 \<and> (\<forall>c. Some c \<in> set cl \<longrightarrow> finite c)"
    
  definition cdb_aux_\<alpha> :: "cdb_aux \<Rightarrow> cdb" where
    "cdb_aux_\<alpha> \<equiv> \<lambda>(l,cl) i. if i<length cl then cl!i else None"
  
  
  definition "cdb_aux_assn \<equiv> size_assn \<times>\<^sub>a woarray_assn zcl.option_assn"
  
  definition "cdb_assn \<equiv> hr_comp cdb_aux_assn (br cdb_aux_\<alpha> cdb_invar)"
  
  lemmas [fcomp_norm_unfold] = cdb_assn_def[symmetric]
    
        
  subsection \<open>Operations\<close>  
  subsubsection \<open>Empty\<close>  
  definition cdb_empty :: cdb where "cdb_empty \<equiv> Map.empty"
  lemma cdb_fold_custom_empty: "Map.empty = cdb_empty" unfolding cdb_empty_def by auto
  
    
  definition cdb_aux_empty :: cdb_aux where "cdb_aux_empty \<equiv> (16,replicate 16 None)"
  
  lemma cdb_aux_empty_refine: "(cdb_aux_empty, cdb_empty) \<in> br cdb_aux_\<alpha> cdb_invar"
    unfolding cdb_empty_def cdb_aux_empty_def cdb_invar_def cdb_aux_\<alpha>_def
    by (auto simp: fun_eq_iff nth_Cons' in_br_conv)
  
  
  sepref_register cdb_empty
  sepref_def cdb_empty_impl is "uncurry0 (RETURN cdb_aux_empty)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a cdb_aux_assn"
    unfolding cdb_aux_empty_def cdb_aux_assn_def
    apply (annot_snat_const size_T)
    unfolding woarray_fold_custom_replicate
    by sepref
    
  lemmas cdb_empty_hnr[sepref_fr_rules] = cdb_empty_impl.refine[FCOMP cdb_aux_empty_refine]

    
    
  subsubsection \<open>Insert\<close>  
  definition cdb_insert :: "nat \<Rightarrow> dv_clause \<Rightarrow> cdb \<Rightarrow> cdb nres" where [simp]: "cdb_insert cid cl cdb \<equiv> RETURN (cdb(cid\<mapsto>cl))"
    
        
  definition cdb_aux_insert :: "nat \<Rightarrow> dv_clause \<Rightarrow> cdb_aux \<Rightarrow> cdb_aux nres" where
    "cdb_aux_insert \<equiv> \<lambda>i c (l,css). doN {
      ASSUME (finite c);
      let c = Some c;
      
      let i = dest_cid i;
      
      (l,css) \<leftarrow> wo_ensure_capacity None l css i;
      
      (_,css) \<leftarrow> mop_wo_exchange css i c;
      
      RETURN (l,css)
    }"
  
  lemma cdb_aux_insert_refine: "(cdb_aux_insert, cdb_insert) \<in> nat_rel \<rightarrow> Id \<rightarrow> br cdb_aux_\<alpha> cdb_invar \<rightarrow> \<langle>br cdb_aux_\<alpha> cdb_invar\<rangle>nres_rel"  
    unfolding cdb_aux_insert_def
    apply clarsimp
    apply refine_vcg
    unfolding cdb_invar_def cdb_aux_\<alpha>_def br_def
    subgoal by (auto)
    subgoal by (auto)
    subgoal
      apply (auto simp: in_set_conv_nth nth_list_update elim!: in_set_upd_cases)
      by (metis atLeastLessThan_iff leI option.simps(3) zero_order(1))
    done

  sepref_register cdb_insert 
    
  sepref_def cdb_insert_impl is "uncurry2 cdb_aux_insert" :: "cid_assn\<^sup>k *\<^sub>a zcl_assn\<^sup>d *\<^sub>a cdb_aux_assn\<^sup>d \<rightarrow>\<^sub>a cdb_aux_assn"
    unfolding cdb_aux_insert_def cdb_aux_assn_def
    by sepref
    
  
  lemmas cdb_insert_hnr[sepref_fr_rules] = cdb_insert_impl.refine[FCOMP cdb_aux_insert_refine]
      
  subsubsection \<open>Delete\<close>  
  definition cdb_delete :: "nat \<Rightarrow> cdb \<Rightarrow> cdb nres" where [simp]: "cdb_delete cid cdb \<equiv> RETURN (cdb(cid:=None))"
  
  definition cdb_aux_delete :: "nat \<Rightarrow> cdb_aux \<Rightarrow> cdb_aux nres" where
    "cdb_aux_delete \<equiv> \<lambda>cid (l,css). doN {
      let cid = dest_cid cid;
      
      if cid<l then doN {
        (_,css) \<leftarrow> mop_wo_exchange css cid None;
        RETURN (l,css)
      } else
        RETURN (l,css)
    
    }"

  lemma cdb_aux_delete_refine: "(cdb_aux_delete, cdb_delete) \<in> nat_rel \<rightarrow> br cdb_aux_\<alpha> cdb_invar \<rightarrow> \<langle>br cdb_aux_\<alpha> cdb_invar\<rangle>nres_rel"
    unfolding cdb_aux_delete_def cdb_delete_def
    apply clarsimp
    apply refine_vcg
    unfolding cdb_invar_def cdb_aux_\<alpha>_def br_def
    apply (auto elim: in_set_upd_cases)
    done
    
  sepref_register cdb_delete
    
  sepref_def cdb_delete_impl is "uncurry cdb_aux_delete" :: "cid_assn\<^sup>k *\<^sub>a cdb_aux_assn\<^sup>d \<rightarrow>\<^sub>a cdb_aux_assn"
    unfolding cdb_aux_delete_def cdb_aux_assn_def
    by sepref
  
  lemmas cdb_delete_hnr[sepref_fr_rules] = cdb_delete_impl.refine[FCOMP cdb_aux_delete_refine]
      
  
  subsubsection \<open>Contains\<close>
  definition cdb_contains :: "nat \<Rightarrow> cdb \<Rightarrow> bool nres" 
    where [simp]: "cdb_contains cid cdb \<equiv> RETURN (cid\<in>dom cdb)"
  
    
  definition cdb_aux_contains :: "nat \<Rightarrow> cdb_aux \<Rightarrow> bool nres" where "cdb_aux_contains \<equiv> \<lambda>i (l,css). doN {
    let i = dest_cid i;
    if i<l then doN {
      css' \<leftarrow> mop_to_eo_conv css;
      r \<leftarrow> eo_with (\<lambda>cs. RETURN (\<not>is_None cs)) css' i;
      css' \<leftarrow> mop_to_wo_conv css';
      unborrow css' css;
      RETURN r
    } else RETURN False
  }"
  
  
  lemma cdb_aux_contains_refine: "(cdb_aux_contains,cdb_contains) \<in> nat_rel \<rightarrow> br cdb_aux_\<alpha> cdb_invar \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
    unfolding cdb_aux_contains_def mop_to_eo_conv_def mop_to_wo_conv_def eo_with_def
    apply (intro fun_relI nres_relI)
    apply simp
    apply refine_vcg
    unfolding cdb_invar_def cdb_aux_\<alpha>_def br_def
    by auto
  
  sepref_register cdb_contains
  
  sepref_def cdb_contains_impl is "uncurry cdb_aux_contains" :: "cid_assn\<^sup>k *\<^sub>a cdb_aux_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding cdb_aux_contains_def cdb_aux_assn_def
    by sepref
  
  lemmas cdb_contains_hnr[sepref_fr_rules] = cdb_contains_impl.refine[FCOMP cdb_aux_contains_refine]
  
    
  subsubsection \<open>Free\<close>

  definition "cdb_free \<equiv> \<lambda>cdb. doN { ASSERT (cdb_invar cdb); let (l,css) = cdb; mop_woarray_free l css }"
  
  lemma cdb_free_refine: "(cdb_free,mop_free) \<in> br cdb_aux_\<alpha> cdb_invar \<rightarrow> \<langle>unit_rel\<rangle>nres_rel"
    unfolding cdb_free_def mop_free_def
    apply refine_vcg
    unfolding br_def cdb_invar_def
    by auto
    
    
  sepref_definition cdb_free_impl [llvm_code] is "cdb_free" :: "cdb_aux_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn"  
    unfolding cdb_aux_assn_def cdb_free_def
    by sepref
    
  lemmas cdb_assn_free[sepref_frame_free_rules] = MK_FREE_mopI[OF cdb_free_impl.refine[FCOMP cdb_free_refine]]
    

  subsubsection \<open>Iteration over Clause\<close>    

  locale clause_iteration_setup = 
    fixes ci :: "'pi::llvm_rep \<Rightarrow> 'si::llvm_rep \<Rightarrow> 1 word llM"
    and c :: "'p \<Rightarrow> 's \<Rightarrow> bool"
    and fi :: "'pi \<Rightarrow> lit_size_t word \<Rightarrow> 'si \<Rightarrow> 'si llM"
    and f :: "'p \<Rightarrow> dv_lit \<Rightarrow> 's \<Rightarrow> 's nres"
    fixes P :: "'p \<Rightarrow> 'pi \<Rightarrow> assn" 
    and S :: "'s \<Rightarrow> 'si \<Rightarrow> assn"
    assumes cond_refine: "(uncurry ci,uncurry (RETURN oo c))\<in>P\<^sup>k *\<^sub>a S\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    assumes body_refine: "(uncurry2 fi,uncurry2 f)\<in>P\<^sup>k *\<^sub>a ulit_assn\<^sup>k *\<^sub>a S\<^sup>d \<rightarrow>\<^sub>a S"
  begin
  
    lemmas cb_refines = cond_refine body_refine
  
  
    definition "zcl_fold_aux2 xs p s \<equiv> zcl_fold xs (c p) (f p) s"
    definition "foreach_lit_in_clause cl p s \<equiv> FOREACHcd cl (c p) (f p) s"
    
    lemma zcl_fold_aux2_refine: "(zcl_fold_aux2,PR_CONST foreach_lit_in_clause) \<in> br zcl_\<alpha> zcl_invar \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
      apply (intro fun_relI nres_relI; clarsimp)
      subgoal for xs cl p s 
        unfolding zcl_fold_aux2_def foreach_lit_in_clause_def
        apply (rule order_trans)
        apply (rule zcl_fold_foreach_refine[of xs cl s s Id "c p" "c p" "f p" "f p"])
        by auto
      done  
    
    sepref_register foreach_lit_in_clause  
    
  
    context
      notes [sepref_fr_rules] = cb_refines
      notes [[sepref_register_adhoc c f]]
    begin
    
    sepref_definition zcl_fold_impl_aux is "uncurry2 zcl_fold_aux2" :: "zcl_aux_assn\<^sup>k *\<^sub>a P\<^sup>k *\<^sub>a S\<^sup>d \<rightarrow>\<^sub>a S"
      unfolding zcl_fold_aux2_def zcl_fold_def zcl_fold_aux_def
      apply (annot_snat_const size_T)
      by sepref
    
    end
      
    lemmas zcl_fold_impl_aux_hnr = zcl_fold_impl_aux.refine[FCOMP zcl_fold_aux2_refine]
  
    concrete_definition (in -) zcl_fold_impl [llvm_code] is clause_iteration_setup.zcl_fold_impl_aux_def
    
    lemma foreach_lit_in_clause_hnr[sepref_fr_rules]: "(uncurry2 (zcl_fold_impl ci fi), uncurry2 (PR_CONST foreach_lit_in_clause)) \<in> zcl_assn\<^sup>k *\<^sub>a P\<^sup>k *\<^sub>a S\<^sup>d \<rightarrow>\<^sub>a S"
      using zcl_fold_impl_aux_hnr[unfolded zcl_fold_impl.refine[OF clause_iteration_setup_axioms]]
      .
    
    
    definition cdb_iterate_clause :: "cdb \<Rightarrow> nat \<Rightarrow> 'p \<Rightarrow> 's \<Rightarrow> 's nres"
    where "cdb_iterate_clause db i p s \<equiv> doN {
      ASSERT (i\<in>dom db);
      ASSUME (finite (the (db i)));
      FOREACHcd (the (db i)) (c p) (f p) s
    }"
      
    definition cdb_iterate_clause_aux :: "cdb_aux \<Rightarrow> nat \<Rightarrow> 'p \<Rightarrow> 's \<Rightarrow> 's nres"
    where "cdb_iterate_clause_aux \<equiv> \<lambda>(l,css) i p s. doN {
      css' \<leftarrow> mop_to_eo_conv css;
    
      let i = dest_cid i;
      
      r \<leftarrow> eo_with (\<lambda>cl. doN {
        ASSERT (cl\<noteq>None);
        let cl' = the cl;
        r \<leftarrow> foreach_lit_in_clause cl' p s;
        let cl' = Some cl';
        let _ = unborrow' cl' cl;
        RETURN r
      }) css' i;
      
      css' \<leftarrow> mop_to_wo_conv css';
    
      unborrow css' css;
      
      RETURN r
    }"  
    
    
    lemma cdb_iterate_clause_aux_refine: "(cdb_iterate_clause_aux, PR_CONST cdb_iterate_clause) \<in> br cdb_aux_\<alpha> cdb_invar \<rightarrow> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
      unfolding cdb_iterate_clause_def cdb_iterate_clause_aux_def eo_with_def unborrow_def foreach_lit_in_clause_def
      apply simp
      apply refine_rcg
      unfolding cdb_aux_\<alpha>_def cdb_invar_def br_def
      apply (auto 0 3 split: if_splits simp: in_set_conv_nth) 
      by metis
      
    
    sepref_register cdb_iterate_clause
    
    sepref_definition cdb_iterate_clause_aux_impl is "uncurry3 cdb_iterate_clause_aux" :: "cdb_aux_assn\<^sup>k *\<^sub>a cid_assn\<^sup>k *\<^sub>a P\<^sup>k *\<^sub>a S\<^sup>d \<rightarrow>\<^sub>a S"
      unfolding cdb_iterate_clause_aux_def cdb_aux_assn_def
      by sepref
        
        
    lemmas cdb_iterate_clause_aux_hnr = cdb_iterate_clause_aux_impl.refine[FCOMP cdb_iterate_clause_aux_refine]
        
    concrete_definition (in -) cdb_iterate_clause_impl is clause_iteration_setup.cdb_iterate_clause_aux_impl_def
  
    lemmas (in -) cdb_iterate_clause_impl_code[llvm_code] = cdb_iterate_clause_impl_def[unfolded eo_with_impl_def zcl_fold_impl_def]  
      
    lemma cdb_iterate_clause_hnr[sepref_fr_rules]: 
      "(uncurry3 (cdb_iterate_clause_impl ci fi), uncurry3 (PR_CONST cdb_iterate_clause)) \<in> cdb_assn\<^sup>k *\<^sub>a cid_assn\<^sup>k *\<^sub>a P\<^sup>k *\<^sub>a S\<^sup>d \<rightarrow>\<^sub>a S"
      using cdb_iterate_clause_aux_hnr[unfolded cdb_iterate_clause_impl.refine[OF clause_iteration_setup_axioms]]
      .
    
     
  end


subsection \<open>Interface\<close>


typ cdb  
term cdb_assn

term cdb_empty thm cdb_empty_hnr (* map empty *)

term cdb_insert thm cdb_insert_hnr  (* map update. clause moved into map. *)
term cdb_delete thm cdb_delete_hnr (* delete clause *)
term cdb_contains thm cdb_contains_hnr (* map contains key *)

term clause_iteration_setup.cdb_iterate_clause
thm clause_iteration_setup.cdb_iterate_clause_def
thm clause_iteration_setup.cdb_iterate_clause_hnr
 

end
