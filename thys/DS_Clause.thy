section \<open>Zero-Terminated Clauses\<close>
theory DS_Clause
imports 
  LRAT_Sepref_Base
  DS_Clause_Buffer
begin

  subsection \<open>Functional Level\<close>

  type_synonym zclause = "dv_lit option list"
  
  definition zcl_\<alpha> :: "zclause \<Rightarrow> dv_clause" where "zcl_\<alpha> xs \<equiv> the`set (butlast xs)"
  definition zcl_invar :: "zclause \<Rightarrow> bool" where "zcl_invar xs \<equiv> xs\<noteq>[] \<and> None \<notin> set (butlast xs) \<and> last xs = None"


  lemma zcl_\<alpha>_finite[simp,intro!]: "finite (zcl_\<alpha> xs)"
    unfolding zcl_\<alpha>_def by auto
  
  lemma zcl_invar_Cons: "zcl_invar (x#xsz) \<longleftrightarrow> (x=None \<and> xsz=[] \<or> \<not>is_None x \<and> zcl_invar xsz)"      
    unfolding zcl_invar_def
    by auto
  
  lemma zcl_invar_Nil[simp]: "\<not>zcl_invar []" unfolding zcl_invar_def by auto
  
  definition "zcl_make_aux xs \<equiv> doN {
    l \<leftarrow> mop_list_length xs;
    rs \<leftarrow> mop_list_replicate (l+1) ulito_None;
    
    rs \<leftarrow> nfoldli [0..<l] (\<lambda>_. True) (\<lambda>i rs. do {
      t \<leftarrow> mop_list_get xs i;
      let t = Some t;
      rs \<leftarrow> mop_list_set rs i t;
      RETURN rs
    }) rs;
 
    ASSERT (length rs = l+1);
    rs \<leftarrow> mk_b_assn (\<lambda>rs. length rs < max_size) rs;
    
    RETURN rs 
  }"

  definition [simp]: "zcl_make xs \<equiv> RETURN (set xs)"
  
  lemma zcl_make_aux_refine: "(zcl_make_aux, zcl_make) \<in> Id \<rightarrow> \<langle>br zcl_\<alpha> zcl_invar\<rangle>nres_rel"
    unfolding zcl_make_def zcl_make_aux_def
    apply (intro fun_relI, clarsimp)
    subgoal for xs
      apply (refine_vcg nfoldli_rule[where 
        I="\<lambda>xs\<^sub>1 xs\<^sub>2 rs. rs = map Some (take (length xs\<^sub>1) xs)@replicate (length xs\<^sub>2+1) None"])
      apply (clarsimp_all simp: upt_eq_lel_conv)
      subgoal by (simp add: list_update_append take_Suc_conv_app_nth)
      subgoal unfolding zcl_invar_def zcl_\<alpha>_def br_def by force
      done
    done
    
  
  
  definition "zcl_fold_aux xs i c f s \<equiv> doN {
    (s,_,_)\<leftarrow>WHILET (\<lambda>(s,i,brk). c s \<and> \<not>brk) (\<lambda>(s,i,brk). doN {
      xs' \<leftarrow> MOVE xs;
      x \<leftarrow> mop_list_get xs' i;
      let _ = restore_bound xs' xs;
      
      if is_None x then RETURN (s,i,True)
      else do {
        s\<leftarrow>f (the x) s;
        ASSERT (i<length xs);
        RETURN (s,i+1,False)
      }
    }) (s,i,False);
    RETURN s
  }"  
      
  definition "zcl_fold xs c f s \<equiv> zcl_fold_aux xs 0 c f s"
  
  lemmas zcl_fold_def' = zcl_fold_def[unfolded zcl_fold_aux_def]
  
    
  context begin
  private lemma zcl_fold_aux_Suc_tl: "zcl_fold_aux xs (Suc i) c f s \<le> zcl_fold_aux (tl xs) i c f s"
    unfolding zcl_fold_aux_def MOVE_def unborrow'_def
    apply simp
    apply (rule refine_IdD)
    apply (refine_rcg)
    supply [refine_dref_RELATES] = RELATESI[where R="Id \<times>\<^sub>r {(Suc i, i) | i. True} \<times>\<^sub>r Id"]
    apply (refine_dref_type)
    apply simp_all
    apply (auto simp: Misc.nth_tl)
    done      
    
  private lemma zcl_fold_aux_tl_Suc: "zcl_fold_aux (tl xs) i c f s \<le> zcl_fold_aux xs (Suc i) c f s"
    unfolding zcl_fold_aux_def MOVE_def unborrow'_def
    apply simp
    apply (rule refine_IdD)
    apply (refine_rcg)
    supply [refine_dref_RELATES] = RELATESI[where R="Id \<times>\<^sub>r {(i, Suc i) | i. True} \<times>\<^sub>r Id"]
    apply (refine_dref_type)
    apply simp_all
    apply (auto simp: Misc.nth_tl)
    done      

  private lemma zcl_fold_aux_Cons: "zcl_fold_aux (x#xs) (Suc i) c f s = zcl_fold_aux xs i c f s"
    apply (rule antisym)
    apply (rule order_trans[OF zcl_fold_aux_Suc_tl]; simp)
    apply (rule order_trans[OF _ zcl_fold_aux_tl_Suc]; simp)  
    done
        
  private lemma zcl_fold_aux_unfold: "zcl_fold_aux xs i c f s = (
    if c s then doN {
      x \<leftarrow> mop_list_get xs i;
      if is_None x then RETURN s
      else do {
        s\<leftarrow>f (the x) s;
        ASSERT (i<length xs);
        zcl_fold_aux xs (i+1) c f s
      }
    } else RETURN s
  
  )"
    unfolding zcl_fold_aux_def
    apply (cases "c s"; simp)
    subgoal
      apply (subst WHILET_unfold; simp)
      apply (subst WHILET_unfold; simp)
      apply (subst WHILET_unfold; simp)
      done
    subgoal
      apply (subst WHILET_unfold; simp)
      done
    done

  lemma zcl_fold_unfold: "zcl_fold (x#xs) c f s = (
    if c s then doN {
      if is_None x then RETURN s
      else do {
        s\<leftarrow>f (the x) s;
        zcl_fold xs c f s
      }
    } else RETURN s
  
  )"  
    unfolding zcl_fold_def
    apply (rewrite in "\<hole> = _" zcl_fold_aux_unfold)
    apply (cases "c s"; clarsimp)
    apply (fo_rule arg_cong)
    apply (rule ext)
    by (simp add: zcl_fold_aux_Cons)
    
  end  
        
  lemma zcl_fold_refine[refine]: 
    assumes XS: "(xs,xs')\<in>Id"
    assumes RS: "(s,s')\<in>Rs"
    assumes CR: "\<And>s s'. (s,s')\<in>Rs \<Longrightarrow> (c s, c' s')\<in>bool_rel"
    assumes F'_refine: "\<And>l l' s s'. \<lbrakk> (l,l')\<in>Id; (s,s')\<in>Rs  \<rbrakk> \<Longrightarrow> f l s \<le> \<Down>Rs (f' l' s')"
    shows "zcl_fold xs c f s \<le> \<Down>Rs (zcl_fold xs' c' f' s')"
    unfolding zcl_fold_def'
    apply (refine_rcg F'_refine)
    supply [refine_dref_RELATES] = RELATESI[of Rs]
    apply refine_dref_type
    using XS
    apply (clarsimp_all simp: RS)
    subgoal using CR by blast
    done
    
  
  lemma zcl_fold_nfoldli_refine: "zcl_invar xs \<Longrightarrow> zcl_fold xs c f s \<le> nfoldli (map the (butlast xs)) c f s"
    apply (induction "xs" arbitrary: s)
    subgoal for s
      by auto
    subgoal for x xs s
      apply (simp add: zcl_fold_unfold)
      apply (auto simp: zcl_invar_Cons)
      apply (rule bind_mono)
      apply (rule order_refl)
      apply simp
      done
    done
    
  lemma zcl_fold_foreach_refine:
    assumes RCL: "(xs,cl)\<in>br zcl_\<alpha> zcl_invar"
    assumes RS: "(s,s')\<in>Rs"
    assumes CR: "\<And>s s'. (s,s')\<in>Rs \<Longrightarrow> (c s, c' s')\<in>bool_rel"
    assumes F'_refine: "\<And>l l' s s'. \<lbrakk> (l,l')\<in>Id; l'\<in>zcl_\<alpha> xs; (s,s')\<in>Rs  \<rbrakk> \<Longrightarrow> f l s \<le> \<Down>Rs (f' l' s')"
    shows "zcl_fold xs c f s \<le> \<Down>Rs (FOREACHcd cl c' f' s')"
    unfolding FOREACHcd_def
    apply (rule refine)
    apply (rule rhs_step_bind_SPEC[where x'="map the (butlast xs)"])
    subgoal using RCL unfolding zcl_\<alpha>_def br_def by simp
    apply (rule order_trans[OF zcl_fold_nfoldli_refine])
    subgoal using RCL unfolding br_def by simp
    apply (rule nfoldli_invar_refine[where I=top])
    apply refine_dref_type
    subgoal by simp
    subgoal by (rule RS)
    subgoal by auto
    subgoal using CR by auto
    subgoal by (simp add: pw_leof_iff)
    apply clarsimp
    subgoal for l1 x l2 s s'
      apply (rule F'_refine)
      subgoal by simp
      subgoal
        unfolding zcl_\<alpha>_def 
        by (simp add: image_set)
      subgoal by simp
      done
    done

  abbreviation "zcl_aux_assn \<equiv> b_assn (array_assn ulito_assn) (\<lambda>xs. length xs < max_size)"


  subsection \<open>Refinement to Imperative Code\<close>
  
  definition "zcl_assn \<equiv> hr_comp zcl_aux_assn (br zcl_\<alpha> zcl_invar)"
  lemmas [fcomp_norm_unfold] = zcl_assn_def[symmetric]
  
  lemma zcl_assn_boundD[sepref_bounds_dest]: 
    "rdomp zcl_assn c \<Longrightarrow> finite c"
    unfolding zcl_assn_def
    apply (simp add: sep_algebra_simps split: prod.splits)
    by (auto simp: in_br_conv)
  
    

  sepref_register zcl_make  
  
  sepref_def zcl_make_impl is "zcl_make_aux" 
    :: "[\<lambda>xs. length xs + 1 < max_size]\<^sub>a cbuf_aux_assn\<^sup>k \<rightarrow> zcl_aux_assn"
    unfolding zcl_make_aux_def array_fold_custom_replicate nfoldli_upt_by_while
    apply (annot_snat_const size_T)
    by sepref
    
    
  lemmas zcl_make_impl_hnr[sepref_fr_rules] = zcl_make_impl.refine[FCOMP zcl_make_aux_refine]  
    
  sepref_def zcl_free_impl is "mop_free" :: "zcl_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn"  
    unfolding mop_free_alt zcl_assn_def
    by sepref
    
  lemmas [sepref_frame_free_rules] = MK_FREE_mopI[OF zcl_free_impl.refine]  
    
  subsection \<open>Zero-Terminated Clause or empty List\<close>  
    
  (*
    Used internally in clause database, to store non-present clauses as empty list
  *)
  interpretation zcl: dflt_option_init zcl_assn "ll_ptrcmp_eq null"
    apply unfold_locales
    subgoal
      unfolding zcl_assn_def
      by (auto simp: hr_comp_def array_assn_def narray_assn_null_eq in_br_conv fun_eq_iff sep_algebra_simps)
    subgoal for p
      supply [vcg_rules] = ll_ptrcmp_eq_null'_rl
      by vcg
    done
  
  subsection \<open>Interface\<close>
  
  term zcl_\<alpha> term zcl_invar (* Abstraction function and invariant *)
  
  term zcl_make thm zcl_make_def zcl_make_impl_hnr (* Constructor *)
  
  term zcl_fold thm zcl_fold_foreach_refine  (* To be inlined for sepref *)





end
