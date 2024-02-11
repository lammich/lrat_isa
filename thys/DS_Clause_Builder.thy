section \<open>Clause Builder\<close>  
theory DS_Clause_Builder
imports 
  LRAT_Sepref_Base
  DS_Clause
begin


  subsection \<open>Functional Level\<close>    
  (* Clause builder: Assemble in intermediate buffer, then make clause *)  
    
  (* max-lit \<times> buf \<times> bound *)  
  type_synonym cbld = "nat \<times> cbuf \<times> nat"
    
  definition cbld_invar :: "cbld \<Rightarrow> bool" where 
    "cbld_invar \<equiv> \<lambda>(ml,cb,bnd). length cb \<le> bnd \<and> (\<forall>l\<in>cbuf_\<alpha> cb. ulit_of l \<le> ml)"
  
  definition cbld_\<alpha>_clause :: "cbld \<Rightarrow> dv_clause" where 
    "cbld_\<alpha>_clause \<equiv> \<lambda>(ml,cb,bnd). cbuf_\<alpha> cb"  
  
  definition cbld_\<alpha>_cap :: "cbld \<Rightarrow> nat" where "cbld_\<alpha>_cap \<equiv> \<lambda>(ml,cb,bnd). bnd - length cb"
  
  definition cbld_\<alpha>_maxlit :: "cbld \<Rightarrow> nat" where "cbld_\<alpha>_maxlit \<equiv> \<lambda>(ml,cb,bnd). ml"

  
  lemma cbld_\<alpha>_maxlit_bound: "\<lbrakk>cbld_invar bld; x\<in>cbld_\<alpha>_clause bld\<rbrakk> \<Longrightarrow> ulit_of x  \<le> cbld_\<alpha>_maxlit bld"
    unfolding cbld_invar_def cbld_\<alpha>_clause_def cbld_\<alpha>_maxlit_def
    by (auto)
  
    
  
    
  definition cbld_make :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> cbld" where [simp]: "cbld_make ml cb bnd \<equiv> (ml,cb,bnd)"
  definition cbld_dest :: "cbld \<Rightarrow> _" where [simp]: "cbld_dest bld \<equiv> bld"
  
  
  definition cbld_new :: "nat \<Rightarrow> cbld" where "cbld_new cap \<equiv> cbld_make 0 cbuf_empty cap"
  
  lemma cbld_new_correct[simp]:
    shows
      "cbld_invar (cbld_new n)"
      "cbld_\<alpha>_clause (cbld_new n) = {}"
      "cbld_\<alpha>_cap (cbld_new n) = n"
      "cbld_\<alpha>_maxlit (cbld_new n) = 0"
    unfolding cbld_invar_def cbld_\<alpha>_clause_def cbld_\<alpha>_cap_def cbld_new_def cbld_\<alpha>_maxlit_def
    by auto
  
  
  definition cbld_add_lit :: "dv_lit \<Rightarrow> cbld \<Rightarrow> cbld nres" where
    "cbld_add_lit l bld \<equiv> doN {
      let (ml,cb,bnd) = cbld_dest bld;
      ASSERT(length cb < bnd);
      let ml = max (ulit_of l) ml;
      let cb = cbuf_insert l cb;
      RETURN (cbld_make ml cb bnd)
    }"
      
  lemma cbld_add_lit_correct[refine_vcg]: 
    "\<lbrakk>cbld_invar bld; cbld_\<alpha>_cap bld > 0\<rbrakk> \<Longrightarrow> cbld_add_lit l bld \<le> SPEC (\<lambda>bld'. 
      cbld_invar bld'
    \<and> cbld_\<alpha>_clause bld' = insert l (cbld_\<alpha>_clause bld)
    \<and> cbld_\<alpha>_cap bld' = cbld_\<alpha>_cap bld - 1
    \<and> cbld_\<alpha>_maxlit bld' = max (cbld_\<alpha>_maxlit bld) (ulit_of l)
    )"
    unfolding cbld_add_lit_def
    apply refine_vcg
    unfolding cbld_invar_def cbld_\<alpha>_clause_def cbld_\<alpha>_cap_def cbld_\<alpha>_maxlit_def
    by auto
  
  definition cbld_finish_clause :: "cbld \<Rightarrow> (dv_clause \<times> cbld) nres" where
    "cbld_finish_clause bld \<equiv> doN {
      let (ml,cb,bnd) = cbld_dest bld;
      ASSERT (length cb < bnd);
      cl \<leftarrow> zcl_make cb;
      let cb = cbuf_flush cb;
      RETURN (cl,cbld_make ml cb bnd)
    }"
  
  lemma cbld_finish_clause_correct[refine_vcg]: "\<lbrakk> cbld_invar bld; cbld_\<alpha>_cap bld > 0 \<rbrakk> 
    \<Longrightarrow> cbld_finish_clause bld \<le> SPEC (\<lambda>(cl,bld').     
       cl = cbld_\<alpha>_clause bld
    \<and> cbld_invar bld'
    \<and> cbld_\<alpha>_clause bld' = {}
    \<and> cbld_\<alpha>_cap bld' \<ge> cbld_\<alpha>_cap bld
    \<and> cbld_\<alpha>_maxlit bld' = cbld_\<alpha>_maxlit bld
    )"  
    unfolding cbld_finish_clause_def
    apply refine_vcg
    unfolding cbld_invar_def cbld_\<alpha>_clause_def cbld_\<alpha>_cap_def cbld_\<alpha>_maxlit_def
    apply simp_all
    subgoal (* TODO: slight breaking of abstraction *)
      unfolding cbuf_\<alpha>_def by auto
    done

  definition cbld_abort_clause :: "cbld \<Rightarrow> cbld nres" where
    "cbld_abort_clause bld \<equiv> doN {
      let (ml,cb,bnd) = cbld_dest bld;
      let cb = cbuf_flush cb;
      RETURN (cbld_make ml cb bnd)
    }"
    
  lemma cbld_abort_clause_correct[refine_vcg]: "\<lbrakk> cbld_invar bld \<rbrakk> 
    \<Longrightarrow> cbld_abort_clause bld \<le> SPEC (\<lambda>bld'.     
      cbld_invar bld'
    \<and> cbld_\<alpha>_clause bld' = {}
    \<and> cbld_\<alpha>_cap bld' \<ge> cbld_\<alpha>_cap bld
    \<and> cbld_\<alpha>_maxlit bld' = cbld_\<alpha>_maxlit bld
    )"  
    unfolding cbld_abort_clause_def
    apply refine_vcg
    unfolding cbld_invar_def cbld_\<alpha>_clause_def cbld_\<alpha>_cap_def cbld_\<alpha>_maxlit_def
    by simp_all
    
        
  definition cbld_is_empty :: "cbld \<Rightarrow> bool nres" where
    "cbld_is_empty bld \<equiv> doN {
      let (ml,cb,bnd) = cbld_dest bld;
      let r = (length cb = 0);
      let bld' = cbld_make ml cb bnd;
      unborrow bld' bld;
      RETURN r
    }"

  lemma cbld_is_empty_correct[refine_vcg]: "cbld_invar bld \<Longrightarrow> cbld_is_empty bld \<le> SPEC (\<lambda>r. r \<longleftrightarrow> cbld_\<alpha>_clause bld = {})"  
    unfolding cbld_is_empty_def
    apply refine_vcg
    unfolding cbld_invar_def cbld_\<alpha>_clause_def cbuf_\<alpha>_def
    by auto
    
  definition cbld_get_maxlit :: "cbld \<Rightarrow> nat nres" where
    "cbld_get_maxlit bld \<equiv> doN {
      let (ml,cb,bnd) = cbld_dest bld;
      let bld' = cbld_make ml cb bnd;
      unborrow bld' bld;
      RETURN ml
    }"
    
  lemma dbld_get_maxlit_correct[refine_vcg]: "cbld_invar bld \<Longrightarrow> cbld_get_maxlit bld \<le> SPEC (\<lambda>r. r = cbld_\<alpha>_maxlit bld)"
    unfolding cbld_get_maxlit_def
    apply refine_vcg
    apply (auto simp: cbld_\<alpha>_maxlit_def)
    done
        

  subsection \<open>Refinement to Imperative Code\<close>  
    
  type_synonym cbldi = "lit_size_t word \<times> (lit_size_t word,size_t) array_list"  
  definition cbld_assn :: "cbld \<Rightarrow> cbldi \<Rightarrow> assn" where "cbld_assn \<equiv> \<lambda>(ml,cb,bnd) (mli,cbi). 
      lit_assn ml mli 
    ** cbuf_aux_assn cb cbi 
    ** dropi_assn (rdomp size_assn) bnd ghost_var"
    
  sepref_register cbld_make cbld_dest cbld_new cbld_add_lit cbld_finish_clause cbld_is_empty

      
  definition cbld_make_impl :: "_ \<Rightarrow> _ \<Rightarrow> 'a word \<Rightarrow> cbldi llM" 
    where [llvm_inline]: "cbld_make_impl mli cbi _ \<equiv> Mreturn (mli,cbi)"
  
  lemma cbld_make_impl_refine[sepref_fr_rules]: 
    "(uncurry2 cbld_make_impl,uncurry2 (RETURN ooo cbld_make)) 
    \<in> [\<lambda>_. True]\<^sub>c lit_assn\<^sup>k *\<^sub>a cbuf_aux_assn\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> cbld_assn [\<lambda>((ml,cb),_) r. r = (ml,cb) ]\<^sub>c"
    unfolding cbld_make_def cbld_make_impl_def cbld_assn_def any_rel_def
    apply sepref_to_hoare
    apply vcg_normalize
    
    apply (simp named_ss HOL_basic_ss_nomatch: move_resolve_ex_eq)
    
    supply [simp] = rdomp_pure_rel_eq
    apply vcg
    done    
  
  lemma cbld_make_impl_refine2[sepref_fr_rules]: 
    "(uncurry2 cbld_make_impl,uncurry2 (RETURN ooo cbld_make)) 
    \<in> [\<lambda>_. True]\<^sub>c lit_assn\<^sup>k *\<^sub>a cbuf_aux_assn\<^sup>d *\<^sub>a (dropi_assn (rdomp size_assn))\<^sup>k \<rightarrow> cbld_assn [\<lambda>((ml,cb),_) r. r = (ml,cb) ]\<^sub>c"
    unfolding cbld_make_def cbld_make_impl_def cbld_assn_def any_rel_def
    apply sepref_to_hoare
    apply vcg_normalize
    
    apply (simp named_ss HOL_basic_ss_nomatch: move_resolve_ex_eq)
    
    supply [simp] = rdomp_pure_rel_eq
    apply vcg
    done    
    
  lemma cbld_dest_impl_refine[sepref_fr_rules]: 
    "(\<lambda>(a,b). Mreturn (a,b,ghost_var::1 word), RETURN o cbld_dest) 
    \<in> [\<lambda>_. True]\<^sub>c cbld_assn\<^sup>d \<rightarrow> lit_assn \<times>\<^sub>a cbuf_aux_assn \<times>\<^sub>a dropi_assn (rdomp size_assn) [\<lambda>(ml,cb) (ml',cb',_). ml'=ml \<and> cb'=cb]\<^sub>c"  
    unfolding cbld_dest_def cbld_assn_def any_rel_def
    apply sepref_to_hoare
    apply vcg_normalize
    apply (simp named_ss HOL_basic_ss_nomatch: move_resolve_ex_eq)
    by vcg
  
  
  sepref_def cbld_new_impl is "RETURN o cbld_new" :: "size_assn\<^sup>k \<rightarrow>\<^sub>a cbld_assn"  
    unfolding cbld_new_def
    apply (rewrite unat_const_fold[where 'a=lit_size_t])
    by sepref

  sepref_def cbld_add_lit_impl is "uncurry cbld_add_lit" :: "ulit_assn\<^sup>k *\<^sub>a cbld_assn\<^sup>d \<rightarrow>\<^sub>a cbld_assn"  
    unfolding cbld_add_lit_def max_def
    by sepref
    
  sepref_def cbld_finish_clause_impl is "cbld_finish_clause" :: "cbld_assn\<^sup>d \<rightarrow>\<^sub>a zcl_assn \<times>\<^sub>a cbld_assn"
    unfolding cbld_finish_clause_def
    by sepref

  sepref_def cbld_abort_clause_impl is "cbld_abort_clause" :: "cbld_assn\<^sup>d \<rightarrow>\<^sub>a cbld_assn"
    unfolding cbld_abort_clause_def
    by sepref
            
  sepref_def cbld_is_empty_impl is "cbld_is_empty" :: "cbld_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding cbld_is_empty_def
    apply (annot_snat_const size_T)
    by sepref
    
  sepref_def cbld_get_maxlit_impl is "cbld_get_maxlit" :: "cbld_assn\<^sup>k \<rightarrow>\<^sub>a lit_assn"  
    unfolding cbld_get_maxlit_def
    by sepref
    
        
  sepref_definition cbld_free [llvm_code] is "\<lambda>cbld. doN {let _ = cbld_dest cbld; RETURN ()}" :: "cbld_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn"  
    by sepref
  
  lemma cbld_free[sepref_frame_free_rules]: "MK_FREE cbld_assn cbld_free"
    apply (rule MK_FREE_hfrefI[OF cbld_free.refine])
    by auto
    
    
  subsection \<open>Interface\<close>  
  
  term cbld_\<alpha>_clause term cbld_\<alpha>_cap term cbld_invar
  
  term cbld_new thm cbld_new_correct cbld_new_impl.refine
    
  term cbld_add_lit thm cbld_add_lit_correct cbld_add_lit_impl.refine
  term cbld_add_lit_impl
    
  term cbld_finish_clause thm cbld_finish_clause_correct cbld_finish_clause_impl.refine
  
  term cbld_abort_clause thm cbld_abort_clause_correct cbld_abort_clause_impl.refine

  term cbld_is_empty thm cbld_is_empty_correct cbld_is_empty_impl.refine
    
end
