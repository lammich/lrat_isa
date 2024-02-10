theory Zero_Term
imports 
  LRAT_Sepref_Base
  Unsigned_Literal
begin

    
  subsection \<open>Clause Buffer\<close>  

  text \<open>Internally used by clause builder\<close>
      
  type_synonym cbuf = "dv_lit list"  
  
  definition cbuf_\<alpha> :: "cbuf \<Rightarrow> dv_clause" where "cbuf_\<alpha> xs = set xs"
  lemma cbuf_\<alpha>_finite[simp, intro!]: "finite (cbuf_\<alpha> xs)"
    unfolding cbuf_\<alpha>_def by auto
  
  definition cbuf_empty :: cbuf where "cbuf_empty \<equiv> []"
  definition cbuf_flush :: "cbuf \<Rightarrow> cbuf" where "cbuf_flush xs = op_emptied_list xs"
  
  definition cbuf_insert :: "dv_lit \<Rightarrow> cbuf \<Rightarrow> cbuf" where "cbuf_insert l xs \<equiv> op_list_append xs l"
  
    
  lemma cbuf_empty_correct[simp]: "cbuf_\<alpha> cbuf_empty = {}"  
    unfolding cbuf_\<alpha>_def cbuf_empty_def by auto
    
  lemma cbuf_flush_correct[simp]: "cbuf_\<alpha> (cbuf_flush xs) = {}"  
    unfolding cbuf_\<alpha>_def cbuf_flush_def by auto
  
  lemma cbuf_insert_correct[simp]: "cbuf_\<alpha> (cbuf_insert l xs) = insert l (cbuf_\<alpha> xs)"
    unfolding cbuf_\<alpha>_def cbuf_insert_def by auto
  
  lemma cbuf_empty_length[simp]: "length cbuf_empty = 0"  
    unfolding cbuf_empty_def by auto
  
  lemma cbuf_flush_length[simp]: "length (cbuf_flush xs) = 0"  
    unfolding cbuf_flush_def by auto
    
  lemma cbuf_insert_length[simp]: "length (cbuf_insert l xs) = length xs + 1"  
    unfolding cbuf_insert_def by auto
    
    
  abbreviation "cbuf_aux_assn \<equiv> al_assn' size_T ulit_assn"  

  
  sepref_register cbuf_empty cbuf_flush cbuf_insert
        
  sepref_def cbuf_empty_impl is "uncurry0 (RETURN cbuf_empty)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a cbuf_aux_assn"
    unfolding cbuf_empty_def al_fold_custom_empty[where 'l=size_t]
    by sepref
    
  sepref_def cbuf_flush_impl is "RETURN o cbuf_flush" :: "cbuf_aux_assn\<^sup>d \<rightarrow>\<^sub>a cbuf_aux_assn"  
    unfolding cbuf_flush_def
    by sepref

  sepref_def cbuf_insert_impl is "uncurry (RETURN oo cbuf_insert)" 
    :: "[\<lambda>(_,xs). length xs + 1 < max_size]\<^sub>a ulit_assn\<^sup>k *\<^sub>a cbuf_aux_assn\<^sup>d \<rightarrow> cbuf_aux_assn"  
    unfolding cbuf_insert_def
    by sepref


  
subsection \<open>Zero-Terminated Clause\<close>

  
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

  
  

  
  definition "zcl_assn \<equiv> hr_comp zcl_aux_assn (br zcl_\<alpha> zcl_invar)"
  lemmas [fcomp_norm_unfold] = zcl_assn_def[symmetric]
  
  lemma zcl_assn_boundD[sepref_bounds_dest]: 
    "rdomp zcl_assn c \<Longrightarrow> finite c"
    unfolding zcl_assn_def
    apply (simp add: sep_algebra_simps split: prod.splits)
    by (auto simp: in_br_conv)
  
    

  sepref_register zcl_make  
    
  find_theorems b_assn hn_refine
  
  
  sepref_def zcl_make_impl is "zcl_make_aux" 
    :: "[\<lambda>xs. length xs + 1 < max_size]\<^sub>a cbuf_aux_assn\<^sup>k \<rightarrow> zcl_aux_assn"
(*    apply (rule hfref_bassn_resI)
    subgoal
      unfolding zcl_make_aux_def
      apply refine_vcg
      apply (rule leof_True_rule)
      apply refine_vcg
      by auto  
    *)  
    
    unfolding zcl_make_aux_def array_fold_custom_replicate nfoldli_upt_by_while
    apply (annot_snat_const size_T)
    by sepref
    
    
  lemmas zcl_make_impl_hnr[sepref_fr_rules] = zcl_make_impl.refine[FCOMP zcl_make_aux_refine]  
    
  sepref_def zcl_free_impl is "mop_free" :: "zcl_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn"  
    unfolding mop_free_alt zcl_assn_def
    by sepref
    
  lemmas [sepref_frame_free_rules] = MK_FREE_mopI[OF zcl_free_impl.refine]  
    
  subsubsection \<open>Interface\<close>
  
  term zcl_\<alpha> term zcl_invar
  
  term zcl_make thm zcl_make_def zcl_make_impl_hnr
  
  term zcl_fold thm zcl_fold_foreach_refine  (* To be inlined for sepref *)
  
    
  subsection \<open>Clause Builder\<close>  
    
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
    
    
  subsubsection \<open>Interface\<close>  
  
  term cbld_\<alpha>_clause term cbld_\<alpha>_cap term cbld_invar
  
  term cbld_new thm cbld_new_correct cbld_new_impl.refine
    
  term cbld_add_lit thm cbld_add_lit_correct cbld_add_lit_impl.refine
  term cbld_add_lit_impl
    
  term cbld_finish_clause thm cbld_finish_clause_correct cbld_finish_clause_impl.refine
  
  term cbld_abort_clause thm cbld_abort_clause_correct cbld_abort_clause_impl.refine

  term cbld_is_empty thm cbld_is_empty_correct cbld_is_empty_impl.refine
    
    
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
    
    
  (*  
  definition "zclo_invar xs \<equiv> xs\<noteq>[] \<longrightarrow> zcl_invar xs"
  definition "zclo_\<alpha> xs \<equiv> if xs=[] then None else Some (zcl_\<alpha> xs)"
  
  definition "zcl_to_zclo xs \<equiv> xs"
  definition "zclo_to_zcl xs \<equiv> xs"
  
  definition "zclo_None \<equiv> []"
  definition "zclo_is_None xs \<equiv> xs=[]"
  
  lemma zcl_to_zclo_correct[simp]:
    "zcl_invar xs \<Longrightarrow> zclo_invar (zcl_to_zclo xs)"
    "zcl_invar xs \<Longrightarrow> zclo_\<alpha> (zcl_to_zclo xs) = Some (zcl_\<alpha> xs)"
    unfolding zclo_invar_def zclo_\<alpha>_def zcl_to_zclo_def
    by auto
  
  lemma zclo_to_zcl_correct[simp]:  
    "zclo_invar xs \<Longrightarrow> \<not>is_None (zclo_\<alpha> xs) \<Longrightarrow> zcl_invar (zclo_to_zcl xs)"
    "zclo_invar xs \<Longrightarrow> \<not>is_None (zclo_\<alpha> xs) \<Longrightarrow> zcl_\<alpha> (zclo_to_zcl xs) = the (zclo_\<alpha> xs)"
    unfolding zclo_invar_def zclo_\<alpha>_def zclo_to_zcl_def
    by auto
    
  lemma zclo_None_correct[simp]: 
    "zclo_invar zclo_None"
    "zclo_\<alpha> zclo_None = None"
    unfolding zclo_invar_def zclo_None_def zclo_\<alpha>_def by auto
  
  lemma zclo_is_None_correct[simp]: "zclo_invar xs \<Longrightarrow> zclo_is_None xs \<longleftrightarrow> is_None (zclo_\<alpha> xs)"
    unfolding zclo_invar_def zclo_is_None_def zclo_\<alpha>_def by auto


  lemma is_init_eq_zcl_aux_assn[sepref_gen_algo_rules]: "GEN_ALGO zclo_None (is_init_eq zcl_aux_assn)"
    unfolding zclo_None_def 
    by (rule is_init_eq_array_assn)
  
  lemma is_init'_zcl_aux_assn[sepref_gen_algo_rules]: "GEN_ALGO zclo_None (is_init' zcl_aux_assn)"  
    by (simp add: is_init_eq_imp_init'_GA is_init_eq_zcl_aux_assn)
    
      
  sepref_register zclo_is_None
  sepref_def zclo_is_None_impl is "RETURN o zclo_is_None" :: "zcl_aux_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn" 
    unfolding zclo_is_None_def
    by sepref
    
  *)    
    
    
    
    
  subsection \<open>Clause Database\<close>  
      
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


subsubsection \<open>Interface\<close>


typ cdb  
term cdb_assn

term cdb_empty thm cdb_empty_hnr (* map empty *)

term cdb_insert thm cdb_insert_hnr  (* map update. clause moved into map. *)
term cdb_delete thm cdb_delete_hnr (* delete clause *)
term cdb_contains thm cdb_contains_hnr (* map contains key *)

term clause_iteration_setup.cdb_iterate_clause
thm clause_iteration_setup.cdb_iterate_clause_def
thm clause_iteration_setup.cdb_iterate_clause_hnr

  
(*  
oops  
  
ctd here:
  clean up!

    we just defined more abstract clause and clause-db operations. 
    Also a locale to instantiate iterations.
    
    Now go for it, and replace in checker
    
    
      
    \<rightarrow> we need check_empty_clause? (we can use cbld_is_empty)
    
    No, the literals are added to builder first. At the same time when assignment is set!
    Only after proof is completed, the clause is transferred from builder to clause database.
    \<rightarrow> At this point, we can easily check for empty in buffer!
      cbld_is_empty!
  
  
*)  
  


end
