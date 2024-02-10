theory LRAT_Sepref_Base
imports   
  Isabelle_LLVM.IICF 
  Isabelle_LLVM.Proto_IICF_EOArray 
  Proto_Sepref_Ghostvar
  Sizes_Setup
begin

  hide_const (open) LLVM_DS_Array.array_assn
  hide_const (open) LLVM_DS_NArray.array_slice_assn  


  
  subsection \<open>Misc\<close>
  
  lemma drop_upd_first: "a<length xs \<Longrightarrow> (drop a xs)[0:=x] = x#drop (Suc a) xs"
    by (simp add: drop_Suc_nth) 
  
    
    
      
  lemma repl_in_list_rel_conv: "(replicate n a, replicate n' b) \<in> \<langle>R\<rangle>list_rel \<longleftrightarrow> n'=n \<and> (n=0 \<or> (a,b)\<in>R)"
    apply (induction n arbitrary: n')
    subgoal for n'
      apply (cases n')
      apply auto
      done
    subgoal for n n'
      apply (cases n')
      apply auto
      done
    done  
   
    
  lemma sep_set_img_all_box[sep_algebra_simps]: "finite s \<Longrightarrow> (\<Union>*x\<in>s. \<box>) = \<box>"
    apply (induction s rule: finite_induct)
    by (auto)
  

  context  
  begin
    interpretation llvm_prim_arith_setup .
  
    lemma ll_ptrcmp_eq_null_rl: "llvm_htriple \<box> (ll_ptrcmp_eq p null) (\<lambda>ri. EXS r. \<upharpoonleft>bool.assn r ri ** \<up>(r \<longleftrightarrow> p=null))"
      unfolding bool.assn_def
      by vcg

    lemma ll_ptrcmp_eq_null'_rl: "llvm_htriple \<box> (ll_ptrcmp_eq null p) (\<lambda>ri. EXS r. \<upharpoonleft>bool.assn r ri ** \<up>(r \<longleftrightarrow> p=null))"
      unfolding bool.assn_def
      by vcg
      
  end    

  
  (* TODO: Move! And add more rules! *)  
  lemma move_resolve_ex_eq:
    "\<up>(a=b \<and> P) = (\<up>(a=b) ** \<up>P)"
    "NO_MATCH (\<up>(Ax=Bx)) Q \<Longrightarrow> (Q ** \<up>(a=b)) = (\<up>(a=b) ** Q) \<and> (Q ** (\<up>(a=b) ** R)) = (\<up>(a=b) ** (Q ** R))"
    "\<And>a b. (\<exists>x. (\<up>(a=b) ** RR x) s) = (\<up>(a=b) ** (EXS x. RR x)) s"
    "\<And>b. (\<exists>a. (\<up>(a=b) ** RR a) s) = RR b s"
    "\<And>a. (\<exists>b. (\<up>(a=b) ** RR b) s) = RR a s"
    apply (simp_all add: sep_algebra_simps)
    done
    
  lemma rdomp_pure_rel_eq: "rdomp (\<lambda>a c. \<up>((c, a) \<in> R)) a \<longleftrightarrow> (\<exists>c. (c,a)\<in>R)"
    unfolding rdomp_def
    by (auto simp: sep_algebra_simps)  

    
  
  (* TODO: Move to Refine_Monadic_Add. Duplicates in isbalele_llvm/\<dots>/examples/Sorting_Misc! *)
  (* TODO: Move *)
  abbreviation monadic_If :: "bool nres \<Rightarrow> 'a nres \<Rightarrow> 'a nres \<Rightarrow> 'a nres" ("(if\<^sub>N (_)/ then (_)/ else (_))" [0, 0, 10] 10)
    where "monadic_If b x y \<equiv> doN { t \<leftarrow> b; if t then x else y }"
    
  (* TODO: Move *)
  lemma monadic_WHILEIT_rule:
    assumes "wf R"
    assumes "I s"
    assumes STEP: "\<And>s. I s \<Longrightarrow> b s \<le> SPEC (\<lambda>r. if r then c s \<le> SPEC (\<lambda>s'. I s' \<and> (s',s)\<in>R) else \<Phi> s)"
    shows "monadic_WHILEIT I b c s \<le> SPEC \<Phi>"
    using \<open>wf R\<close> \<open>I s\<close> apply (induction s rule: wf_induct_rule)
    apply (subst monadic_WHILEIT_unfold)
    apply (refine_vcg)
    apply (rule STEP[THEN order_trans], assumption)
    apply (refine_vcg)
    subgoal
      apply (split if_splits; simp)
      apply (rule order_trans, assumption)
      apply (refine_vcg)
      apply blast
      done
    subgoal
      by auto  
    done
  
  lemma monadic_WHILEIT_strengthen_invar_rule:
    assumes INEW_IMP: "\<And>s. Inew s \<Longrightarrow> I s"
    assumes "wf R"
    assumes "Inew s"
    assumes STEP: "\<And>s. Inew s \<Longrightarrow> b s \<le> SPEC (\<lambda>r. if r then c s \<le> SPEC (\<lambda>s'. Inew s' \<and> (s',s)\<in>R) else \<Phi> s)"
    shows "monadic_WHILEIT I b c s \<le> SPEC \<Phi>"
    using \<open>wf R\<close> \<open>Inew s\<close> apply (induction s rule: wf_induct_rule)
    apply (subst monadic_WHILEIT_unfold)
    apply (refine_vcg)
    apply (simp add: INEW_IMP; fail)
    apply (rule STEP[THEN order_trans], assumption)
    apply (refine_vcg)
    subgoal
      apply (split if_splits; simp)
      apply (rule order_trans, assumption)
      apply (refine_vcg)
      apply blast
      done
    subgoal
      by auto  
    done
    
    
  (* Required as VCG-rule when using monadic_WHILEIT_rule *)    
  lemma split_ifI[refine_vcg]: "\<lbrakk> b\<Longrightarrow>P; \<not>b\<Longrightarrow>Q \<rbrakk> \<Longrightarrow> If b P Q" by simp 
  
  
  (* TODO: Move *)
  lemma mk_vcg_rule_PQ:
    assumes "m \<equiv> doN {ASSERT P; SPEC Q}"
    assumes "P"
    shows "m \<le> SPEC Q"
    using assms by auto  
  
    
    
    
    
    
    
    
    
    
    
  subsection \<open>Unborrow without abstract assertion\<close>  
  (* TODO: Move, to Proto_Sepref_Borrow *)

  text \<open>Operation to reinstantiate dst, by moving source. 
    Implementations will also require a proof that the concrete objects are equal!
  \<close>
  definition unborrow' :: "'a \<Rightarrow> 'a \<Rightarrow> unit" where [simp]: "unborrow' src dst \<equiv> ()"
  sepref_register unborrow'
  
  lemma unborrow'_rule[sepref_comb_rules]:
    assumes FRAME: "\<Gamma> \<turnstile> hn_ctxt R src srci ** hn_invalid R dst dsti ** F"
    assumes EQ: "src = dst"
    assumes EQI: "vassn_tag \<Gamma> \<Longrightarrow> CP_cond (srci = dsti)"
    shows "hn_refine \<Gamma> (Mreturn ()) (hn_invalid R src srci ** hn_ctxt R dst dsti ** F) unit_assn (\<lambda>_. True) (RETURN$(unborrow'$src$dst))"
    apply (rule hn_refine_vassn_tagI)
    apply (rule hn_refine_cons_pre[OF FRAME])
    apply (rule hn_refineI)
    using EQ EQI
    unfolding unborrow'_def CP_defs
    apply (simp add: refine_pw_simps)
    unfolding hn_ctxt_def invalid_assn_def pure_def
    apply vcg'
    done
    
    
  
    
    
  
  
  subsection \<open>More Bounded Assertion\<close>
    
  definition mk_b_assn :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a nres" where "mk_b_assn B x \<equiv> RETURN x"

  lemma mk_b_assn_rl[refine_vcg]: "mk_b_assn B x \<le> SPEC (\<lambda>r. r=x)"
    unfolding mk_b_assn_def
    apply refine_vcg
    by auto
  
  
  
    
  context 
    fixes B :: "'a \<Rightarrow> bool"
  begin
    sepref_register "mk_b_assn B" 
  end  
  
  lemma mk_b_assn_hnr[sepref_fr_rules]: "(Mreturn, PR_CONST (mk_b_assn B)) \<in> [\<lambda>x. B x]\<^sub>a [\<lambda>_. True]\<^sub>c A\<^sup>d \<rightarrow>\<^sub>d (\<lambda>_. b_assn A B) [\<lambda>xi r. r=xi]\<^sub>c"
    unfolding mk_b_assn_def
    apply sepref_to_hoare
    supply [simp] = refine_pw_simps
    by vcg
  

    
  (* Workaround against loosing bounds. MOVE to new variable before bound is lost, then back with restore_bound *)
  definition restore_bound :: "'a \<Rightarrow> 'a \<Rightarrow> unit" where [simp]: "restore_bound src dst \<equiv> ()"
  sepref_register restore_bound
  
  lemma restore_bound_rule[sepref_comb_rules]:
    assumes FRAME: "\<Gamma> \<turnstile> hn_ctxt R src srci ** hn_invalid (b_assn R B) dst dsti ** F"
    assumes EQ: "src = dst"
    assumes EQI: "vassn_tag \<Gamma> \<Longrightarrow> CP_cond (srci = dsti)"
    shows "hn_refine \<Gamma> (Mreturn ()) (hn_invalid R src srci ** hn_ctxt (b_assn R B) dst dsti ** F) unit_assn (\<lambda>_. True) (RETURN$(restore_bound$src$dst))"
    apply (rule hn_refine_vassn_tagI)
    apply (rule hn_refine_cons_pre[OF FRAME])
    apply (rule hn_refineI)
    using EQ EQI
    unfolding unborrow'_def CP_defs
    apply (simp add: refine_pw_simps)
    unfolding hn_ctxt_def invalid_assn_def pure_def
    apply vcg'
    done
  
  
  
  
  
  
        
  
  subsection \<open>More default initializer\<close>  
  
  (* More default initializer: The is_init is too weak, assuming pure assertions.
  
    We only need to be pure at init!
    Also, in typical cases, the assertion will only hold on the empty memory,
    allowing us to convert between assertion and empty memory.
  *)
  
  definition is_init' :: "('a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn) \<Rightarrow> 'a \<Rightarrow> bool" 
    where "is_init' A i \<equiv> \<box> \<turnstile> A i init"
    
  lemma is_init_imp_init': "is_init A i \<Longrightarrow> is_init' A i"  
    unfolding is_init_def is_init'_def
    by (metis (full_types) entails_eq_iff pure_app_eq pure_the_pure pure_true_conv)
    
  lemma is_init'_id_assn[sepref_gen_algo_rules]: "GEN_ALGO init (is_init' id_assn)"
    by (auto simp: GEN_ALGO_def is_init'_def pure_def sep_algebra_simps)
  
  lemma is_init'_array_assn[sepref_gen_algo_rules]: "GEN_ALGO [] (is_init' (array_assn A))"
    apply (simp add: GEN_ALGO_def is_init'_def)
    unfolding array_assn_def hr_comp_def
    by fri
  
    
  definition is_init_eq :: "('a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn) \<Rightarrow> 'a \<Rightarrow> bool" 
    where "is_init_eq A i \<equiv> \<forall>ii. A i ii = \<up>(ii=init)"
    
  lemma is_init_eq_imp_init': "is_init_eq A i \<Longrightarrow> is_init' A i"  
    unfolding is_init_eq_def is_init'_def 
    by (metis (full_types) entails_eq_iff pure_true_conv)

      
  lemma is_init_eq_imp_init'_GA: "GEN_ALGO x (is_init_eq A) \<Longrightarrow> GEN_ALGO x (is_init' A)"
    unfolding GEN_ALGO_def
    by (rule is_init_eq_imp_init')
  
    
        
  lemma is_init_eq_id_assn[sepref_gen_algo_rules]: "GEN_ALGO init (is_init_eq id_assn)"
    by (auto simp: GEN_ALGO_def is_init_eq_def pure_def sep_algebra_simps)
    
    
  lemma is_init_eq_array_assn[sepref_gen_algo_rules]: "GEN_ALGO [] (is_init_eq (array_assn A))"
    apply (simp add: GEN_ALGO_def is_init_eq_def)
    unfolding array_assn_def hr_comp_def
    unfolding LLVM_DS_NArray.narray_assn_def
    by (auto simp: entails_def sep_algebra_simps)
    
    
  definition [simp]: "mop_free_dflt iv x \<equiv> do { ASSERT (x=iv); RETURN () }"  
  
  lemma mop_free_dflt_rl[refine_vcg]: "x=iv \<Longrightarrow> mop_free_dflt iv x \<le> SPEC (\<lambda>_. True)" by simp
    
  context fixes iv begin
    sepref_register "mop_free_dflt iv"
  end
  
  lemma mop_free_dflt_hnr[sepref_fr_rules]:
    assumes "GEN_ALGO iv (is_init_eq A)"
    shows "(\<lambda>_. Mreturn (), PR_CONST (mop_free_dflt iv)) \<in> A\<^sup>d \<rightarrow>\<^sub>a unit_assn"
  proof -
    from assms have [simp]: "A iv xs = (\<up>(xs=init))" for xs
      unfolding GEN_ALGO_def is_init_eq_def by auto
  
      
    show ?thesis
      supply [simp] = refine_pw_simps
      apply sepref_to_hoare
      by vcg
      
  qed
  
  subsection \<open>Default Option where init is default value\<close>
  
  
  locale dflt_option_init = dflt_option init A is_dflt for A is_dflt 
  begin
    
    lemma is_init_eqI[sepref_gen_algo_rules]:
      "GEN_ALGO None (is_init_eq option_assn)"
      unfolding GEN_ALGO_def is_init_eq_def option_assn_def
      by auto
      
    lemma is_init'I[sepref_gen_algo_rules]: "GEN_ALGO None (is_init' option_assn)"
      by (meson is_init_eqI is_init_eq_imp_init'_GA)  
  
  end  
  
  
    

  subsection \<open>More Array\<close>
  
  lemma narray_assn_null_eq: "\<upharpoonleft>narray_assn x null = \<up>(x=[])"
    unfolding narray_assn_def
    by (auto split: list.split)

  lemma narray_assn_Nil_eq: "\<upharpoonleft>narray_assn [] p = \<up>(p=null)"
    unfolding narray_assn_def
    by (auto split: list.split)
    
  (* Checking an array for being empty *)        
  lemma raw_array_assn_empty_hn: "(\<lambda>xsi. ll_ptrcmp_eq xsi null, RETURN o op_list_is_empty) \<in> (raw_array_assn)\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding bool1_rel_def bool.assn_is_rel[symmetric]
    supply [vcg_rules] = ll_ptrcmp_eq_null_rl
    supply [simp] = narray_assn_null_eq narray_assn_Nil_eq
    apply sepref_to_hoare
    by vcg

  (* Clearing an array *)
  definition array_emptied_impl :: "'a::llvm_rep ptr \<Rightarrow> 'a ptr llM" where [llvm_inline]:
    "array_emptied_impl p \<equiv> doM { narray_free p; Mreturn null }"
  
  lemma array_emptied_impl_hnr: "(array_emptied_impl, RETURN o op_emptied_list) \<in> raw_array_assn\<^sup>d \<rightarrow>\<^sub>a raw_array_assn"
    unfolding array_emptied_impl_def op_emptied_list_def
    apply sepref_to_hoare
    by vcg
    
        
  context 
    notes [fcomp_norm_unfold] = array_assn_def[symmetric] array_assn_comp
  begin    
    sepref_decl_impl raw_array_assn_empty_hn .
    sepref_decl_impl array_emptied_impl_hnr .  
  end    
  
  
  
  subsection \<open>More EO and WO Array\<close>


  subsubsection \<open>Helper Lemmas\<close>
  
    
    
  lemma list_oelem_assn_NoneI: "PRECOND (SOLVE_DEFAULT_AUTO (n=n')) \<Longrightarrow> \<box> \<turnstile> \<upharpoonleft>(list_assn (oelem_assn A)) (replicate n None) (replicate n' xs)"
    by (cases "n'=n"; simp add: sep_algebra_simps list_assn_def PRECOND_def SOLVE_DEFAULT_AUTO_def)
    
  lemma list_oelem_assn_initI:
    assumes "\<box> \<turnstile> A x init"
    shows "\<box> \<turnstile> \<upharpoonleft>(list_assn (oelem_assn (mk_assn A))) (replicate n (Some x)) (replicate n init)"  
    unfolding list_assn_def
    apply (simp add: sep_algebra_simps)
    using nao_repl_init_aux[where A="mk_assn A", simplified, OF assms]
    by blast
  
  
  lemma list_assn_None_emp_eq: "set xs \<subseteq> {None} 
    \<Longrightarrow> \<upharpoonleft>(list_assn (oelem_assn (mk_assn A))) xs xs' = \<up>(length xs = length xs')"
    unfolding PRECOND_def SOLVE_DEFAULT_AUTO_def
    apply (induction xs arbitrary: xs')
    subgoal for xs'
      by auto
    subgoal for a xs xs'
      apply (cases xs')
      apply (auto simp: sep_algebra_simps entails_def list_assn_cons1_conv)
      done
    done
  
    
    
    
  lemma nao_new_rule: "llvm_htriple 
    (\<upharpoonleft>snat.assn n ni) 
    (narray_new TYPE('a::llvm_rep) ni) 
    (\<lambda>ri. \<upharpoonleft>(Proto_EOArray.nao_assn A) (replicate n None) ri)"
    unfolding Proto_EOArray.nao_assn_def
    supply [fri_rules] = list_oelem_assn_NoneI
    by vcg
    
  

  subsubsection \<open>New\<close>
    
  text \<open>Create unowned elements\<close>
  definition op_eoarray_new :: "('a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn) \<Rightarrow> nat \<Rightarrow> 'a option list"
    where [simp]: "op_eoarray_new A n \<equiv> replicate n None"  
    
  context
    fixes A :: "'a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn"
  begin
    sepref_register "op_eoarray_new A"
    
    lemma op_eoarray_new_hnr[sepref_fr_rules]: "(narray_new TYPE('c), RETURN o PR_CONST (op_eoarray_new A)) \<in> size_assn\<^sup>k \<rightarrow>\<^sub>a eoarray_assn A"
      unfolding eoarray_assn_def
      unfolding snat_rel_def snat.assn_is_rel[symmetric]
      apply sepref_to_hoare
      supply [vcg_rules] = nao_new_rule (* TODO: clashes with other rules for narray_new, and is only resolved by backtracking! *)
      by (vcg)
    
    
  end  
  

  text \<open>Create default-initialized elements\<close>    
  definition [simp]: "op_woarray_replicate x n \<equiv> replicate n x"
  lemmas woarray_fold_custom_replicate = op_woarray_replicate_def[symmetric]
  
  (* Auxiliary Definition *)  
  definition [llvm_inline]: "woarray_new TYPE('a::llvm_rep) ni \<equiv> narray_new TYPE('a::llvm_rep) ni"  
    
  lemma woarray_assn_repl_init[vcg_rules]:
    assumes "PRECOND (SOLVE_DEFAULT_AUTO (\<box> \<turnstile> A x init))"
    shows "llvm_htriple 
      (\<upharpoonleft>snat.assn n ni) 
      (woarray_new TYPE('a::llvm_rep) ni) 
      (\<lambda>ri. (woarray_assn A) (replicate n x) ri)"
    unfolding woarray_new_def woarray_assn_def eoarray_assn_def Proto_EOArray.nao_assn_def hr_comp_def
    apply simp
    supply [fri_rules] = list_oelem_assn_initI[where A=A,OF assms[unfolded PRECOND_def SOLVE_DEFAULT_AUTO_def]]
    supply [simp] = repl_in_list_rel_conv
    by vcg
  
    
    
  
  context fixes x begin
  sepref_register "op_woarray_replicate x" 
  end
  
  lemma woarray_replicate_hnr[sepref_fr_rules]:
    fixes A :: "'a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn"
    assumes "GEN_ALGO x (is_init' A)"
    shows "(woarray_new TYPE('c), RETURN o PR_CONST (op_woarray_replicate x)) \<in> snat_assn\<^sup>k \<rightarrow>\<^sub>a woarray_assn A"
  proof -
  
    from assms have A[intro!]: "\<box> \<turnstile> A x init"
      by (simp add: GEN_ALGO_def is_init'_def)
    
    show ?thesis  
      unfolding snat_rel_def snat.assn_is_rel[symmetric]
      apply sepref_to_hoare
      apply vcg
      done
      
  qed
  
  
  
  
  
  subsubsection \<open>Free\<close>

  
  lemma eoarray_free_empty_rl[vcg_rules]: "llvm_htriple (eoarray_assn A xs xsi ** \<up>(set xs\<subseteq>{None})) (narray_free xsi) (\<lambda>_. \<box>)"
    unfolding eoarray_assn_def Proto_EOArray.nao_assn_def
    supply [simp] = list_assn_None_emp_eq
    by vcg

  (* Free if no elements owned *)    
  definition "mop_eoarray_free_empty xs \<equiv> doN {
    ASSERT (set xs \<subseteq> {None});
    RETURN ()
  }"
      
  sepref_register "mop_eoarray_free_empty"
  
  lemma mop_eoarray_free_empty_hnr[sepref_fr_rules]: 
    "(narray_free,mop_eoarray_free_empty) \<in> (eoarray_assn A)\<^sup>d \<rightarrow>\<^sub>a unit_assn"
    unfolding mop_eoarray_free_empty_def
    apply sepref_to_hoare
    apply (simp add: refine_pw_simps)
    by vcg
  
  lemma mop_eoarray_free_empty_rule[refine_vcg]: 
    "set xs \<subseteq> {None} \<Longrightarrow> mop_eoarray_free_empty xs \<le> SPEC (\<lambda>_. True)"  
    unfolding mop_eoarray_free_empty_def
    apply refine_vcg
    by auto
    
  (* Deep-Free wo-array *)    
  definition "mop_woarray_free l xs \<equiv> doN {
    ASSERT (l=length xs);
    xs \<leftarrow> mop_to_eo_conv xs;
  
    (_,xs) \<leftarrow> WHILEIT (\<lambda>(i,xs'). i\<le>l \<and> xs' = replicate i None @ drop i xs) 
      (\<lambda>(i,xs). i<l) (\<lambda>(i,xs). doN {
      (vi,xs) \<leftarrow> mop_eo_extract xs i;
      mop_free vi;
      ASSERT (i+1\<le>l);
      RETURN (i+1,xs)
    }) (0,xs);
    
    mop_eoarray_free_empty xs
  }"
    
  
  lemma mop_woarray_free_rl[refine_vcg]: "l=length xs \<Longrightarrow> mop_woarray_free l xs \<le> SPEC (\<lambda>_. True)"
    unfolding mop_woarray_free_def mop_free_def
    apply simp
    thm WHILEIT_rule
    apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(i,_). length xs - i)"])
    apply (simp_all add: nth_append)
    apply (clarsimp simp: list_update_append drop_upd_first replicate_append_same)
    by fastforce
    
  
  context
    fixes A :: "'a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn" and freeA
    assumes [sepref_frame_free_rules]: "MK_FREE A freeA"
  begin  
    
  sepref_definition woarray_free_impl_aux is "uncurry mop_woarray_free" :: "size_assn\<^sup>k *\<^sub>a (woarray_assn A)\<^sup>d \<rightarrow>\<^sub>a unit_assn"
    unfolding mop_woarray_free_def
    apply (annot_snat_const size_T)
    by sepref
    
  end  
  
  sepref_register mop_woarray_free
  
  concrete_definition woarray_free_impl [llvm_code] is woarray_free_impl_aux_def
  
  context
    fixes A :: "'a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn" and freeA
    assumes F: "MK_FREE A freeA"
  begin  
  
    lemmas woarray_free_impl_hnr[sepref_fr_rules] = woarray_free_impl_aux.refine[OF F, unfolded woarray_free_impl.refine[OF F]]
  end
  

  subsubsection \<open>Grow and Ensure-Capacity\<close>

  
  definition "wo_grow xinit l xs nsz \<equiv> doN {
    ASSERT (length xs \<le> nsz);
    ASSERT (l = length xs);
    
    xs \<leftarrow> mop_to_eo_conv xs;
    
    let ys = op_woarray_replicate xinit nsz; \<^cancel>\<open>Assertion annotation to be inserted only upon refinement\<close>
    ys \<leftarrow> mop_to_eo_conv ys;
    
    (_,xs,ys)\<leftarrow>WHILEIT (\<lambda>(i,xs',ys'). i\<le>l \<and> xs' = replicate i None @ drop i xs \<and> ys' = take i xs @ replicate (nsz-i) (Some xinit)) 
      (\<lambda>(i,xs,ys). i<l) 
      (\<lambda>(i,xs,ys). doN {
        (x,xs) \<leftarrow> mop_eo_extract xs i;
        (y,ys) \<leftarrow> mop_eo_extract ys i;  
        mop_free_dflt xinit y;
        
        ys \<leftarrow> mop_eo_set ys i x;
        ASSERT (i+1\<le>l);
        RETURN (i+1,xs,ys)
      }) (0,xs,ys);
  
    mop_eoarray_free_empty xs;
    
    ys \<leftarrow> mop_to_wo_conv ys;
      
    RETURN ys
  }"  
    
  
  definition "wo_ensure_capacity xinit l xs i \<equiv> doN {
    if i<l then
      RETURN (l,xs)
    else if l \<ge> max_size_incl div 2 then doN {
      let l' = i+1;
      xs \<leftarrow> wo_grow xinit l xs l';
      RETURN (l',xs)
    } else doN {
      ASSERT (2*l < max_size);
      let l' = max (2*l) (i+1);
      xs \<leftarrow> wo_grow xinit l xs l';
      RETURN (l',xs)
    }
  }"
  
  
  lemma wo_grow_rule[refine_vcg]: "\<lbrakk>l=length xs; length xs \<le> nsz\<rbrakk> \<Longrightarrow> wo_grow xinit l xs nsz \<le> SPEC (\<lambda>ys. ys = xs @ replicate (nsz - length xs) xinit)"
    unfolding wo_grow_def mop_to_eo_conv_def
    apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(i,_,_). l-i)"])
    apply (auto simp: nth_append replicate_append_same upd_conv_take_nth_drop take_Suc_conv_app_nth)
    done
  
  lemma wo_ensure_capacity_rule[refine_vcg]: "\<lbrakk> l = length xs \<rbrakk> \<Longrightarrow> wo_ensure_capacity xinit l xs i 
    \<le> SPEC (\<lambda>(l',ys). length xs \<le> length ys \<and> i<length ys \<and>l'=length ys \<and> (\<forall>j\<in>{0..<length xs}. ys!j=xs!j) \<and> (\<forall>j\<in>{length xs..<length ys}. ys!j=xinit))"
    unfolding wo_ensure_capacity_def
    apply refine_vcg
    by (auto simp: nth_append)
    
    
    
    
    
  context fixes xinit begin
    sepref_register "wo_grow xinit" "wo_ensure_capacity xinit"
  end  
  
    
  context
    fixes A :: "'a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn" and xinit
    assumes IEQ[sepref_gen_algo_rules]: "GEN_ALGO xinit (is_init_eq A)"
    
    notes [sepref_gen_algo_rules] = is_init_eq_imp_init'_GA
    
  begin
  
    sepref_definition wo_grow_impl_aux is "uncurry2 (PR_CONST (wo_grow xinit))" :: "size_assn\<^sup>k *\<^sub>a (woarray_assn A)\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a woarray_assn A"
      unfolding wo_grow_def PR_CONST_def
      apply (annot_snat_const size_T)
      by sepref
  
  end
    
  concrete_definition wo_grow_impl [llvm_code] is wo_grow_impl_aux_def
  
  
  context
    fixes A :: "'a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn" and xinit
    assumes IEQ: "GEN_ALGO xinit (is_init_eq A)"
  begin
    lemmas wo_grow_impl_hnr[sepref_fr_rules] = wo_grow_impl_aux.refine[OF IEQ, unfolded wo_grow_impl.refine[OF IEQ]]
  
    
    sepref_definition wo_ensure_capacity_impl_aux is "uncurry2 (PR_CONST (wo_ensure_capacity xinit))" 
      :: "[\<lambda>((l,xs),i). i<max_size_incl]\<^sub>a size_assn\<^sup>k *\<^sub>a (woarray_assn A)\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> size_assn \<times>\<^sub>a woarray_assn A"
      unfolding wo_ensure_capacity_def PR_CONST_def max_def
      apply (annot_snat_const size_T)
      by sepref
    
    
  end
  
  concrete_definition wo_ensure_capacity_impl [llvm_code,llvm_inline] is wo_ensure_capacity_impl_aux_def
  
  context
    fixes A :: "'a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn" and xinit
    assumes IEQ: "GEN_ALGO xinit (is_init_eq A)"
  begin
    lemmas wo_ensure_capacity_impl_hnr[sepref_fr_rules] = wo_ensure_capacity_impl_aux.refine[OF IEQ, unfolded wo_ensure_capacity_impl.refine[OF IEQ]]
  
  end
    
  
  subsubsection \<open>Exchange\<close>
  
  (* Move element to index, and return element that was at this index *)
  definition "mop_wo_exchange xs i v \<equiv> doN {
    xs \<leftarrow> mop_to_eo_conv xs;
  
    (r,xs) \<leftarrow> mop_eo_extract xs i;
    xs \<leftarrow> mop_eo_set xs i v;
    
    xs \<leftarrow> mop_to_wo_conv xs;
    
    RETURN (r,xs)
  }"
  
  lemma mop_wo_exchange_rule[refine_vcg]: "i<length xs \<Longrightarrow> mop_wo_exchange xs i v \<le> SPEC (\<lambda>(r,xs'). r=xs!i \<and> xs'=xs[i:=v] )"
    unfolding mop_wo_exchange_def
    apply simp
    apply refine_vcg
    subgoal by (metis ex_map_conv map_update option.distinct(1))
    by (auto simp: map_update)
    
  sepref_register mop_wo_exchange  
    
  sepref_def wo_exchange_impl [llvm_inline] is "uncurry2 mop_wo_exchange" :: "(woarray_assn A)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a A\<^sup>d \<rightarrow>\<^sub>a A \<times>\<^sub>a woarray_assn A"  
    unfolding mop_wo_exchange_def
    by sepref
  
  
  subsubsection \<open>With-Element\<close>    
  
  definition "eo_with f xs i \<equiv> doN {
    ASSERT (i<length xs \<and> xs!i\<noteq>None);
    f (the (xs!i))
  }"
    
  
  definition [llvm_inline]: "eo_with_impl fi xsi ii \<equiv> doM {
    x \<leftarrow> array_nth xsi ii;
    fi x
  }"
  
  
  (* Monadifier setup *)
  lemma eo_with_arity[sepref_monadify_arity]: "eo_with \<equiv> \<lambda>\<^sub>2f xs n. SP eo_with$(\<lambda>\<^sub>2x. f$x)$xs$n"
    by simp
  
  lemma eo_with_comb[sepref_monadify_comb]:  
    "eo_with$f$xs$n = Refine_Basic.bind$(EVAL$xs)$(\<lambda>\<^sub>2xs. Refine_Basic.bind$(EVAL$n)$(\<lambda>\<^sub>2n. SP eo_with$f$xs$n))"
    by simp
  
  
  
  lemma eo_with_impl_hnr_aux_old:
    assumes FI: "(fi,f) \<in> A\<^sup>k \<rightarrow>\<^sub>a R"
    shows "(uncurry (eo_with_impl fi), uncurry (PR_CONST (eo_with f))) \<in> (eoarray_assn A)\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a R"
  proof -
  
    note [vcg_rules] = FI[to_hnr, THEN hn_refineD, unfolded hn_ctxt_def, simplified]
  
    show ?thesis  
      unfolding snat_rel_def snat.assn_is_rel[symmetric] eo_with_impl_def eo_with_def
      apply sepref_to_hoare
      unfolding eoarray_assn_def Proto_EOArray.nao_assn_def
      supply [simp] = refine_pw_simps
      supply [simp] = lo_extract_elem
      by vcg
  
  qed
  
  
  lemma eo_with_impl_hnr_aux:
    assumes FI: "\<And>x xi. hn_refine (hn_ctxt A x xi ** hn_ctxt size_assn i ii ** F) (fi xi) (hn_ctxt  A x xi ** hn_ctxt size_assn i ii ** F') R (\<lambda>_. True) (f x)"
    shows "hn_refine (hn_ctxt (eoarray_assn A) xs xsi ** hn_ctxt size_assn i ii ** F) (eo_with_impl fi xsi ii) (hn_ctxt (eoarray_assn A) xs xsi ** hn_ctxt size_assn i ii ** F') R (\<lambda>_. True) (eo_with f xs i)"
  proof -
  
    note [vcg_rules] = FI[THEN hn_refineD, unfolded hn_ctxt_def snat_rel_def snat.assn_is_rel[symmetric], simplified]
  
    show ?thesis  
      unfolding snat_rel_def snat.assn_is_rel[symmetric] eo_with_impl_def eo_with_def
      apply sepref_to_hoare
      unfolding eoarray_assn_def Proto_EOArray.nao_assn_def
      supply [simp] = refine_pw_simps
      supply [simp] = lo_extract_elem
      apply vcg
      done
  qed
  
  lemma eo_with_hnr[sepref_comb_rules]:
    assumes FR1: "\<Gamma> \<turnstile> hn_ctxt (eoarray_assn A) xs xsi ** hn_ctxt size_assn i ii ** \<Gamma>\<^sub>1"
    assumes FI_RL: "\<And>x xi. hn_refine (hn_ctxt A x xi ** hn_ctxt size_assn i ii ** \<Gamma>\<^sub>1) (fi xi) (\<Gamma>\<^sub>2 x xi) R (CP\<^sub>2 x xi) (f x)"
    assumes FR2: "\<And>x xi. \<Gamma>\<^sub>2 x xi \<turnstile> hn_ctxt A x xi ** hn_ctxt size_assn i ii ** \<Gamma>\<^sub>3"
    
    shows "hn_refine \<Gamma> (eo_with_impl fi xsi ii) (hn_ctxt (eoarray_assn A) xs xsi ** hn_ctxt size_assn i ii ** \<Gamma>\<^sub>3) R (\<lambda>_. True) (eo_with$(\<lambda>\<^sub>2x. f x)$xs$i)"
  
  proof -
  
    note R[vcg_rules] = FI_RL[THEN hn_refineD]
  
    show ?thesis
      unfolding autoref_tag_defs PROTECT2_def
      apply (rule hn_refine_cons_post)
  
      
      apply (rule hn_refine_cons_pre)
      apply (rule FR1)
      
      apply (rule eo_with_impl_hnr_aux)
      apply (rule hn_refine_cons_cp[OF entails_refl])
      apply (rule FI_RL)
      apply (sep_drule FR2, fri)
      apply simp
      apply simp
      apply fri
      done
  qed    
      
    
  subsubsection \<open>Test\<close>    
  
  experiment
  begin
  
  term wo_grow_impl
  
  definition wo_grow_impl_test :: "64 word \<Rightarrow> 32 word ptr \<Rightarrow> 64 word \<Rightarrow> 32 word ptr llM" where [llvm_code]: "wo_grow_impl_test \<equiv> wo_grow_impl"
  
  definition wo_ensure_capacity_impl_test :: "64 word \<Rightarrow> 32 word ptr \<Rightarrow> 64 word \<Rightarrow> (64 word \<times> 32 word ptr) llM" where [llvm_code]: "wo_ensure_capacity_impl_test \<equiv> wo_ensure_capacity_impl"
  
  export_llvm wo_grow_impl_test wo_ensure_capacity_impl_test
  
  end
  
  
  
  
    


end
