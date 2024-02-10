theory Unsigned_Literal
imports SAT_Basic LRAT_Sepref_Base
begin

  (* TODO: Move *)    
  lemma even_bitwise: "even l \<longleftrightarrow> (l AND 0x1) = 0" for l :: nat by auto
  lemma odd_pred_div_eq: "odd l \<Longrightarrow> (l - Suc 0) div 2 = l div 2" by presburger
  



  subsection \<open>Positive Natural Numbers\<close>

  text \<open>Variables in DIMACs are positive natural numbers\<close>
  
  typedef dimacs_var = "{v::nat. v\<noteq>0}" morphisms nat_of_var var_of_nat
    by blast

  type_synonym dv_lit = "dimacs_var literal"  
  type_synonym dv_clause = "dimacs_var clause"  
  type_synonym dv_cnf = "dimacs_var cnf"  
    
  lemmas [simp] = nat_of_var_inverse nat_of_var_inject 
    
  lemma var_of_nat_inverse'[simp]: "x\<noteq>0 \<Longrightarrow> nat_of_var (var_of_nat x) = x"
    using var_of_nat_inverse by auto

  lemma var_of_nat_inj[simp]: "\<lbrakk>x\<noteq>0; x'\<noteq>0\<rbrakk> \<Longrightarrow> var_of_nat x = var_of_nat x' \<longleftrightarrow> x=x'"
    by (metis var_of_nat_inverse')  
    
  lemma nat_of_var'[simp]: 
    "nat_of_var x \<noteq> 0" 
    "Suc 0 \<le> nat_of_var x" 
    "0 < nat_of_var x" 
    using Suc_le_eq nat_of_var by auto
      

  subsection \<open>Unsigned Encoding\<close>
  text \<open>
    The lowest bit is the polarity, 0 for positive, 1 for negated. 
    The higher bits encode the variable index.
  \<close>  
        
  definition ulit_\<alpha> :: "nat \<Rightarrow> dimacs_var literal" where
    "ulit_\<alpha> n \<equiv> 
      if even n then Pos (var_of_nat (n div 2)) 
      else Neg (var_of_nat (n div 2))"  
    
  definition ulit_invar :: "nat \<Rightarrow> bool" where "ulit_invar n \<equiv> n\<ge>2" 
  
  definition "ulit_rel \<equiv> br ulit_\<alpha> ulit_invar"

  
  text \<open>
    To encode an optional literal, we use the unused value 0. Note that also the value 1 is unused. 
  \<close>
  definition ulito_\<alpha> :: "nat \<Rightarrow> dimacs_var literal option" where
    "ulito_\<alpha> n \<equiv> if n=0 then None else Some (ulit_\<alpha> n)"  
    
  definition ulito_invar :: "nat \<Rightarrow> bool" where "ulito_invar n \<equiv> n=0 \<or> ulit_invar n" 
  
  definition "ulito_rel \<equiv> br ulito_\<alpha> ulito_invar"
    
  lemma ulit_\<alpha>_inj[simp]: "\<lbrakk>ulit_invar n; ulit_invar n'\<rbrakk> \<Longrightarrow> ulit_\<alpha> n = ulit_\<alpha> n' \<longleftrightarrow> n=n'"
    unfolding ulit_\<alpha>_def ulit_invar_def apply auto
    using div2_even_ext_nat by presburger
  
  lemma ulito_\<alpha>_inj[simp]: "\<lbrakk>ulito_invar n; ulito_invar n'\<rbrakk> \<Longrightarrow> ulito_\<alpha> n = ulito_\<alpha> n' \<longleftrightarrow> n=n'"
    unfolding ulito_\<alpha>_def ulito_invar_def by auto

  subsection \<open>Operations on literals\<close>  

  subsubsection \<open>Constructing from nat\<close>
  definition mk_ulito :: "nat \<Rightarrow> dv_lit option nres" where "mk_ulito n \<equiv> do { ASSERT(n\<noteq>1); RETURN (ulito_\<alpha> n) }"
  
  lemmas mk_ulito_correct[refine_vcg] = vcg_of_RETURN[OF mk_ulito_def]

  lemma mk_ulito_refine: "(RETURN o id,mk_ulito) \<in> nat_rel \<rightarrow> \<langle>ulito_rel\<rangle>nres_rel"
    unfolding mk_ulito_def
    apply refine_vcg
    by (auto simp: ulito_rel_def in_br_conv ulito_invar_def ulit_invar_def)
  
    
  subsubsection \<open>Negation\<close>    
  definition ulit_neg :: "nat \<Rightarrow> nat" where "ulit_neg l \<equiv> (if even l then l+1 else l-1)"

  lemma ulit_neg_alt: "ulit_neg l = l XOR 0x1"
    unfolding ulit_neg_def
    by (auto simp: xor_Suc_0_eq)
  
  lemma ulit_neg_correct[simp]: 
    "ulit_invar l \<Longrightarrow> ulit_invar (ulit_neg l)"
    "ulit_invar l \<Longrightarrow> ulit_\<alpha> (ulit_neg l) = neg_lit (ulit_\<alpha> l)"
    unfolding ulit_invar_def ulit_\<alpha>_def ulito_\<alpha>_def ulit_neg_def even_bitwise
    apply (auto simp: odd_pred_div_eq bitXOR_1_if_mod_2[simplified] simp flip: even_iff_mod_2_eq_zero)
    by presburger
  
  subsubsection \<open>Zero\<close>  

  definition ulito_zero :: "nat" where "ulito_zero \<equiv> 0"
  
  lemma ulito_zero_correct[simp]: 
    "ulito_invar ulito_zero"
    "ulito_\<alpha> ulito_zero = None"
    unfolding ulito_\<alpha>_def ulito_invar_def ulito_zero_def by auto
    
  definition ulito_is_zero :: "nat \<Rightarrow> bool" where "ulito_is_zero n \<equiv> n=0"      
    
  lemma ulito_is_zero_correct[simp]: 
    "ulito_invar x \<Longrightarrow> ulito_is_zero x = is_None (ulito_\<alpha> x)"
    unfolding ulito_\<alpha>_def ulito_invar_def ulito_is_zero_def by auto 

    
  text \<open>Tagging operation, to indicate that abstraction changes from ulito to ulit\<close>  
  definition ulito_the :: "nat \<Rightarrow> nat" where
    "ulito_the n = n"
    
  lemma ulito_the_correct[simp]:
    assumes "ulito_invar n" 
    assumes "\<not>is_None (ulito_\<alpha> n)" 
    shows 
      "ulit_invar (ulito_the n)"    
      "ulit_\<alpha> (ulito_the n) = the (ulito_\<alpha> n)"    
      using assms unfolding ulito_invar_def ulito_\<alpha>_def ulito_the_def
      by (auto split: if_splits)
    
      
  text \<open>Tagging operation, to indicate that abstraction changes from ulit to ulito\<close>  
  definition ulit_wrapo :: "nat \<Rightarrow> nat" where "ulit_wrapo n \<equiv> n"
      
  lemma ulit_wrapo_correct[simp]:
    assumes "ulit_invar l"
    shows 
      "ulito_invar (ulit_wrapo l)" 
      "ulito_\<alpha> (ulit_wrapo l) = Some (ulit_\<alpha> l)"
    using assms unfolding ulito_invar_def ulit_wrapo_def ulito_\<alpha>_def
    apply simp_all
    unfolding ulit_invar_def by auto

  subsection \<open>Concretization\<close>  
            
  (* Inverse function, to define assignment *)    
           
  fun ulit_of :: "dimacs_var literal \<Rightarrow> nat" where
    "ulit_of (Pos v) = 2 * nat_of_var v"  
  | "ulit_of (Neg v) = 2 * nat_of_var v + 1"  

  lemma ulit_of_inv[simp]:
    "ulit_invar (ulit_of l)"
    "ulit_\<alpha> (ulit_of l) = l"
    unfolding ulit_invar_def ulit_\<alpha>_def 
    by (cases l; auto; fail)+

  lemma ulit_of_gtZ: "0<ulit_of l"  
    by (cases l; auto)

  lemma ulit_of_inv'[simp]: "ulit_invar l \<Longrightarrow> ulit_of (ulit_\<alpha> l) = l"
    unfolding ulit_\<alpha>_def ulit_invar_def
    by auto
    
  lemma ulit_of_inj[simp]: "ulit_of l = ulit_of l' \<longleftrightarrow> l=l'"  
    apply (cases l; cases l'; simp)
    by presburger+
    
    
    
  fun ulito_of :: "dimacs_var literal option \<Rightarrow> nat" where
    "ulito_of None = 0"
  | "ulito_of (Some x) = ulit_of x"

  
  lemma ulito_of_inv[simp]:
    "ulito_invar (ulito_of l)"
    "ulito_\<alpha> (ulito_of l) = l"
    unfolding ulito_invar_def ulito_\<alpha>_def 
    apply (cases l; auto)
    by (cases l; auto simp: ulit_of_gtZ)

  lemma ulito_of_inv'[simp]: "ulito_invar l \<Longrightarrow> ulito_of (ulito_\<alpha> l) = l"
    unfolding ulito_invar_def ulito_\<alpha>_def 
    apply (cases l)
    by auto  

  lemma ulit_of_\<alpha>[simp]: "ulit_invar x \<Longrightarrow> ulit_of (ulit_\<alpha> x) = x"
    using ulit_\<alpha>_inj ulit_of_inv(1) ulit_of_inv(2) by blast
    

  
  subsection \<open>Range of Variables by Maximum Literal\<close>  
      

  text \<open>Adjust to next odd number, such that both polarities of any variable are covered\<close>  
  definition ulit_maxlit_adjust :: "nat \<Rightarrow> nat" where "ulit_maxlit_adjust ml \<equiv> if even ml then ml+1 else ml"

  lemma ulit_maxlit_adjust_alt: "ulit_maxlit_adjust ml = ml OR 0x1"
    unfolding ulit_maxlit_adjust_def 
    by (auto simp: or_Suc_0_eq)
  
  text \<open>Variables covered by given max-literal\<close>
  definition "maxlit_vdom ml \<equiv> { var_of_lit (ulit_\<alpha> l) | l. l\<le>ml \<and> ulit_invar l }"
  
  
  lemma 
    ulit_maxlit_adjust_correct[simp]:
      "ulit_invar (ulit_maxlit_adjust l) = ulit_invar l"
      "var_of_lit (ulit_\<alpha> (ulit_maxlit_adjust l)) = var_of_lit (ulit_\<alpha> l)"
      "odd (ulit_maxlit_adjust l)"
    and 
    ulit_maxlit_adjust_bounds:    
      "l \<le> ulit_maxlit_adjust l"
      "ulit_neg l \<le> ulit_maxlit_adjust l"
    unfolding ulit_maxlit_adjust_def ulit_invar_def ulit_\<alpha>_def ulit_neg_def
    by auto

  lemma in_maxlit_vdom_iff: "var_of_lit l \<in> maxlit_vdom ml \<longleftrightarrow> ulit_of l \<le> ulit_maxlit_adjust ml"
    unfolding maxlit_vdom_def ulit_maxlit_adjust_def ulit_\<alpha>_def ulit_invar_def
    apply (cases l; simp; intro conjI impI iffI)
    apply (auto 0 3 intro: 
      exI[where x="2 * nat_of_var _"]
      )
    by presburger  
        
  lemma maxlit_adjust_vdom[simp]: "maxlit_vdom (ulit_maxlit_adjust ml) = maxlit_vdom ml"
    unfolding maxlit_vdom_def
    unfolding ulit_maxlit_adjust_def
    apply (auto split: if_splits)
    subgoal for l
      apply (rule exI[where x="if even l then l else l-1"])
      unfolding ulit_\<alpha>_def ulit_invar_def
      apply (auto simp: odd_pred_div_eq)
      apply fastforce
      by presburger
    done    
        
  lemma maxlit_vdom_mono: "l\<le>l' \<Longrightarrow> maxlit_vdom l \<subseteq> maxlit_vdom l'"
    unfolding maxlit_vdom_def
    by auto

subsection \<open>Implementation\<close>    

sepref_def ulito_zero_impl [llvm_inline] is "uncurry0 (RETURN ulito_zero)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a lit_assn"
  unfolding ulito_zero_def
  apply (annot_unat_const "lit_size_T")
  by sepref

sepref_def ulito_is_zero_impl [llvm_inline] is "RETURN o ulito_is_zero" :: "lit_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding ulito_is_zero_def
  apply (annot_unat_const "lit_size_T")
  by sepref
  
  
sepref_def ulit_neg_impl [llvm_inline] is "RETURN o ulit_neg" :: "lit_assn\<^sup>k \<rightarrow>\<^sub>a lit_assn"
  unfolding ulit_neg_alt
  apply (annot_unat_const "lit_size_T")
  by sepref
    

sepref_def ulit_maxlit_adjust_impl [llvm_inline] is "RETURN o ulit_maxlit_adjust" :: "lit_assn\<^sup>k \<rightarrow>\<^sub>a lit_assn"
  unfolding ulit_maxlit_adjust_alt
  apply (annot_unat_const "lit_size_T")
  by sepref

sepref_register ulito_zero ulito_is_zero ulit_neg ulit_maxlit_adjust
  
  
text \<open>On this level, we make no distinction between literals and wrapped literals, 
  so we can simply unfold the coercion tagging constants\<close>  
lemmas [sepref_preproc] = ulito_the_def[abs_def] ulit_wrapo_def[abs_def]  
    
    














  definition "dimacs_var_rel \<equiv> (br var_of_nat ((\<noteq>)0))"
  definition "dimacs_var_assn_aux \<equiv> (b_assn (unat_assn' lit_size_T) (\<lambda>x. x<max_var))"
  definition "dimacs_var_assn \<equiv> hr_comp dimacs_var_assn_aux dimacs_var_rel"

  lemma dimacs_var_assn_is_pure[safe_constraint_rules, simp]: "is_pure dimacs_var_assn"
    unfolding dimacs_var_assn_def dimacs_var_assn_aux_def
    by solve_constraint

  lemmas [sepref_frame_free_rules] = mk_free_is_pure[OF dimacs_var_assn_is_pure]
    
  definition "mk_dimacs_var n \<equiv> doN {
    ASSERT (n\<noteq>0 \<and> n<max_var);
    RETURN (var_of_nat n)
  }"

  lemmas mk_dimacs_var_correct[refine_vcg] = vcg_of_RETURN[OF mk_dimacs_var_def]
  
  lemma mk_dimacs_var_refine: "(mk_dimacs_var,RETURN o var_of_nat) \<in> [\<lambda>n. n\<noteq>0 \<and> n<max_var]\<^sub>f nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
    apply (rule frefI)
    apply refine_vcg
    by auto
  
  definition "mk_dimacs_var1 n \<equiv> doN {
    ASSERT (n\<noteq>0 \<and> n<max_var);
    RETURN (op_snat_unat_downcast lit_size_T n)
  }"

  lemma mk_dimacs_var1_refine: "(mk_dimacs_var1, mk_dimacs_var) \<in> Id \<rightarrow> \<langle>dimacs_var_rel\<rangle>nres_rel"
    unfolding mk_dimacs_var_def mk_dimacs_var1_def dimacs_var_rel_def
    apply refine_vcg
    by (auto simp: in_br_conv)

    
  sepref_def mk_dimacs_var_impl [llvm_inline] is "mk_dimacs_var1" 
    :: "size_assn\<^sup>k \<rightarrow>\<^sub>a dimacs_var_assn_aux"
    supply [simp] = is_down'
    unfolding mk_dimacs_var1_def dimacs_var_assn_aux_def
    apply (rule hfref_bassn_resI)
    subgoal apply refine_vcg by auto
    by sepref
    
  
  term lit_assn
  
  definition "ulit_assn \<equiv> hr_comp lit_assn ulit_rel"
  lemma fold_ulit_assn: "pure (unat_rel O ulit_rel) = ulit_assn"
    unfolding ulit_assn_def
    by (simp add: hr_comp_pure)

  lemma ulit_assn_is_pure[safe_constraint_rules, simp]: "is_pure ulit_assn"
    unfolding ulit_assn_def
    by solve_constraint
    
  lemmas [sepref_frame_free_rules] = mk_free_is_pure[OF ulit_assn_is_pure]
      
  definition "ulit_mk_pos n \<equiv> 2*COPY n"
  definition "ulit_mk_neg n \<equiv> 2*COPY n + 1"

  lemma ulit_mk_pos_refine: "(ulit_mk_pos,Pos) \<in> dimacs_var_rel \<rightarrow> ulit_rel"
    unfolding ulit_mk_pos_def
    by (auto simp: dimacs_var_rel_def in_br_conv ulit_rel_def ulit_\<alpha>_def ulit_invar_def)

  lemma ulit_mk_neg_refine: "(ulit_mk_neg,Neg) \<in> dimacs_var_rel \<rightarrow> ulit_rel"
    unfolding ulit_mk_neg_def
    by (auto simp: dimacs_var_rel_def in_br_conv ulit_rel_def ulit_\<alpha>_def ulit_invar_def)
      
  sepref_def ulit_mk_pos_impl [llvm_inline] is "RETURN o ulit_mk_pos" :: "dimacs_var_assn_aux\<^sup>k \<rightarrow>\<^sub>a lit_assn"  
    unfolding ulit_mk_pos_def dimacs_var_assn_aux_def
    apply (annot_unat_const lit_size_T)
    by sepref
  
  sepref_def ulit_mk_neg_impl [llvm_inline] is "RETURN o ulit_mk_neg" :: "dimacs_var_assn_aux\<^sup>k \<rightarrow>\<^sub>a lit_assn"  
    unfolding ulit_mk_neg_def dimacs_var_assn_aux_def
    apply (annot_unat_const lit_size_T)
    by sepref

  lemma ulit_neg_refine: "(ulit_neg,neg_lit) \<in> ulit_rel \<rightarrow> ulit_rel"
    by (auto simp: ulit_rel_def in_br_conv)
      
    
  definition "ulito_assn \<equiv> hr_comp lit_assn ulito_rel"
  lemma fold_ulito_assn: "pure (unat_rel O ulito_rel) = ulito_assn"
    unfolding ulito_assn_def
    by (simp add: hr_comp_pure)

  lemma ulito_assn_is_pure[safe_constraint_rules, simp]: "is_pure ulito_assn"
    unfolding ulito_assn_def
    by solve_constraint
    
  lemmas [sepref_frame_free_rules] = mk_free_is_pure[OF ulito_assn_is_pure]

  definition ulito_None :: "_ literal option" where [simp]: "ulito_None \<equiv> None"
  lemmas fold_ulito_None = ulito_None_def[symmetric]
  
  sepref_register ulito_None
  
  lemma ulito_zero_refine: "(ulito_zero,ulito_None) \<in> ulito_rel"
    by (auto simp: ulito_rel_def in_br_conv)
  
      
  lemma ulito_is_zero_refine: "(ulito_is_zero,is_None) \<in> ulito_rel \<rightarrow> bool_rel"
    by (auto simp: ulito_rel_def in_br_conv)

    
  lemma ulito_the_refine: "(ulito_the,the) \<in> [\<lambda>x. \<not>is_None x]\<^sub>f ulito_rel \<rightarrow> ulit_rel"
    unfolding ulito_the_def ulito_rel_def ulit_rel_def
    apply (rule frefI)
    apply (clarsimp simp: in_br_conv)
    subgoal for x y
      using ulito_the_correct[of x]
      unfolding ulito_the_def 
      by auto
    done    
    
  sepref_def ulito_the_impl [llvm_inline] is "RETURN o ulito_the" :: "lit_assn\<^sup>k \<rightarrow>\<^sub>a lit_assn"
    unfolding ulito_the_def by sepref

  lemma ulit_wrapo_refine: "(ulit_wrapo,Some) \<in> ulit_rel \<rightarrow> ulito_rel"
    unfolding ulito_rel_def ulit_rel_def
    by (auto simp: in_br_conv)
    
  sepref_def ulit_wrapo_impl [llvm_inline] is "RETURN o ulit_wrapo" :: "lit_assn\<^sup>k \<rightarrow>\<^sub>a lit_assn"
    unfolding ulit_wrapo_def by sepref
           

        
  sepref_definition lit_id_impl [llvm_inline] is "RETURN o id" :: "lit_assn\<^sup>k \<rightarrow>\<^sub>a lit_assn"
    by sepref  

  (* definition ulit_of2 :: "nat \<Rightarrow> nat" where [simp]: "ulit_of2 x \<equiv> x" *)
  
  lemma ulit_of_refine: "(id, ulit_of) \<in> ulit_rel \<rightarrow> nat_rel"
    by (clarsimp simp: ulit_rel_def in_br_conv)  
    
  lemma ulito_of_refine: "(id, ulito_of) \<in> ulito_rel \<rightarrow> nat_rel"
    by (clarsimp simp: ulito_rel_def in_br_conv)  
    
        
  thm mk_ulito_refine  
    
    

  sepref_register var_of_nat mk_dimacs_var Pos Neg mk_ulito
  context
    notes [fcomp_norm_unfold] = dimacs_var_assn_def[symmetric] ulit_assn_def[symmetric] ulito_assn_def[symmetric] fold_ulit_assn fold_ulito_assn
  begin  
    lemmas mk_dimacs_var_hnr[sepref_fr_rules] = mk_dimacs_var_impl.refine[FCOMP mk_dimacs_var1_refine]    
    
    lemmas mk_dimacs_var_hnr'[sepref_fr_rules] = mk_dimacs_var_hnr[FCOMP mk_dimacs_var_refine]
    
    lemmas ulit_mk_pos_hnr[sepref_fr_rules] = ulit_mk_pos_impl.refine[FCOMP ulit_mk_pos_refine]
    lemmas ulit_mk_neg_hnr[sepref_fr_rules] = ulit_mk_neg_impl.refine[FCOMP ulit_mk_neg_refine]

    lemmas ulit_neg_hnr[sepref_fr_rules] = ulit_neg_impl.refine[FCOMP ulit_neg_refine]
    
    lemmas ulit_of_hnr[sepref_fr_rules] = lit_id_impl.refine[FCOMP ulit_of_refine]
        
    lemmas ulito_zero_hnr[sepref_fr_rules] = ulito_zero_impl.refine[FCOMP ulito_zero_refine]
    lemmas ulito_is_zero_hnr[sepref_fr_rules] = ulito_is_zero_impl.refine[FCOMP ulito_is_zero_refine]
    
    lemmas ulito_the_hnr[sepref_fr_rules] = ulito_the_impl.refine[FCOMP ulito_the_refine]
    lemmas ulit_wrapo_hnr[sepref_fr_rules] = ulit_wrapo_impl.refine[FCOMP ulit_wrapo_refine]
    
    lemmas ulito_of_hnr[sepref_fr_rules] = lit_id_impl.refine[FCOMP ulito_of_refine]

    lemmas mk_ulito_hnr[sepref_fr_rules] = lit_id_impl.refine[FCOMP mk_ulito_refine]
    
  end

    
  definition "some_var \<equiv> var_of_nat 1"
  definition "some_lit \<equiv> Pos some_var"

  sepref_register some_var some_lit 
  sepref_def some_var_impl [llvm_inline] is "uncurry0 (RETURN some_var)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a dimacs_var_assn"  
    unfolding some_var_def 
    apply (annot_snat_const size_T) 
    by sepref
        
  sepref_def some_lit_impl [llvm_inline] is "uncurry0 (RETURN some_lit)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a ulit_assn"  
    unfolding some_lit_def 
    by sepref
    

    

end
