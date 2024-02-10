theory Trailed_Assignment
imports Unsigned_Literal Relaxed_Assignment Sizes_Setup Proto_Sepref_Ghostvar
begin

(* TODO: Move *)
definition [llvm_inline]: "snat_even_impl w \<equiv> doM {
  b \<leftarrow> ll_and w (signed_nat 0x1);
  ll_icmp_eq b (signed_nat 0)
}"  
    
lemma snat_even_rule[vcg_rules]: "htriple (\<upharpoonleft>snat.assn n ni) (snat_even_impl ni) (\<lambda>ri. EXS r. \<upharpoonleft>bool.assn r ri ** \<up>(r = even n))"
  unfolding snat_even_impl_def
  apply vcg_monadify
  by vcg



text \<open>Assignment with rollback\<close>

  subsection \<open>Array of Boolean as Map\<close>
  definition "bla_\<alpha> xs i \<equiv> if i<length xs then xs!i else False"  
  
  definition "bla_get_checked xs i \<equiv> if i<length xs then xs!i else False"
  definition "bla_get_unchecked xs i \<equiv> mop_list_get xs i"

  definition "bla_set_unchecked xs i v \<equiv> mop_list_set xs i v"
  
  
  definition "bla_new_size csz i \<equiv> do {
    ASSERT(csz \<le> i);
    SPEC (\<lambda>ns. i<ns \<and> even ns)
  }"
  
  definition "bla_set_checked_aux xs i v \<equiv> do {
    len \<leftarrow> mop_list_length xs;
    ns \<leftarrow> bla_new_size len i;
    ASSERT(len<ns);
    let xs = op_list_grow_init False ns len xs;
    mop_list_set xs i v
  }"
  
  definition "bla_set_checked xs i v \<equiv> do {
    len \<leftarrow> mop_list_length xs;
    if i<len then mop_list_set xs i v
    else bla_set_checked_aux xs i v
  }"
  
  
  lemma bla_\<alpha>_empty[simp]: "bla_\<alpha> [] = (\<lambda>_. False)"
    unfolding bla_\<alpha>_def by auto
    
  lemma bla_init_correct[simp]: "bla_\<alpha> (replicate n False) = (\<lambda>_. False)"  
    unfolding bla_\<alpha>_def by auto
      
  lemma bla_get_checked_correct[simp]: "bla_get_checked xs i = bla_\<alpha> xs i"
    unfolding bla_\<alpha>_def bla_get_checked_def by auto
  
  lemma bla_get_unchecked_correct[refine_vcg]: "i<length xs \<Longrightarrow> bla_get_unchecked xs i \<le> SPEC (\<lambda>r. r=bla_\<alpha> xs i)"
    unfolding bla_\<alpha>_def bla_get_unchecked_def by auto
  

  lemma bla_set_unchecked_correct[refine_vcg]:
    "i<length xs \<Longrightarrow> bla_set_unchecked xs i v \<le> SPEC (\<lambda>xs'. length xs'=length xs \<and> bla_\<alpha> xs' = (bla_\<alpha> xs)(i:=v))"
    unfolding bla_\<alpha>_def bla_set_unchecked_def
    by (auto simp: fun_eq_iff)
    
  lemma bla_set_checked_aux_correct[refine_vcg]:
    "\<lbrakk>even (length xs); length xs \<le> i\<rbrakk> \<Longrightarrow> bla_set_checked_aux xs i v \<le> SPEC (\<lambda>xs'. 
        length xs \<le> length xs' 
      \<and> i<length xs' 
      \<and> even (length xs') 
      \<and> bla_\<alpha> xs' = (bla_\<alpha> xs)(i:=v))"  
    unfolding bla_set_checked_aux_def bla_new_size_def   
    apply refine_vcg
    unfolding bla_\<alpha>_def
    by (auto simp: fun_eq_iff nth_append)
    
  lemma bla_set_checked_correct[refine_vcg]:
    "even (length xs) \<Longrightarrow> bla_set_checked xs i v \<le> SPEC (\<lambda>xs'. 
        length xs \<le> length xs' 
      \<and> i<length xs' 
      \<and> even (length xs') 
      \<and> bla_\<alpha> xs' = (bla_\<alpha> xs)(i:=v))"  
    unfolding bla_set_checked_def    
    apply refine_vcg
    unfolding bla_\<alpha>_def
    by (auto simp: fun_eq_iff)

    
  subsection \<open>Assignment\<close>
  text \<open>The assignment contains the array, the trail, and a capacity bound that the trail is guaranteed to not exceed\<close>
      
  type_synonym rpan = "bool list \<times> nat list \<times> nat"
    
  definition rpan_\<alpha> :: "rpan \<Rightarrow> dimacs_var rp_ass" where "rpan_\<alpha> \<equiv> \<lambda>(A,_,_). bla_\<alpha> A o ulit_of"
  definition rpan_cap :: "rpan \<Rightarrow> nat" where "rpan_cap \<equiv> \<lambda>(_,tr,bnd). bnd - length tr"
  definition rpan_dom :: "rpan \<Rightarrow> dimacs_var set" where "rpan_dom \<equiv> \<lambda>(A,_,_). { var_of_lit (ulit_\<alpha> l) | l. l<length A \<and> ulit_invar l }"
  definition rpan_invar :: "rpan \<Rightarrow> bool" where 
    "rpan_invar \<equiv> \<lambda>(A,tr,bnd). 
        even (length A) 
      \<and> {x. bla_\<alpha> A x} \<subseteq> set tr 
      \<and> length tr\<le>bnd
      \<and> set tr \<subseteq> {0..<length A}
      "

  definition rpan_make :: "bool list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> rpan" where [simp]: "rpan_make A tr bnd \<equiv> (A,tr,bnd)"
  definition rpan_dest :: "rpan \<Rightarrow> _" where [simp]: "rpan_dest x \<equiv> x"

        
  definition rpan_empty :: "nat \<Rightarrow> nat \<Rightarrow> rpan" where 
    "rpan_empty maxlit cap \<equiv> rpan_make (replicate ((ulit_maxlit_adjust maxlit) + 1) False) [] cap"
    
  lemma rpan_empty_correct[simp]: 
    "rpan_invar (rpan_empty ml cap)"
    "rpan_\<alpha> (rpan_empty ml cap) = rpa_empty"
    "rpan_cap (rpan_empty ml cap) = cap"
    "rpan_dom (rpan_empty ml cap) = maxlit_vdom ml"
    unfolding rpan_empty_def rpan_\<alpha>_def rpan_cap_def rpan_dom_def rpan_invar_def 
    apply (clarsimp_all simp: comp_def simp del: replicate.simps) 
    
    apply (rule)
    
    subgoal by (auto simp: in_maxlit_vdom_iff)
    subgoal
      unfolding maxlit_vdom_def
      by (auto simp: ulit_maxlit_adjust_def)
    done
      
    
  definition rpan_is_true_checked :: "rpan \<Rightarrow> dimacs_var literal \<Rightarrow> bool" where "rpan_is_true_checked rp x \<equiv> let (A,_,_) = rpan_dest rp in bla_get_checked A (ulit_of x)"
  definition rpan_is_true_unchecked :: "rpan \<Rightarrow> dimacs_var literal \<Rightarrow> bool nres" where "rpan_is_true_unchecked rp x \<equiv> let (A,_,_) = rpan_dest rp in bla_get_unchecked A (ulit_of x)"
  abbreviation "rpan_is_false_checked A x \<equiv> rpan_is_true_checked A (neg_lit x)"
  abbreviation "rpan_is_false_unchecked A x \<equiv> rpan_is_true_unchecked A (neg_lit x)"
  
  lemma rpan_is_true_checked_refine[simp]: "rpan_is_true_checked A x = is_true (rpan_\<alpha> A) x"
    unfolding rpan_is_true_checked_def is_true_def rpan_\<alpha>_def 
    by auto
    
  lemma var_of_lit_eq_cases[consumes 1]:
    assumes "var_of_lit l = var_of_lit l'"
    obtains (eq) "l=l'" | (neg) "l = neg_lit l'"
    using assms apply (cases l; cases l') by auto
  
    
  lemma even_lit_bound_conv: "\<lbrakk>even n; ulit_invar l; ulit_invar l'; ulit_\<alpha> l = neg_lit (ulit_\<alpha> l')\<rbrakk> \<Longrightarrow> l'<n \<longleftrightarrow> l<n"
    unfolding ulit_\<alpha>_def ulit_invar_def
    by (fastforce split: if_splits)
    
    
    
  lemma rpan_is_true_unchecked_refine[refine_vcg]: 
    "\<lbrakk>rpan_invar A; var_of_lit x\<in>rpan_dom A \<rbrakk> \<Longrightarrow> rpan_is_true_unchecked A x \<le> SPEC (\<lambda>r. r= is_true (rpan_\<alpha> A) x)"
    unfolding rpan_is_true_unchecked_def 
    apply refine_vcg
    unfolding rpan_invar_def rpan_\<alpha>_def is_true_def rpan_dom_def
    by (auto elim!: var_of_lit_eq_cases simp: even_lit_bound_conv)
    
    
  definition rpan_set_checked :: "rpan \<Rightarrow> dimacs_var literal \<Rightarrow> rpan nres" where 
    "rpan_set_checked \<equiv> \<lambda>rp l. do {
      let (A,tr,bnd) = rpan_dest rp; 
      let l = ulit_of l;
      A \<leftarrow> bla_set_checked A l True;
      ASSERT (length tr < bnd);
      tr \<leftarrow> mop_list_append tr l;
      RETURN (rpan_make A tr bnd)}"
      
  definition rpan_set_unchecked :: "rpan \<Rightarrow> dimacs_var literal \<Rightarrow> rpan nres" where 
    "rpan_set_unchecked \<equiv> \<lambda>rp l. do {
      let l = ulit_of l;
      let (A,tr,bnd) = rpan_dest rp; 
      A \<leftarrow> bla_set_unchecked A l True;
      ASSERT (length tr < bnd);
      tr \<leftarrow> mop_list_append tr l;
      RETURN (rpan_make A tr bnd)}"

  lemma rpan_set_checked_correct[refine_vcg]:
    assumes "rpan_invar A" "rpan_cap A \<noteq> 0"
    shows 
      "rpan_set_checked A l \<le> SPEC (\<lambda>r. 
          rpan_invar r 
        \<and> rpan_\<alpha> r = (rpan_\<alpha> A)(l:=True) 
        \<and> rpan_cap r = rpan_cap A - 1
        \<and> insert (var_of_lit (l)) (rpan_dom A) \<subseteq> rpan_dom r
      )"
    unfolding rpan_set_checked_def
    apply refine_vcg
    using assms unfolding rpan_invar_def rpan_\<alpha>_def rpan_cap_def rpan_dom_def
    by (auto simp: fun_eq_iff intro: exI[where x="ulit_of l"])      

  lemma rpan_set_unchecked_correct[refine_vcg]:
    assumes "rpan_invar A" "rpan_cap A \<noteq> 0" "var_of_lit l \<in> rpan_dom A"
    shows 
      "rpan_set_unchecked A l \<le> SPEC (\<lambda>r. 
          rpan_invar r 
        \<and> rpan_\<alpha> r = (rpan_\<alpha> A)(l:=True) 
        \<and> rpan_cap r = rpan_cap A - 1
        \<and> rpan_dom r = rpan_dom A 
      )"
    unfolding rpan_set_unchecked_def
    apply refine_vcg
    using assms unfolding rpan_invar_def rpan_\<alpha>_def rpan_cap_def rpan_dom_def
    by (auto simp: fun_eq_iff even_lit_bound_conv elim: var_of_lit_eq_cases)
                  
  definition rpan_clear :: "nat \<Rightarrow> rpan \<Rightarrow> rpan nres" where "rpan_clear cap rp \<equiv> do {
    let (A,tr,_) = rpan_dest rp;
    A \<leftarrow> nfoldli tr (\<lambda>_. True) (\<lambda>l A. bla_set_unchecked A l False) A;
    tr \<leftarrow> mop_emptied_list tr;
    RETURN (rpan_make A tr cap)
  }"
    
  lemma rpan_clear_correct[refine_vcg]: 
    assumes "rpan_invar A\<^sub>0"
    shows "rpan_clear cap A\<^sub>0 \<le> SPEC (\<lambda>A. 
        rpan_invar A 
      \<and> rpan_\<alpha> A = rpa_empty 
      \<and> rpan_cap A = cap
      \<and> rpan_dom A = rpan_dom A\<^sub>0
      )"
    apply (cases A\<^sub>0)
    subgoal for bla\<^sub>0 tr\<^sub>0 bnd\<^sub>0
      using assms unfolding rpan_clear_def
      apply (refine_vcg nfoldli_rule[where I="\<lambda>_ it A. {x. bla_\<alpha> A x} \<subseteq> set it \<and> set it \<subseteq> {0..<length A} \<and> length A = length bla\<^sub>0"])
      by (auto simp: rpan_invar_def rpan_\<alpha>_def rpan_cap_def rpan_dom_def)
    done  







  definition bla_new_size_aux_impl :: "size_t word \<Rightarrow> lit_size_t word \<Rightarrow> size_t word llM" 
  where [llvm_inline]:   
    "bla_new_size_aux_impl n i \<equiv> doM {
      \<comment> \<open>Maximum sensible length\<close>
      max::lit_size_t word \<leftarrow> ll_max_unat;
      max \<leftarrow> unat_snat_upcast size_T max;
      max \<leftarrow> ll_add max (signed_nat 1);
      
      \<comment> \<open>New length from current size\<close>
      ns \<leftarrow> ll_mul n (signed_nat 3);
      ns \<leftarrow> ll_udiv n (signed_nat 2);
      
      do_max \<leftarrow> ll_icmp_sle max ns;
      llc_if do_max (doM {
        Mreturn max
      }) (doM {
        \<comment> \<open>New length required from index\<close>
        ns'::size_t word \<leftarrow> unat_snat_upcast size_T i;
        ns' \<leftarrow> ll_add ns' (signed_nat 1);
        
        take_ns \<leftarrow> ll_icmp_sle ns' ns;
        llc_if take_ns (Mreturn ns) (Mreturn ns')
      })
    }"

  
  lemma bla_new_size_aux_impl_rule[vcg_rules]: 
    "llvm_htriple 
      (\<upharpoonleft>snat.assn n ni ** \<upharpoonleft>unat.assn i ii ** \<up>(n \<le> i)) 
      (bla_new_size_aux_impl ni ii)
      (\<lambda>ri. EXS r. \<upharpoonleft>snat.assn r ri ** \<up>(i<r \<and> r\<le>max_lit))"  
    unfolding bla_new_size_aux_impl_def
    apply (vcg_monadify)
    apply vcg'
    apply clarsimp_all
    unfolding max_snat_def max_unat_def    
    apply (simp_all add: is_up')
    done
    
  
      
  definition [llvm_inline]: "bla_new_size_impl n i \<equiv> doM {
    ns \<leftarrow> bla_new_size_aux_impl n i;
    b \<leftarrow> snat_even_impl ns;
    llc_if b (Mreturn ns) (ll_add ns (signed_nat 1))
  }"
    
            
    
  sepref_register bla_new_size
  lemma bla_new_size_impl_refine[sepref_fr_rules]: 
    "(uncurry bla_new_size_impl, uncurry bla_new_size)
    \<in> size_assn\<^sup>k *\<^sub>a lit_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  proof -
  
  
    show ?thesis  
      unfolding bla_new_size_def bla_new_size_impl_def
      apply sepref_to_hoare
      unfolding in_snat_rel_conv_assn in_unat_rel_conv_assn
      supply [simp] = refine_pw_simps
      
      apply vcg_monadify
      apply vcg'
      
      by (auto simp: max_unat_def max_snat_def)

  qed    
    
    
  
  type_synonym blai = "(1 word, size_t)larray"
  
  abbreviation bla_assn :: "bool list \<Rightarrow> blai \<Rightarrow> assn" where "bla_assn \<equiv> larray_assn' size_T bool1_assn"
  
  sepref_register bla_get_checked bla_get_unchecked bla_set_unchecked bla_set_checked
  
  sepref_def bla_get_checked_impl is "uncurry (RETURN oo bla_get_checked)" :: "bla_assn\<^sup>k *\<^sub>a lit_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding bla_get_checked_def
    
    apply (rewrite at "if \<hole> < _ then _ else _" annot_unat_snat_upcast[where 'l=size_t])
    apply (rewrite at "_!\<hole>" annot_unat_snat_upcast[where 'l=size_t])
    supply [simp] = is_up'
    by sepref
    
  lemma bla_get_unchecked_alt: "bla_get_unchecked xs i = mop_list_get xs (op_unat_snat_upcast TYPE(size_t) i)"  
    unfolding bla_get_unchecked_def by simp
    
  lemma bla_set_unchecked_alt: "bla_set_unchecked xs i v = mop_list_set xs (op_unat_snat_upcast TYPE(size_t) i) v"  
    unfolding bla_set_unchecked_def by simp
    
  sepref_def bla_get_unchecked_impl [llvm_inline] is "uncurry (bla_get_unchecked)" :: "bla_assn\<^sup>k *\<^sub>a lit_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding bla_get_unchecked_alt
    supply [simp] = is_up'
    by sepref
    
    
  sepref_def bla_set_unchecked_impl [llvm_inline] is "uncurry2 (bla_set_unchecked)" :: "bla_assn\<^sup>d *\<^sub>a lit_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a bla_assn"
    unfolding bla_set_unchecked_alt
    supply [simp] = is_up'
    by sepref
  
    
  sepref_def bla_set_checked_aux_impl is "uncurry2 (bla_set_checked_aux)" :: "bla_assn\<^sup>d *\<^sub>a lit_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a bla_assn"
    unfolding bla_set_checked_aux_def
    apply (rewrite at "mop_list_set _ \<hole>" annot_unat_snat_upcast[where 'l=size_t])
    supply [simp] = is_up'
    by sepref
  
  sepref_def bla_set_checked_impl [llvm_inline] is "uncurry2 (bla_set_checked)" :: "bla_assn\<^sup>d *\<^sub>a lit_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a bla_assn"
    unfolding bla_set_checked_def
    apply (rewrite at "if \<hole> < _ then _ else _" annot_unat_snat_upcast[where 'l=size_t])
    apply (rewrite at "mop_list_set _ \<hole>" annot_unat_snat_upcast[where 'l=size_t])
    supply [simp] = is_up'
    by sepref


    
    
    
    
    
    
        
  term rpan_empty  
  
  term arl_assn
    
  lemma rpan_empty_alt: "rpan_empty ml cap = do {
    let ml = ulit_maxlit_adjust ml;
    let n = op_unat_snat_upcast TYPE(size_t) ml;
    let n=n+1;
    
    rpan_make (replicate n False) [] cap  
  }"
    unfolding rpan_empty_def
    by (auto)
    
  sepref_register rpan_make rpan_dest rpan_empty rpan_is_true_unchecked rpan_set_checked rpan_set_unchecked rpan_clear

  
  type_synonym rpani = "blai \<times> (lit_size_t word, size_t) array_list"  

  definition rpan_assn :: "rpan \<Rightarrow> rpani \<Rightarrow> assn" 
    where "rpan_assn \<equiv> \<lambda>(A,tr,bnd) (Ai,tri). bla_assn A Ai ** al_assn' size_T lit_assn tr tri ** dropi_assn (rdomp size_assn) bnd ghost_var"
  
  
  definition rpan_make_impl :: "_ \<Rightarrow> _ \<Rightarrow> 'a \<Rightarrow> rpani llM" 
    where [llvm_inline]: "rpan_make_impl Ai tri _ \<equiv> Mreturn (Ai,tri)"
  

  lemma rpan_make_impl_refine[sepref_fr_rules]: 
    "(uncurry2 rpan_make_impl,uncurry2 (RETURN ooo rpan_make)) 
    \<in> [\<lambda>_. True]\<^sub>c bla_assn\<^sup>d *\<^sub>a (al_assn lit_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> rpan_assn [\<lambda>((Ai,tri),_) r. r = (Ai,tri) ]\<^sub>c"
    unfolding rpan_make_def rpan_make_impl_def rpan_assn_def any_rel_def
    apply sepref_to_hoare
    apply vcg_normalize
    
    apply (simp named_ss HOL_basic_ss_nomatch: move_resolve_ex_eq)
    
    supply [simp] = rdomp_pure_rel_eq
    apply vcg
    done    

    
  lemma rpan_make_impl_refine2[sepref_fr_rules]: 
    "(uncurry2 rpan_make_impl,uncurry2 (RETURN ooo rpan_make)) 
    \<in> [\<lambda>_. True]\<^sub>c bla_assn\<^sup>d *\<^sub>a (al_assn lit_assn)\<^sup>d *\<^sub>a (dropi_assn (rdomp size_assn))\<^sup>k \<rightarrow> rpan_assn [\<lambda>((Ai,tri),_) r. r = (Ai,tri) ]\<^sub>c"
    unfolding rpan_make_def rpan_make_impl_def rpan_assn_def any_rel_def
    apply sepref_to_hoare
    apply vcg_normalize
    
    apply (simp named_ss HOL_basic_ss_nomatch: move_resolve_ex_eq)
    by vcg
  
    
  lemma rpan_dest_impl_refine[sepref_fr_rules]: 
    "(\<lambda>(a,b). Mreturn (a,b,ghost_var::1 word), RETURN o rpan_dest) 
    \<in> [\<lambda>_. True]\<^sub>c rpan_assn\<^sup>d \<rightarrow> bla_assn \<times>\<^sub>a al_assn lit_assn \<times>\<^sub>a dropi_assn (rdomp size_assn) [\<lambda>(Ai,tri) (Ai',tri',_). Ai'=Ai \<and> tri'=tri]\<^sub>c"  
    unfolding rpan_dest_def rpan_assn_def any_rel_def
    apply sepref_to_hoare
    apply vcg_normalize
    apply (simp named_ss HOL_basic_ss_nomatch: move_resolve_ex_eq)
    by vcg
    

  sepref_definition rpan_free [llvm_code] is "\<lambda>A. doN {let _ = rpan_dest A; RETURN ()}" :: "rpan_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn"  
    by sepref

  lemma rpan_free[sepref_frame_free_rules]: "MK_FREE rpan_assn rpan_free"
    apply (rule MK_FREE_hfrefI[OF rpan_free.refine])
    by auto
      
      
  sepref_def rpan_empty_impl is "uncurry (RETURN oo rpan_empty)" :: "lit_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a rpan_assn"
    unfolding rpan_empty_alt 
    apply (annot_snat_const size_T)
    apply (subst al_fold_custom_empty[where 'l=size_t])
    apply (subst larray.fold_replicate_init)
    supply [simp] = is_up'
    by sepref    
        
    
  lemma rpan_is_true_unchecked_alt: "rpan_is_true_unchecked rp x = do { 
    let (A,tr,bnd) = rpan_dest rp; 
    r \<leftarrow> bla_get_unchecked A (ulit_of x);
    let rp' = rpan_make A tr bnd;
    unborrow rp' rp;
    RETURN r
  }"
    unfolding rpan_is_true_unchecked_def
    by (auto simp: unborrow_def split: prod.split)
            
    
  lemma rpan_is_true_checked_alt: "RETURN oo rpan_is_true_checked = (\<lambda>rp x. do { 
    let (A,tr,bnd) = rpan_dest rp;
    let r = bla_get_checked A (ulit_of x);
    let rp' = rpan_make A tr bnd;
    unborrow rp' rp;
    RETURN r
  })"
    unfolding rpan_is_true_checked_def
    by (auto simp: fun_eq_iff unborrow_def)
      
    
  lemmas [sepref_opt_simps] = rpan_make_impl_def  
    
  sepref_def rpan_is_true_unchecked_impl [llvm_code,llvm_inline] is "uncurry rpan_is_true_unchecked" :: "rpan_assn\<^sup>k *\<^sub>a ulit_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"  
    unfolding rpan_is_true_unchecked_alt
    by sepref

    
  sepref_def rpan_is_true_checked_impl [llvm_code,llvm_inline] is "uncurry (RETURN oo rpan_is_true_checked)" :: "rpan_assn\<^sup>k *\<^sub>a ulit_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"  
    unfolding rpan_is_true_checked_alt 
    by sepref    
      
  sepref_def rpan_set_checked_impl [llvm_code,llvm_inline] is "uncurry rpan_set_checked" :: "rpan_assn\<^sup>d *\<^sub>a ulit_assn\<^sup>k \<rightarrow>\<^sub>a rpan_assn"  
    unfolding rpan_set_checked_def 
    by sepref
    
    
  sepref_def rpan_set_unchecked_impl [llvm_code,llvm_inline] is "uncurry rpan_set_unchecked" :: "rpan_assn\<^sup>d *\<^sub>a ulit_assn\<^sup>k \<rightarrow>\<^sub>a rpan_assn"  
    unfolding rpan_set_unchecked_def 
    by sepref
    
  sepref_def rpan_clear_impl is "uncurry rpan_clear" :: "size_assn\<^sup>k *\<^sub>a rpan_assn\<^sup>d \<rightarrow>\<^sub>a rpan_assn"  
    unfolding rpan_clear_def 
    
    apply (subst nfoldli_by_idx)
    apply (subst nfoldli_upt_by_while)
    apply (annot_snat_const size_T)
    by sepref    
  
  
  
  export_llvm
    rpan_empty_impl
    rpan_is_true_unchecked_impl  
    rpan_is_true_checked_impl  
    rpan_set_checked_impl
    rpan_set_unchecked_impl  
    rpan_clear_impl
  
(*    
  type_synonym rpani = "blai \<times> (lit_size_t word, size_t) array_list \<times> size_t word"  

  (* TODO: The bound is not needed, and can be dropped once we have stored that it is small enough *)
  definition rpan_assn :: "rpan \<Rightarrow> rpani \<Rightarrow> assn" where "rpan_assn \<equiv> bla_assn \<times>\<^sub>a al_assn' size_T lit_assn \<times>\<^sub>a size_assn"
  
  
  sepref_def rpan_empty_impl is "uncurry (RETURN oo rpan_empty)" :: "lit_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a rpan_assn"
    unfolding rpan_empty_alt rpan_assn_def rpan_make_def
    apply (annot_snat_const size_T)
    apply (subst al_fold_custom_empty[where 'l=size_t])
    apply (subst larray.fold_replicate_init)
    by sepref  
    
    
  sepref_def rpan_is_true_unchecked_impl is "uncurry rpan_is_true_unchecked" :: "rpan_assn\<^sup>k *\<^sub>a lit_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"  
    unfolding rpan_is_true_unchecked_def rpan_assn_def rpan_dest_def Let_def
    by sepref    
    
  sepref_def rpan_is_true_checked_impl is "uncurry (RETURN oo rpan_is_true_checked)" :: "rpan_assn\<^sup>k *\<^sub>a lit_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"  
    unfolding rpan_is_true_checked_def rpan_assn_def rpan_dest_def Let_def
    by sepref    
  
  sepref_def rpan_set_checked_impl is "uncurry rpan_set_checked" :: "rpan_assn\<^sup>d *\<^sub>a lit_assn\<^sup>k \<rightarrow>\<^sub>a rpan_assn"  
    unfolding rpan_set_checked_def rpan_assn_def rpan_make_def rpan_dest_def Let_def
    by sepref
    
  sepref_def rpan_set_unchecked_impl is "uncurry rpan_set_unchecked" :: "rpan_assn\<^sup>d *\<^sub>a lit_assn\<^sup>k \<rightarrow>\<^sub>a rpan_assn"  
    unfolding rpan_set_unchecked_def rpan_assn_def rpan_make_def rpan_dest_def Let_def
    by sepref
    
  sepref_def rpan_clear_impl is "uncurry rpan_clear" :: "size_assn\<^sup>k *\<^sub>a rpan_assn\<^sup>d \<rightarrow>\<^sub>a rpan_assn"  
    unfolding rpan_clear_def rpan_assn_def rpan_make_def rpan_dest_def Let_def
    
    apply (subst nfoldli_by_idx)
    apply (subst nfoldli_upt_by_while)
    apply (annot_snat_const size_T)
    by sepref    
    
*)

end

