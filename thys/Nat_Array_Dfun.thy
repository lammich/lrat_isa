section \<open>Array based Default-Valued Function\<close>
theory Nat_Array_Dfun
imports Intf_Dfun
begin


text \<open>Functions \<open>nat \<Rightarrow> 'a::default\<close>, based on dynamic array\<close>

subsection \<open>Intermediate Abstraction Level\<close>

context
  fixes dflt :: 'a
begin 
    
    
definition nat_map_\<alpha> :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" where 
  "nat_map_\<alpha> xs i \<equiv> if i<length xs then xs!i else dflt"

definition nat_map_init_size :: nat where "nat_map_init_size = 16"  
definition nat_map_empty :: "'a list" where "nat_map_empty \<equiv> replicate nat_map_init_size dflt"  
         
definition "nat_map_lookup xs i \<equiv> if i<length xs then op_list_get xs i else dflt"

definition nat_map_newsize :: "nat \<Rightarrow> nat \<Rightarrow> nat nres" 
  where "nat_map_newsize csz nsz \<equiv> do {ASSERT(csz<nsz); SPEC (\<lambda>sz'. nsz \<le> sz')}"

  
definition "nat_map_update_resize xs i v \<equiv> doN {
  l \<leftarrow> mop_list_length xs;
  ASSERT (l \<le> i);
  ns \<leftarrow> nat_map_newsize l (i+1);
  ASSERT(l<ns);
  let xs = op_list_grow_init dflt ns l xs;
  mop_list_set xs i v
}"  
    
definition "nat_map_update xs i v \<equiv> do {
  if i<length xs then
    mop_list_set xs i v
  else 
    nat_map_update_resize xs i v  
}"

definition "nat_map_reset xs i \<equiv> 
  if i<length xs then
    mop_list_set xs i dflt
  else
    RETURN xs
"

lemma nat_map_empty_correct[simp]: "nat_map_\<alpha> nat_map_empty = (\<lambda>_. dflt)"
  unfolding nat_map_\<alpha>_def nat_map_empty_def
  by (simp add: fun_eq_iff) 
    
lemma nat_map_lookup_correct[simp]: "nat_map_lookup m i = nat_map_\<alpha> m i"
  unfolding nat_map_lookup_def nat_map_\<alpha>_def by auto
  
lemma nat_map_update_correct[refine_vcg]: "nat_map_update m i x \<le> SPEC (\<lambda>m'. nat_map_\<alpha> m' = (nat_map_\<alpha> m)(i:=x))"
  unfolding nat_map_update_def nat_map_update_resize_def nat_map_newsize_def 
  apply refine_vcg
  unfolding nat_map_\<alpha>_def 
  by (auto simp: fun_eq_iff nth_append split: if_splits)

lemma nat_map_reset_correct[refine_vcg]: "nat_map_reset m i \<le> SPEC (\<lambda>m'. nat_map_\<alpha> m' = (nat_map_\<alpha> m)(i:=dflt))"
  unfolding nat_map_reset_def 
  apply refine_vcg
  unfolding nat_map_\<alpha>_def 
  by (auto simp: fun_eq_iff split: if_splits)
  
sepref_register nat_map_empty nat_map_lookup nat_map_update nat_map_update_resize nat_map_reset 
        
end


subsection \<open>Implementation\<close>


subsubsection \<open>Max-Index computation\<close>

definition nat_map_newsize_impl :: "'l::len2 word \<Rightarrow> 'l word \<Rightarrow> 'l word llM" 
where [llvm_inline]:   
  "nat_map_newsize_impl c c' \<equiv> doM {
    max::'l word \<leftarrow> ll_max_snat;
    max \<leftarrow> ll_udiv max (signed_nat 2);
    b \<leftarrow> ll_icmp_ule c max;
    llc_if b (doM {
        c \<leftarrow> ll_mul c (signed_nat 2);
        cok \<leftarrow> ll_icmp_sle c' c;
        llc_if cok (Mreturn c) (Mreturn c')
      }) 
      (Mreturn c')
  }"

lemma nat_map_newsize_impl_rule[vcg_rules]: 
  "llvm_htriple 
    (\<up>\<^sub>d(LENGTH('l)>2) ** \<upharpoonleft>snat.assn c ci ** \<upharpoonleft>snat.assn c' ci' ** \<up>\<^sub>d(c\<le>c')) 
    (nat_map_newsize_impl ci (ci'::'l::len2 word)) 
    (\<lambda>ri. EXS r. \<upharpoonleft>snat.assn r ri ** \<up>(max c c' \<le> r))"  
  unfolding nat_map_newsize_impl_def
  apply (vcg_monadify)
  by vcg

find_theorems snat.assn snat_rel  
  
sepref_register nat_map_newsize
lemma nat_map_newsize_impl_refine[sepref_fr_rules]: 
  "(uncurry nat_map_newsize_impl, uncurry nat_map_newsize)
  \<in> [\<lambda>_. LENGTH('l)>2]\<^sub>a (snat_assn' TYPE('l::len2))\<^sup>k *\<^sub>a (snat_assn' TYPE('l::len2))\<^sup>k \<rightarrow> snat_assn' TYPE('l::len2)"
  unfolding nat_map_newsize_def
  apply sepref_to_hoare
  unfolding in_snat_rel_conv_assn
  apply vcg'
  by (simp_all add: refine_pw_simps)
  
  
subsubsection \<open>Standard Operations\<close>  

sepref_def nat_map_empty_impl is "uncurry0 (RETURN (PR_CONST (nat_map_empty init)))" 
  :: "[\<lambda>_. 5<LENGTH('l)]\<^sub>a unit_assn\<^sup>k \<rightarrow> larray_assn' TYPE('l::len2) id_assn"
  apply -
  unfolding PR_CONST_def nat_map_empty_def larray_fold_custom_replicate nat_map_init_size_def
  apply (annot_snat_const "TYPE('l)")
  by sepref_dbg_keep

sepref_def nat_map_lookup_impl [llvm_code,llvm_inline] is "uncurry (RETURN oo PR_CONST (nat_map_lookup init))" 
  :: "(larray_assn' TYPE('l::len2) id_assn)\<^sup>k *\<^sub>a (snat_assn' TYPE('l))\<^sup>k \<rightarrow>\<^sub>a id_assn"  
  unfolding nat_map_lookup_def PR_CONST_def
  by sepref

sepref_def nat_map_update_resize_impl is "uncurry2 (PR_CONST (nat_map_update_resize init))" 
  :: "[\<lambda>((xs,i),v). 2 < LENGTH('l) \<and> i+1 < max_snat LENGTH('l)]\<^sub>a (larray_assn' TYPE('l::len2) id_assn)\<^sup>d *\<^sub>a (snat_assn' TYPE('l))\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> larray_assn' TYPE('l::len2) id_assn"  
  unfolding nat_map_update_resize_def PR_CONST_def
  apply (annot_snat_const "TYPE('l)")
  by sepref
  
sepref_def nat_map_update_impl [llvm_code,llvm_inline] is "uncurry2 (PR_CONST (nat_map_update init))" 
  :: "[\<lambda>((xs,i),v). 2 < LENGTH('l) \<and> i+1 < max_snat LENGTH('l)]\<^sub>a 
        (larray_assn' TYPE('l::len2) id_assn)\<^sup>d *\<^sub>a (snat_assn' TYPE('l))\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> larray_assn' TYPE('l::len2) id_assn"
  unfolding nat_map_update_def PR_CONST_def
  by sepref


sepref_def nat_map_reset_impl [llvm_code,llvm_inline] is "uncurry (PR_CONST (nat_map_reset init))" 
  :: "(larray_assn' TYPE('l::len2) id_assn)\<^sup>d *\<^sub>a (snat_assn' TYPE('l))\<^sup>k \<rightarrow>\<^sub>a larray_assn' TYPE('l::len2) id_assn"
  unfolding nat_map_reset_def PR_CONST_def
  by sepref
  

subsection \<open>Chaining of Refinements\<close>   

context
  fixes dflt:: 'a
  fixes A :: "'a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn"
  assumes INIT: "GEN_ALGO dflt (is_init A)"
begin

  subsubsection \<open>Custom Parametricity Rules\<close>
  text \<open>We define custom parametricity rules that depend on the correctness of the default element\<close>

  private lemma init_param: "(init,dflt) \<in> the_pure A" 
    using INIT unfolding is_init_def GEN_ALGO_def by simp

  
  lemma nat_map_empty_param: "(uncurry0 (RETURN (PR_CONST (nat_map_empty init))), uncurry0 (RETURN (PR_CONST (nat_map_empty dflt)))) 
    \<in> unit_rel \<rightarrow>\<^sub>f \<langle>\<langle>the_pure A\<rangle>list_rel\<rangle>nres_rel"    
    unfolding nat_map_empty_def PR_CONST_def uncurry0_def
    apply (rule frefI)
    apply (parametricity add: init_param)
    by simp

  term nat_map_lookup  
  lemma nat_map_lookup_param: 
    "(((PR_CONST (nat_map_lookup init))), ((PR_CONST (nat_map_lookup dflt))))
    \<in> \<langle>the_pure A\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> the_pure A"
    unfolding nat_map_lookup_def PR_CONST_def
    apply (parametricity add: init_param)
    apply simp
    apply (parametricity)
    apply simp
    done
      
  term nat_map_update  
  
  lemma nat_map_update_param: "(PR_CONST (nat_map_update init), PR_CONST (nat_map_update dflt)) \<in> 
    \<langle>the_pure A\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> the_pure A \<rightarrow> \<langle>\<langle>the_pure A\<rangle>list_rel\<rangle>nres_rel"
    unfolding PR_CONST_def nat_map_update_def nat_map_update_resize_def
    apply parametricity
    apply (clarsimp_all)
    apply (parametricity; simp)
    apply (parametricity; simp)
    apply (simp add: nres_relI)
    apply (parametricity add: init_param; simp)
    apply (parametricity; simp)
    done
        
  lemma nat_map_reset_param: "(PR_CONST (nat_map_reset init), PR_CONST (nat_map_reset dflt)) \<in> 
    \<langle>the_pure A\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> \<langle>\<langle>the_pure A\<rangle>list_rel\<rangle>nres_rel"
    unfolding PR_CONST_def nat_map_reset_def
    apply parametricity
    apply (clarsimp_all)
    apply (parametricity add: init_param; simp)
    done
    
        
end    

text \<open>We add the information about the correct default element to the refinement relation\<close>

definition "nm_ga_rel dflt A \<equiv> (if GEN_ALGO dflt (is_init A) then \<langle>the_pure A\<rangle>list_rel else {})"

lemma nat_map_empty_param2: "GEN_ALGO dflt (is_init A) \<Longrightarrow> 
  (uncurry0 (RETURN (PR_CONST (nat_map_empty init))), uncurry0 (RETURN (PR_CONST (nat_map_empty dflt)))) 
    \<in> unit_rel \<rightarrow>\<^sub>f \<langle>nm_ga_rel dflt A\<rangle>nres_rel
  "
  using nat_map_empty_param unfolding nm_ga_rel_def by force

lemma nat_map_lookup_param2: "
  (((PR_CONST (nat_map_lookup init))), ((PR_CONST (nat_map_lookup dflt))))
    \<in> nm_ga_rel dflt A \<rightarrow> nat_rel \<rightarrow> the_pure A"
  using nat_map_lookup_param[of dflt A] unfolding nm_ga_rel_def 
  by auto
  
lemma nat_map_update_param2: "(PR_CONST (nat_map_update init), PR_CONST (nat_map_update dflt)) \<in> 
  nm_ga_rel dflt A \<rightarrow> nat_rel \<rightarrow> the_pure A \<rightarrow> \<langle>nm_ga_rel dflt A\<rangle>nres_rel"
  using nat_map_update_param[of dflt A] unfolding nm_ga_rel_def 
  by auto

lemma nat_map_reset_param2: "(PR_CONST (nat_map_reset init), PR_CONST (nat_map_reset dflt)) \<in> 
  nm_ga_rel dflt A \<rightarrow> nat_rel \<rightarrow> \<langle>nm_ga_rel dflt A\<rangle>nres_rel"
  using nat_map_reset_param[of dflt A] unfolding nm_ga_rel_def 
  by auto
  

subsection \<open>Customized intermediate to abstract lemmas\<close>   

lemma nat_map_empty_refine: "(PR_CONST (nat_map_empty i),PR_CONST (op_dfun_empty i)) \<in> br (nat_map_\<alpha> i) top"
  by (auto simp: in_br_conv)

lemma nat_map_lookup_refine: "(PR_CONST (nat_map_lookup i), op_dfun_lookup) \<in> br (nat_map_\<alpha> i) top \<rightarrow> Id \<rightarrow> Id"
  by (auto simp: in_br_conv)  

lemma nat_map_update_refine: 
  "(PR_CONST (nat_map_update i), RETURN ooo op_dfun_upd) \<in> br (nat_map_\<alpha> i) top \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>br (nat_map_\<alpha> i) top\<rangle>nres_rel"  
  apply clarsimp
  apply refine_vcg  
  by (simp add: in_br_conv)  

lemma nat_map_reset_refine: 
  "(PR_CONST (nat_map_reset i), RETURN oo (PR_CONST op_dfun_reset i)) \<in> br (nat_map_\<alpha> i) top \<rightarrow> Id \<rightarrow> \<langle>br (nat_map_\<alpha> i) top\<rangle>nres_rel"  
  apply clarsimp
  apply refine_vcg  
  by (simp add: in_br_conv)  
  

subsection \<open>Combined Refinements\<close>
      
type_synonym ('a,'l) nadf = "('a,'l) larray"

definition nadf_assn :: "'a \<Rightarrow> ('a\<Rightarrow>'c::llvm_rep \<Rightarrow> assn) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> ('c,'l::len2) nadf \<Rightarrow> assn" 
  where "nadf_assn dflt A \<equiv> hr_comp (hr_comp (larray_assn id_assn) (nm_ga_rel dflt A)) (br (nat_map_\<alpha> dflt) top)"  

abbreviation nadf_assn' :: "'l::len2 itself \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (_,'l) larray \<Rightarrow> assn"
  where "nadf_assn' TYPE('l) dflt A \<equiv> nadf_assn dflt A"
  
  
lemma nadf_vassn_tagD[dest!]: "vassn_tag (nadf_assn dflt A a c) \<Longrightarrow> GEN_ALGO dflt (is_init A)"
  unfolding nadf_assn_def nm_ga_rel_def
  apply (rule ccontr)
  by simp
    
  
  
    
definition op_nadf_empty :: "'l::len2 itself \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'vi::llvm_rep \<Rightarrow> assn) \<Rightarrow> 'k \<Rightarrow> 'v" where
  [simp]: "op_nadf_empty TYPE('l) dflt A \<equiv> op_dfun_empty dflt"  
lemmas nadf_fold_custom_empty = op_nadf_empty_def[symmetric]  


lemma nadf_assn_intf[intf_of_assn]: "intf_of_assn A TYPE('v) \<Longrightarrow> intf_of_assn (nadf_assn dflt A) (TYPE((nat,'v)i_dfun))"
  by simp

  
context
  notes [fcomp_norm_unfold] = nadf_assn_def[symmetric]
  fixes A :: "'v \<Rightarrow> 'vi::llvm_rep \<Rightarrow> assn"
  fixes dflt :: "'v"
  (* assumes PURE: "CONSTRAINT is_pure A" *)
begin

      
  sepref_register op_nadf_empty: "op_nadf_empty TYPE('l::len2) dflt A" :: "('k,'v) i_dfun" 


  lemma nat_map_empty_hnr[sepref_fr_rules]: "GEN_ALGO dflt (is_init A) \<Longrightarrow>
    (uncurry0 nat_map_empty_impl, uncurry0 (Refine_Basic.RETURN (PR_CONST (op_nadf_empty TYPE('l) dflt A))))
    \<in> [\<lambda>x. 5 < LENGTH('l::len2)]\<^sub>a unit_assn\<^sup>k \<rightarrow> nadf_assn' TYPE('l) dflt A"
    using nat_map_empty_impl.refine[FCOMP nat_map_empty_param2, FCOMP nat_map_empty_refine]
    apply simp
    by fast
    
  lemma nat_map_lookup_hnr[sepref_fr_rules]: 
    "(uncurry nat_map_lookup_impl, uncurry (Refine_Basic.RETURN \<circ>\<circ> op_dfun_lookup))
    \<in> (nadf_assn dflt A)\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a A"
    apply (rule hfref_indep_vassn_tagI)
    apply clarsimp
    using nat_map_lookup_impl.refine[FCOMP nat_map_lookup_param2, FCOMP nat_map_lookup_refine, of dflt A]
    by (simp add: GEN_ALGO_is_init_pure)
    
  lemma nat_map_update_hnr[sepref_fr_rules]:
    "(uncurry2 nat_map_update_impl, uncurry2 (Refine_Basic.RETURN ooo op_dfun_upd))
    \<in> [\<lambda>((f, x), y). 2 < LENGTH('l::len2) \<and> Suc x < max_snat LENGTH('l)]\<^sub>a 
      (nadf_assn' TYPE('l) dflt A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow> nadf_assn dflt A"    
    apply (rule hfref_indep_vassn_tagI)
    apply clarsimp
    using nat_map_update_impl.refine[FCOMP nat_map_update_param2, FCOMP nat_map_update_refine, of dflt A]
    by (simp add: GEN_ALGO_is_init_pure)

  lemma nat_map_reset_hnr[sepref_fr_rules]:
    "(uncurry nat_map_reset_impl, uncurry (Refine_Basic.RETURN oo (PR_CONST (op_dfun_reset dflt))))
      \<in> (nadf_assn dflt A)\<^sup>d *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a nadf_assn dflt A"    
    apply (rule hfref_indep_vassn_tagI)
    apply clarsimp
    using nat_map_reset_impl.refine[FCOMP nat_map_reset_param2, FCOMP nat_map_reset_refine, of dflt A]
    by (simp add: GEN_ALGO_is_init_pure)
    
    
end        

synth_definition nadf_free [llvm_code] is [sepref_frame_free_rules]: "MK_FREE (nadf_assn dflt A) \<hole>"
  unfolding nadf_assn_def
  by (rule free_thms sepref_frame_free_rules)+


export_llvm 
  "nat_map_empty_impl :: (64 word \<times> 8 word ptr) llM"
  "nat_map_lookup_impl :: (64 word \<times> 8 word ptr) \<Rightarrow> _ \<Rightarrow> _ llM"
  "nat_map_update_impl :: (64 word \<times> 8 word ptr) \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ llM"
  "nat_map_reset_impl :: (64 word \<times> 8 word ptr) \<Rightarrow> _ \<Rightarrow> _ llM"


end
