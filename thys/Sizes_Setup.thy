subsection \<open>Setup of Default Machine Word Sizes\<close>
theory Sizes_Setup
imports Isabelle_LLVM.IICF
begin

(* TODO: Move *)      
(*
  To be used to synthesize a free rule with sepref_definition
*)
lemma MK_FREE_hfrefI: "(fri,fr) \<in> A\<^sup>d \<rightarrow>\<^sub>a unit_assn \<Longrightarrow> (\<And>x. nofail (fr x)) \<Longrightarrow> MK_FREE A fri"
  apply (rule)
  apply (drule hfrefD; simp)
  apply (drule hn_refineD)
  apply assumption
  apply (erule cons_rule)
  apply assumption
  by (simp add: sep_algebra_simps invalid_assn_def pure_def)

  
lemma mop_free_alt: "mop_free x = doN {let _ = x; RETURN ()}"
  unfolding mop_free_def by auto           

  
lemma MK_FREE_mopI: "(fri,mop_free) \<in> A\<^sup>d \<rightarrow>\<^sub>a unit_assn \<Longrightarrow> MK_FREE A fri"
  apply (erule MK_FREE_hfrefI)
  unfolding mop_free_def
  by simp
  
  
  
(* TODO: homogenize MK_FREE generation.
  currently, there's a mix of using schematic_goal or fixed goals, and
  either manual application of sepref_frame_free_rules, or sepref_dbg_side
  
  \<Rightarrow> use synth_definition where possible, and expose the mk_free-tac as proper tactic!

  
  synth_definition nadf_free [llvm_code] is [sepref_frame_free_rules]: "MK_FREE (cs_op_assn) \<hole>"
    unfolding cs_op_assn_def 
    by sepref_dbg_side 
  
*)  
  
  
  
(* TODO: Move.  *)
sepref_register 
  ucast: "UCAST(_\<rightarrow>_)"
  scast: "SCAST(_\<rightarrow>_)"
  
lemma UCAST_word_refine[sepref_fr_rules]: 
  "(\<lambda>w::'l\<^sub>1::len word. ll_zext w TYPE('l\<^sub>2::len word), RETURN o UCAST('l\<^sub>1 \<rightarrow> 'l\<^sub>2)) 
    \<in> [\<lambda>_. is_up' UCAST('l\<^sub>1 \<rightarrow> 'l\<^sub>2) ]\<^sub>a word_assn\<^sup>k \<rightarrow> word_assn"
proof -

  interpret llvm_prim_arith_setup .
  show ?thesis
    apply sepref_to_hoare
    by vcg  

qed    

lemma UCAST_word_refine_down[sepref_fr_rules]: 
  "(\<lambda>w::'l\<^sub>1::len word. ll_trunc w TYPE('l\<^sub>2::len word), RETURN o UCAST('l\<^sub>1 \<rightarrow> 'l\<^sub>2)) 
    \<in> [\<lambda>_. is_down' UCAST('l\<^sub>1 \<rightarrow> 'l\<^sub>2) ]\<^sub>a word_assn\<^sup>k \<rightarrow> word_assn"
proof -

  interpret llvm_prim_arith_setup .
  show ?thesis
    apply sepref_to_hoare
    by vcg  

qed    

lemma SCAST_word_refine[sepref_fr_rules]: 
  "(\<lambda>w::'l\<^sub>1::len word. ll_sext w TYPE('l\<^sub>2::len word), RETURN o SCAST('l\<^sub>1 \<rightarrow> 'l\<^sub>2)) 
    \<in> [\<lambda>_. is_up' SCAST('l\<^sub>1 \<rightarrow> 'l\<^sub>2) ]\<^sub>a word_assn\<^sup>k \<rightarrow> word_assn"
proof -

  interpret llvm_prim_arith_setup .
  show ?thesis
    apply sepref_to_hoare
    by vcg  

qed    

(* TODO: Move *)    
sepref_register 
  unat: unat 
  snat: snat

lemma unat_unat_rel_refine[sepref_import_param]: "(\<lambda>x. x, unat) \<in> Id \<rightarrow> unat_rel"
  unfolding unat_rel_def unat.rel_def
  by (auto simp: in_br_conv)

lemma snat_snat_rel_refine[sepref_import_param]: "(\<lambda>x::'l word. x, snat) \<in> [\<lambda>x. x<2^(LENGTH('l::len2)-1)]\<^sub>f Id \<rightarrow> snat_rel"
  unfolding snat_rel_def snat.rel_def
  apply (clarsimp simp: in_br_conv snat_invar_alt intro!: frefI)
  by (metis Suc_pred len_gt_0 p2_gt_0 unat_less_power word_gt_a_gt_0)
  
  
(* TODO: Move, close to thm of_nat_word_refine *)
thm of_nat_word_refine
lemma of_nat_snat_word_refine[sepref_import_param]: 
  "(id,word_of_nat) \<in> snat_rel' TYPE('a::len2) \<rightarrow> word_rel"
  by (auto simp: snat_rel_def snat.rel_def in_br_conv snat_eq_unat_aux2)
  

(* TODO: Move *)

definition [simp]: "max_snat_incl TYPE('l::len2) \<equiv> max_snat LENGTH('l)-1"
definition [simp]: "max_unat_incl TYPE('l::len) \<equiv> max_unat LENGTH('l)-1"
(* definition [simp]: "max_uint_incl TYPE('l::len) \<equiv> max_uint LENGTH('l)-1" *)
definition [simp]: "max_sint_incl TYPE('l::len2) \<equiv> max_sint LENGTH('l)-1"

sepref_register 
  "max_snat_incl TYPE('l::len2)"
  "max_unat_incl TYPE('l::len)"
  (* "max_uint_incl TYPE('l::len)" *)
  "max_sint_incl TYPE('l::len2)"


lemma max_snat_incl_refine[sepref_fr_rules]: 
  "(uncurry0 ll_max_snat,uncurry0 (RETURN (PR_CONST (max_snat_incl TYPE('l::len2))))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE('l)"
  apply sepref_to_hoare
  unfolding in_snat_rel_conv_assn
  by vcg
  
(* TODO: Fix in LLVM_ds_arith: ll_max_unat should be ::len, not ::len2 *)  
lemma max_unat_incl_refine[sepref_fr_rules]: 
  "(uncurry0 ll_max_unat,uncurry0 (RETURN (PR_CONST (max_unat_incl TYPE('l::len2))))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn' TYPE('l)"
  apply sepref_to_hoare
  unfolding in_unat_rel_conv_assn
  by vcg

(* TODO: Move to Sepref_HOL_Bindings, close to thm in_snat_rel_conv_assn *)  
lemma in_sint_rel_conv_assn: "\<up>((xi, x) \<in> sint_rel) = \<upharpoonleft>sint.assn x xi"
  by (auto simp: sint_rel_def sint.assn_is_rel pure_app_eq)

lemma in_bool1_rel_conv_assn: "\<up>((xi, x) \<in> bool1_rel) = \<upharpoonleft>bool.assn x xi"
  by (auto simp: bool1_rel_def bool.assn_is_rel pure_app_eq)
  
    
lemma max_sint_incl_refine[sepref_fr_rules]: 
  "(uncurry0 ll_max_sint,uncurry0 (RETURN (PR_CONST (max_sint_incl TYPE('l::len2))))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a sint_assn' TYPE('l)"
  apply sepref_to_hoare
  unfolding in_sint_rel_conv_assn
  by vcg


(* TODO: Move *)
context
begin  
  interpretation llvm_prim_arith_setup .

  sepref_register "of_bool :: bool \<Rightarrow> nat"
  lemma of_bool_snat_refine[sepref_fr_rules]: "(\<lambda>x. unat_snat_upcast TYPE('l::len2) x, RETURN o of_bool) \<in> bool1_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE('l)"  
    unfolding unat_snat_upcast_def
    apply sepref_to_hoare
    subgoal for x xi
      supply [simp] = is_up' word1_neqZ_is_one
      apply (simp add: bool1_rel_def bool.rel_def snat_rel_def snat.rel_def snat_invar_def in_br_conv)
      by vcg'
    done  
    
end  
  
  
  


text \<open>Characters are 8 bit unsigned\<close>
type_synonym char_t = 8
abbreviation "char_T \<equiv> TYPE(char_t)"
abbreviation "char_assn \<equiv> unat_assn' char_T"
abbreviation "max_char \<equiv> max_unat LENGTH(char_t)"


text \<open>And use a 64 bit size_t\<close>
type_synonym size_t = "64"
abbreviation "size_t_len \<equiv> 64"
abbreviation "size_T \<equiv> TYPE(size_t)"
abbreviation "size_assn \<equiv> snat_assn' size_T"
abbreviation "size_rel \<equiv> snat_rel' size_T"
abbreviation "max_size \<equiv> max_snat LENGTH(size_t)"
abbreviation "max_size_incl \<equiv> max_snat_incl size_T"

(* TODO: Generalize for all numerals! (will require a separate constant for the arg of numeral in len_of! ) *)
lemma len_of_size_t_unfold: "LENGTH(size_t) = size_t_len" by simp

text \<open>We store literals in 32 bits\<close>
type_synonym lit_size_t = "32"
abbreviation "lit_size_t_len \<equiv> 32"
abbreviation "lit_size_T \<equiv> TYPE(lit_size_t)"
abbreviation "lit_assn \<equiv> unat_assn' lit_size_T" 

abbreviation "max_lit \<equiv> max_unat LENGTH(lit_size_t)"
abbreviation "max_var \<equiv> max_snat LENGTH(lit_size_t)"

abbreviation "max_lit_incl \<equiv> max_unat_incl lit_size_T"
abbreviation "max_var_incl \<equiv> unat_const lit_size_T 0x7FFFFFFF"

abbreviation "max_var_incl_size \<equiv> snat_const size_T 0x7FFFFFFF"
lemma "max_var_incl_size = max_var_incl" by simp  


lemma len_of_lit_t_unfold: "LENGTH(lit_size_t) = lit_size_t_len" by simp


(* Checking lemma for above definition *)
lemma "max_var_incl = max_snat LENGTH(lit_size_t) - 1"
  by (simp add: max_snat_def)
  

text \<open>Clause-IDs are limited to max_size-1, such that we can map them with a standard array-map\<close>


definition "cid_rel \<equiv> b_rel size_rel (\<lambda>n. n<max_size-1)"

abbreviation "cid_assn \<equiv> pure cid_rel"

lemma in_cid_rel_boundsD[sepref_bounds_dest]: 
  "(w, n) \<in> cid_rel \<Longrightarrow> n < max_size-1"
  unfolding cid_rel_def
  by sepref_bounds

definition mk_cid :: "nat \<Rightarrow> nat" where [simp]: "mk_cid n = n"  
definition dest_cid :: "nat \<Rightarrow> nat" where [simp]: "dest_cid n = n"  

sepref_register mk_cid dest_cid
  
lemma mk_cid_refine[sepref_fr_rules]: "(Mreturn,RETURN o mk_cid) \<in> [\<lambda>n. n<max_size-1]\<^sub>a size_assn\<^sup>k \<rightarrow> cid_assn"
  unfolding mk_cid_def cid_rel_def
  apply sepref_to_hoare
  by vcg
  
lemma dest_cid_refine[sepref_fr_rules]: "(Mreturn,RETURN o dest_cid) \<in> cid_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding mk_cid_def cid_rel_def
  apply sepref_to_hoare
  by vcg

definition "word_of_cid cid \<equiv> word_of_nat (dest_cid cid)"  
sepref_register word_of_cid
sepref_def word_of_cid_impl [llvm_inline] is "RETURN o word_of_cid" :: "cid_assn\<^sup>k \<rightarrow>\<^sub>a word_assn' TYPE(size_t)"
  unfolding word_of_cid_def by sepref
    

end
