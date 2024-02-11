section \<open>Input\<close>
theory Parser_Input
imports LRAT_Sepref_Base
begin

subsection \<open>Abstract Input\<close>

(*
  We distinguish between input, and an iterator on the input.
  Thus, we can handle the input as constant parameter for sepref, and the iterator can
  be handled separately. The connection between input and iterator is only done at the abstract level. 
*)
  
    
  datatype input = INPUT (i_data: "8 word list")
  datatype input_iterator = INPUT_IT (position: nat)
  
  
  fun i_valid :: "input \<Rightarrow> input_iterator \<Rightarrow> bool" where
    "i_valid (INPUT xs) (INPUT_IT i) \<longleftrightarrow> i\<le>length xs"
    
  fun i_rem :: "input \<Rightarrow> input_iterator \<Rightarrow> 8 word list" where
    "i_rem (INPUT xs) (INPUT_IT i) = drop i xs"
    
  definition i_remsize :: "input \<Rightarrow> input_iterator \<Rightarrow> nat" where
    "i_remsize inp i = length (i_rem inp i)"
      
  fun i_pos :: "input \<Rightarrow> input_iterator \<Rightarrow> nat" where
    "i_pos (INPUT _) (INPUT_IT i) = i"
  
  definition [simp]: "i_eof inp i \<equiv> i_remsize inp i = 0"  
    
  fun i_peek :: "input \<Rightarrow> input_iterator \<Rightarrow> 8 word nres" where
    "i_peek (INPUT xs) (INPUT_IT i) = doN { ASSERT (i<length xs); mop_list_get xs i }"
  
  fun i_next :: "input \<Rightarrow> input_iterator \<Rightarrow> input_iterator nres" where
    "i_next (INPUT xs) (INPUT_IT i) = doN { ASSERT (i<length xs); RETURN (INPUT_IT (i+1)) }"
  
  definition i_size :: "input \<Rightarrow> nat" where
    "i_size inp = length (i_data inp)"  
    
  fun i_make_iterator :: "input \<Rightarrow> input_iterator nres" where
    "i_make_iterator (INPUT xs) = RETURN (INPUT_IT 0)"  
  
  
  
  definition i_read :: "input \<Rightarrow> input_iterator \<Rightarrow> (8 word \<times> input_iterator) nres" where
    "i_read inp it \<equiv> doN { c\<leftarrow>i_peek inp it; it \<leftarrow> i_next inp it; RETURN (c,it) }"  
    
    
    
  (* Abstract Interface *)    
  lemma i_peek_correct[refine_vcg]: "\<lbrakk>i_valid inp i; \<not>i_eof inp i\<rbrakk> \<Longrightarrow> i_peek inp i \<le> SPEC (\<lambda>r. r = hd (i_rem inp i))" 
    apply (cases inp; cases i)
    by (simp add: hd_drop_conv_nth i_remsize_def)
  
  lemma i_next_correct[refine_vcg]: "\<lbrakk>i_valid inp i; \<not>i_eof inp i\<rbrakk> \<Longrightarrow> i_next inp i 
    \<le> SPEC (\<lambda>i'. i_valid inp i' \<and> i_remsize inp i' < i_remsize inp i \<and> i_rem inp i' = tl (i_rem inp i))"
    apply (cases inp; cases i)
    by (simp add: drop_Suc drop_tl i_remsize_def)
  
  lemma i_make_iterator_correct[refine_vcg]: "i_make_iterator inp 
    \<le> SPEC (\<lambda>it. i_valid inp it \<and> i_remsize inp it = i_size inp \<and> i_rem inp it = i_data inp)"  
    apply (cases inp)
    unfolding i_remsize_def i_size_def
    by auto
    
  lemma i_read_correct[refine_vcg]: "\<lbrakk>i_valid inp i; \<not>i_eof inp i\<rbrakk> \<Longrightarrow> i_read inp i 
    \<le> SPEC (\<lambda>(c,i'). i_valid inp i' \<and> i_remsize inp i' < i_remsize inp i \<and> c=hd (i_rem inp i) \<and> i_rem inp i' = tl (i_rem inp i) )"    
    unfolding i_read_def
    apply refine_vcg
    by auto
  
    
  definition "parsed1 inp it c it' \<equiv> i_valid inp it \<and> i_valid inp it' \<and> i_rem inp it = c # i_rem inp it'"  
  definition "parsed inp it xs it' \<equiv> i_valid inp it \<and> i_valid inp it' \<and> i_rem inp it = xs @ i_rem inp it'"  

  lemma parsed_refl[simp]: 
    "parsed inp it xs it \<longleftrightarrow> i_valid inp it \<and> xs=[]"
    "parsed inp it [] it' \<longleftrightarrow> i_valid inp it \<and> it=it'"
    unfolding parsed_def
    apply auto
    apply (cases inp; cases it; cases it')
    apply auto
    by (metis diff_diff_cancel length_drop)
  
  lemma parsed_valid[simp]: 
    "parsed inp it xs it' \<Longrightarrow> i_valid inp it \<and> i_valid inp it'"
    "parsed1 inp it c it' \<Longrightarrow> i_valid inp it \<and> i_valid inp it'"
    unfolding parsed_def parsed1_def by auto

  lemma parsed1_Cons[simp]: "parsed inp it (c#xs) it' \<longleftrightarrow> (\<exists>ith. parsed1 inp it c ith \<and> parsed inp ith xs it')"  
    unfolding parsed_def parsed1_def
    apply auto
    apply (cases inp; cases it; cases it')
    apply (rule exI[where x="INPUT_IT (position it + 1)"])
    apply clarsimp
    by (metis drop_eq_ConsD drop_eq_Nil2 list.simps(3) not_less_eq_eq)
    
          
  lemma parsed_append[simp]: "parsed inp it (xs\<^sub>1@xs\<^sub>2) it' \<longleftrightarrow> (\<exists>ith. parsed inp it xs\<^sub>1 ith \<and> parsed inp ith xs\<^sub>2 it')"  
    unfolding parsed_def
    apply auto
    apply (cases inp; cases it; cases it')
    apply (rule exI[where x="INPUT_IT (position it + length xs\<^sub>1)"])
    apply (clarsimp)
    by (metis (no_types, lifting) add.commute append.right_neutral drop_append_miracle drop_drop drop_eq_Nil2 length_drop nat_le_linear ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
    
  lemma parsed_appendI: "parsed inp it xs\<^sub>1 ith \<Longrightarrow> parsed inp ith xs\<^sub>2 it' \<Longrightarrow> parsed inp it (xs\<^sub>1@xs\<^sub>2) it'" by auto  
  lemma parsed1_appendI: 
    "parsed1 inp it c ith \<Longrightarrow> parsed inp ith xs\<^sub>2 it' \<Longrightarrow> parsed inp it (c#xs\<^sub>2) it'" 
    "parsed inp it xs\<^sub>1 ith \<Longrightarrow> parsed1 inp ith c it' \<Longrightarrow> parsed inp it (xs\<^sub>1@[c]) it'" 
    by auto  
    
    
  lemma parsed_remsize: "parsed inp it xs it' \<Longrightarrow> i_remsize inp it = i_remsize inp it' + length xs"
    unfolding parsed_def i_remsize_def by auto
    
  lemma parsed1_remsize: "parsed1 inp it c it' \<Longrightarrow> i_remsize inp it = i_remsize inp it' + 1"
    unfolding parsed1_def i_remsize_def by auto
    
  lemma i_read_correct': "\<lbrakk> i_valid inp it; \<not>i_eof inp it \<rbrakk> \<Longrightarrow> i_read inp it \<le> SPEC (\<lambda>(c,it'). parsed1 inp it c it')"  
    unfolding i_read_def
    apply refine_vcg
    apply (auto simp: )
    unfolding parsed1_def
    by (auto simp: i_remsize_def)
  
  lemmas [refine_vcg del] = i_read_correct  
  lemmas [refine_vcg] = i_read_correct'
  

  subsection \<open>Input from Memory\<close>

  (* Reading from memory *)  
      
  (* memory, current index, size *)
  type_synonym rdmem_inp = "8 word list \<times> nat"
  type_synonym rdmem_it = "nat"
  

  definition "rdmem_inp_rel \<equiv> br (INPUT o fst) (\<lambda>(xs,n). n=length xs)"
  definition "rdmem_it_rel \<equiv> br (INPUT_IT) (\<lambda>_. True)"
    

  definition rdmem_size :: "rdmem_inp \<Rightarrow> nat" where "rdmem_size \<equiv> \<lambda>(m,n). n"
  definition rdmem_make_iterator :: "rdmem_inp \<Rightarrow> rdmem_it nres" where "rdmem_make_iterator \<equiv> \<lambda>(m,n). RETURN 0"
    
  definition rdmem_remsize :: "rdmem_inp \<Rightarrow> rdmem_it \<Rightarrow> nat nres" where "rdmem_remsize \<equiv> \<lambda>(m,n) i. doN {ASSERT (i\<le>n); RETURN (n-i)}"

  definition rdmem_peek :: "rdmem_inp \<Rightarrow> rdmem_it \<Rightarrow> 8 word nres" where "rdmem_peek \<equiv> \<lambda>(m,n) i. do {
    mop_list_get m i
  }"
  
  definition rdmem_next :: "rdmem_inp \<Rightarrow> rdmem_it \<Rightarrow> rdmem_it nres" where "rdmem_next \<equiv> \<lambda>(m,n) i. do {
    ASSERT(i<n);
    RETURN (i+1)
  }"
    
  definition rdmem_read :: "rdmem_inp \<Rightarrow> rdmem_it \<Rightarrow> (8 word \<times> rdmem_it) nres" where "rdmem_read inp it \<equiv> do {
    r\<leftarrow>rdmem_peek inp it;
    it\<leftarrow>rdmem_next inp it;
    RETURN (r,it)
  }"

  
  lemma rdmem_size_refine: "(rdmem_size, i_size) \<in> rdmem_inp_rel \<rightarrow> nat_rel"
    unfolding rdmem_size_def i_size_def
    unfolding rdmem_inp_rel_def 
    by (auto simp: in_br_conv)
    
  lemma rdmem_make_iterator_refine: "(rdmem_make_iterator, i_make_iterator) \<in> rdmem_inp_rel \<rightarrow> \<langle>rdmem_it_rel\<rangle>nres_rel"
    unfolding rdmem_make_iterator_def
    unfolding rdmem_inp_rel_def rdmem_it_rel_def
    apply (clarsimp simp: in_br_conv)
    apply (refine_vcg SPEC_refine)
    by (auto simp: in_br_conv)
      
  
  lemma rdmem_remsize_refine: "(uncurry rdmem_remsize, uncurry (RETURN oo i_remsize)) 
    \<in> [\<lambda>(inp,it). i_valid inp it]\<^sub>f rdmem_inp_rel \<times>\<^sub>r rdmem_it_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"  
    apply (intro frefI; clarsimp)
    unfolding rdmem_remsize_def
    apply refine_vcg
    unfolding rdmem_inp_rel_def rdmem_it_rel_def i_remsize_def
    by (auto simp: in_br_conv)
    

  lemma rdmem_peek_refine: "(rdmem_peek, i_peek) \<in> rdmem_inp_rel \<rightarrow> rdmem_it_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"  
    unfolding rdmem_peek_def 
    unfolding rdmem_inp_rel_def rdmem_it_rel_def
    apply (intro fun_relI; clarsimp simp: in_br_conv)
    by (refine_vcg SPEC_refine)
    
  lemma rdmem_next_refine: "(rdmem_next, i_next) \<in> rdmem_inp_rel \<rightarrow> rdmem_it_rel \<rightarrow> \<langle>rdmem_it_rel\<rangle>nres_rel"  
    unfolding rdmem_next_def 
    unfolding rdmem_inp_rel_def rdmem_it_rel_def
    apply (intro fun_relI; clarsimp simp: in_br_conv)
    apply (refine_vcg SPEC_refine)
    by (auto simp: in_br_conv)
    
  lemma rdmem_read_refine: "(rdmem_read, i_read) \<in> rdmem_inp_rel \<rightarrow> rdmem_it_rel \<rightarrow> \<langle>Id \<times>\<^sub>r rdmem_it_rel\<rangle>nres_rel"  
    unfolding rdmem_read_def i_read_def
    supply [refine_dref_RELATES] = RELATESI[of rdmem_it_rel]
    apply (refine_rcg rdmem_peek_refine[param_fo, THEN nres_relD] rdmem_next_refine[param_fo, THEN nres_relD])
    by auto
    
  definition "rdmem_inp_assn_raw \<equiv> array_slice_assn (id_assn::8 word \<Rightarrow> _) \<times>\<^sub>a size_assn"  
  definition "rdmem_it_assn_raw \<equiv> size_assn" (* Defined here to wrap size-assn, 
    and effectively mark it as ^d (otherwise, it would be recognized as pure, and resurrected immediately) *)

  sepref_def rdmem_size_impl [llvm_inline] is "RETURN o rdmem_size" :: "rdmem_inp_assn_raw\<^sup>k \<rightarrow>\<^sub>a size_assn"
    unfolding rdmem_size_def rdmem_inp_assn_raw_def
    by sepref  
    
  sepref_def rdmem_make_iterator_impl [llvm_inline] is "rdmem_make_iterator" :: "rdmem_inp_assn_raw\<^sup>k \<rightarrow>\<^sub>a rdmem_it_assn_raw"
    unfolding rdmem_make_iterator_def rdmem_inp_assn_raw_def rdmem_it_assn_raw_def
    apply (annot_snat_const size_T)
    by sepref
        
  sepref_def rdmem_remsize_impl [llvm_inline] is "uncurry rdmem_remsize" :: "rdmem_inp_assn_raw\<^sup>k *\<^sub>a rdmem_it_assn_raw\<^sup>k \<rightarrow>\<^sub>a size_assn"
    unfolding rdmem_remsize_def rdmem_inp_assn_raw_def rdmem_it_assn_raw_def
    by sepref
    
  sepref_def rdmem_peek_impl [llvm_inline] is "uncurry rdmem_peek" :: "rdmem_inp_assn_raw\<^sup>k *\<^sub>a rdmem_it_assn_raw\<^sup>k \<rightarrow>\<^sub>a id_assn"
    unfolding rdmem_peek_def rdmem_inp_assn_raw_def rdmem_it_assn_raw_def
    by sepref
    
  sepref_def rdmem_next_impl [llvm_inline] is "uncurry rdmem_next" :: "rdmem_inp_assn_raw\<^sup>k *\<^sub>a rdmem_it_assn_raw\<^sup>d \<rightarrow>\<^sub>a rdmem_it_assn_raw"
    unfolding rdmem_next_def rdmem_inp_assn_raw_def rdmem_it_assn_raw_def
    apply (annot_snat_const size_T)
    by sepref
      
  sepref_def rdmem_read_impl [llvm_inline] is "uncurry rdmem_read" :: "rdmem_inp_assn_raw\<^sup>k *\<^sub>a rdmem_it_assn_raw\<^sup>d \<rightarrow>\<^sub>a id_assn \<times>\<^sub>a rdmem_it_assn_raw"
    unfolding rdmem_read_def 
    by sepref
          
  definition "rdmem_inp_assn \<equiv> hr_comp rdmem_inp_assn_raw rdmem_inp_rel"
  definition "rdmem_it_assn \<equiv> hr_comp rdmem_it_assn_raw rdmem_it_rel"
    
  lemma rdmem_it_assn_is_pure[safe_constraint_rules, simp]: "is_pure rdmem_it_assn"
    unfolding rdmem_it_assn_def rdmem_it_assn_raw_def
    by solve_constraint

  lemmas [sepref_frame_free_rules] = mk_free_is_pure[OF rdmem_it_assn_is_pure]
  
  sepref_register i_size i_make_iterator i_remsize i_peek i_next i_read
  
  
  context
    notes [fcomp_norm_unfold] = rdmem_inp_assn_def[symmetric] rdmem_it_assn_def[symmetric] 
  begin

    
    lemmas rdmem_size_impl_hnr[sepref_fr_rules] = rdmem_size_impl.refine[FCOMP rdmem_size_refine]
    lemmas rdmem_make_iterator_impl_hnr[sepref_fr_rules] = rdmem_make_iterator_impl.refine[FCOMP rdmem_make_iterator_refine]
    
    lemmas rdmem_remsize_impl_hnr[sepref_fr_rules] = rdmem_remsize_impl.refine[FCOMP rdmem_remsize_refine]
    lemmas rdmem_peek_impl_hnr[sepref_fr_rules] = rdmem_peek_impl.refine[FCOMP rdmem_peek_refine]
    lemmas rdmem_next_impl_hnr[sepref_fr_rules] = rdmem_next_impl.refine[FCOMP rdmem_next_refine]
    lemmas rdmem_read_impl_hnr[sepref_fr_rules] = rdmem_read_impl.refine[FCOMP rdmem_read_refine]
    
  end  

  
  sepref_register i_eof
  
  sepref_def rdmem_eof [llvm_inline] is "uncurry (RETURN oo i_eof)" :: "[\<lambda>(inp,it). i_valid inp it]\<^sub>a rdmem_inp_assn\<^sup>k *\<^sub>a rdmem_it_assn\<^sup>k \<rightarrow> bool1_assn"
    unfolding i_eof_def
    apply (annot_snat_const size_T)
    by sepref
  






end
