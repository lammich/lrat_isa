theory LRAT_Parsers
imports LRAT_Sepref_Base Unsigned_Literal 
begin


  (*
    size_t fread_from_proof( void * ptr, size_t n )
  
    Reads at most n bytes into memory at ptr, and returns the number of bytes actually read.
    
    We under-specify the values of the read bytes, such that we get a sound approximation 
    of this function, even without a model of the input file. 
    As we only read proofs with this method, this does not affect soundness of the checker.
    
  *)
  
  consts fread_from_proof :: "8 word ptr \<Rightarrow> size_t word \<Rightarrow> size_t word llM"
  specification (fread_from_proof)
    fread_from_proof_rule[vcg_rules]: "llvm_htriple 
      (\<upharpoonleft>LLVM_DS_NArray.array_slice_assn xs xsi ** \<upharpoonleft>snat.assn n ni ** \<up>(n\<le>length xs))
      (fread_from_proof xsi ni)                               
      (\<lambda>ri. EXS r ys. 
          \<upharpoonleft>snat.assn r ri 
        ** \<upharpoonleft>LLVM_DS_NArray.array_slice_assn ys xsi 
        ** \<up>(r\<le>n \<and> length ys = length xs \<and> drop r ys = drop r xs))
      "
    apply (rule exI[where x="\<lambda>_ _. Mreturn 0"])
    by vcg

  lemmas [llvm_code_raw] = LLVM_EXTERNALI[of fread_from_proof "''fread_from_proof''"]
    
  
  (* Replaced the below hack by proper external function decl
  (* HACK (unsound if exploited): We define external_fread_std as something executable, and
    then replace in generated code.
  
    When this is exploited (e.g. by exposing the definition of external_fread_std), 
    it get's unsound, as we can prove stronger properties of external_fread_std than our replacement has.
  *)

  definition external_fread_std :: "8 word ptr \<Rightarrow> size_t word \<Rightarrow> size_t word llM" where
    [llvm_code]: "external_fread_std _ _ \<equiv> Mreturn 0"
    
  lemma fread_std_rule[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>LLVM_DS_NArray.array_slice_assn xs xsi ** \<upharpoonleft>snat.assn n ni ** \<up>(n\<le>length xs))
    (external_fread_std xsi ni)                               
    (\<lambda>ri. EXS r ys. 
        \<upharpoonleft>snat.assn r ri 
      ** \<upharpoonleft>LLVM_DS_NArray.array_slice_assn ys xsi 
      ** \<up>(r\<le>n \<and> length ys = length xs \<and> drop r ys = drop r xs))
    "
    unfolding external_fread_std_def 
    by vcg  
  *)  
    
  definition [llvm_inline]: "fread_std_impl n ptr \<equiv> doM {
    r \<leftarrow> fread_from_proof ptr n;
    Mreturn (r,ptr)
  }"  
        
  definition fread_std_spec :: "nat \<Rightarrow> 8 word list \<Rightarrow> (nat \<times> 8 word list) nres" 
    where "fread_std_spec n xs \<equiv> doN { 
      ASSERT (n\<le>length xs); 
      SPEC (\<lambda>(r,xs'). \<exists>ys. r\<le>n \<and> length ys = r \<and> xs' = ys @ drop r xs )}"

  lemma fread_std_spec_alt: "fread_std_spec n xs = doN {
    ASSERT (n\<le>length xs);
    SPEC (\<lambda>(r,ys). r\<le>n \<and> length ys = length xs \<and> drop r ys = drop r xs) }"
    unfolding fread_std_spec_def
    apply (rule antisym; refine_vcg)
    apply clarsimp_all
    subgoal for r xs'
      apply (drule sym[of "drop _ _"])
      apply (rule exI[where x="take r xs'"])
      by auto
    done  
      
  lemma array_assn_word_eq_raw: "array_assn word_assn = raw_array_assn"  
    unfolding array_assn_def
    by simp
      
    
  lemma array_slice_assn_word_eq_raw: "array_slice_assn word_assn = raw_array_slice_assn"  
    unfolding array_slice_assn_def
    by simp
  
  find_theorems LLVM_DS_NArray.array_slice_assn LLVM_DS_NArray.narray_assn  
  
  thm array_assn_split
    
    
  lemma fri_intro_pure_rl: "\<lbrakk>PRECOND (SOLVE_ASM (\<flat>\<^sub>pA a c)); PRECOND (SOLVE_DEFAULT_AUTO (LLVM_Shallow_RS.is_pure A))\<rbrakk> \<Longrightarrow> \<box> \<turnstile> \<upharpoonleft>A a c"
    by (simp add: PRECOND_def SOLVE_ASM_def SOLVE_DEFAULT_AUTO_def extract_pure_assn pure_true_conv)
    
  sepref_register fread_std_spec
  lemma fread_std_spec_array_hnr[sepref_fr_rules]: "(uncurry fread_std_impl, uncurry fread_std_spec) 
    \<in> size_assn\<^sup>k *\<^sub>a (array_assn word_assn)\<^sup>d \<rightarrow>\<^sub>a size_assn \<times>\<^sub>a array_assn word_assn"
    unfolding array_assn_word_eq_raw fread_std_impl_def fread_std_spec_def array_assn_split
    unfolding snat_rel_def snat.assn_is_rel[symmetric] 
    supply [simp] = refine_pw_simps snat.assn_pure
    apply sepref_to_hoare
    apply vcg_normalize
    supply [fri_rules] = fri_intro_pure_rl
    
    apply vcg'
    
    apply clarsimp
    subgoal for xs ptr n r xs'
      apply (rule exI[where x="take r xs'"])
      apply simp
      by (metis append_take_drop_id)
    
    done
  
  lemma fread_std_spec_array_slice_hnr[sepref_fr_rules]: "(uncurry fread_std_impl, uncurry fread_std_spec) 
    \<in> size_assn\<^sup>k *\<^sub>a (array_slice_assn word_assn)\<^sup>d \<rightarrow>\<^sub>a size_assn \<times>\<^sub>a array_slice_assn word_assn"
    unfolding array_slice_assn_word_eq_raw fread_std_impl_def fread_std_spec_def
    unfolding snat_rel_def snat.assn_is_rel[symmetric] 
    supply [simp] = refine_pw_simps snat.assn_pure
    apply sepref_to_hoare
    apply vcg_normalize
    supply [fri_rules] = fri_intro_pure_rl
    
    apply vcg'
    
    apply clarsimp
    subgoal for xs ptr n r xs'
      apply (rule exI[where x="take r xs'"])
      apply simp
      by (metis append_take_drop_id)
    
    done



        
  (* pos \<times> size \<times> buffer *)  
  type_synonym brd = "nat \<times> nat \<times> 8 word list"  
  definition buf_size :: nat where "buf_size \<equiv> 1048576"
  
  definition brd_invar :: "brd \<Rightarrow> bool" where
    "brd_invar \<equiv> \<lambda>(p,n,xs). n\<le>length xs \<and> length xs = buf_size"
  
  (*
    We store EOF by setting p>n.
  *)  
  definition brd_is_eof :: "brd \<Rightarrow> bool" where
    "brd_is_eof \<equiv> \<lambda>(p,n,_). (p>n)"
  
  
  definition brd_new :: "brd" where "brd_new \<equiv> (0,0,array_replicate_init 0 buf_size)"
  
  lemma brd_new_correct[simp]: 
    "brd_invar brd_new"
    "\<not>brd_is_eof brd_new"
    unfolding brd_invar_def brd_new_def brd_is_eof_def
    by auto
  
    
  definition brd_refill :: "nat \<Rightarrow> nat \<Rightarrow> 8 word list \<Rightarrow> (8 word \<times> brd) nres" where
    "brd_refill p n xs \<equiv> doN {
      if p=n then doN {
        (n,xs) \<leftarrow> fread_std_spec buf_size xs;
        
        let p=0;
        if p<n then doN {
          r \<leftarrow> mop_list_get xs p;
          RETURN (r, (p+1,n,xs))
        } else doN {
          RETURN (0,(1,0,xs))
        }
      } else 
        RETURN (0,(p,n,xs))
    }"
    
  

  (* If the end of file is reached, this will continue to return zeroes.
    In our implementation, this will either finish the proof or fail.
  *)      
  definition brd_read :: "brd \<Rightarrow> (8 word \<times> brd) nres" where
    "brd_read \<equiv> \<lambda>(p,n,xs). doN {
      if p<n then doN {
        r \<leftarrow> mop_list_get xs p;
        RETURN (r, (p+1,n,xs))
      } else  
        brd_refill p n xs
    }"
    
  lemma brd_read_correct[refine_vcg]: "brd_invar brd 
    \<Longrightarrow> brd_read brd \<le> SPEC (\<lambda>(r,brd'). 
        brd_invar brd' 
      \<and> (brd_is_eof brd \<longrightarrow> brd_is_eof brd')
      \<and> (brd_is_eof brd' \<longrightarrow> r=0)
    )"
    unfolding brd_read_def brd_refill_def fread_std_spec_def
    apply refine_vcg
    unfolding brd_invar_def brd_is_eof_def
    by auto
    
    
  definition "brd_assn \<equiv> size_assn \<times>\<^sub>a size_assn \<times>\<^sub>a array_assn (word_assn' TYPE(8))"
  
  sepref_register brd_new brd_refill brd_read brd_is_eof
  
  sepref_def brd_new_impl is "uncurry0 (RETURN brd_new)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a brd_assn"
    unfolding brd_new_def brd_assn_def buf_size_def
    apply (annot_snat_const size_T)
    by sepref
  
  sepref_def brd_free_impl [llvm_inline] is "mop_free" :: "brd_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn"
    unfolding mop_free_alt brd_assn_def
    by sepref
    
  lemmas brd_free[sepref_frame_free_rules] = MK_FREE_mopI[OF brd_free_impl.refine]
    
    
  sepref_def brd_refill_impl is "uncurry2 brd_refill"
    :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (array_assn (word_assn' TYPE(8)))\<^sup>d \<rightarrow>\<^sub>a word_assn' TYPE(8) \<times>\<^sub>a (size_assn \<times>\<^sub>a size_assn \<times>\<^sub>a array_assn (word_assn' TYPE(8)))"
    unfolding brd_refill_def brd_assn_def buf_size_def
    apply (annot_snat_const size_T)
    by sepref
        
  sepref_def brd_read_impl [llvm_inline] 
    is brd_read :: "brd_assn\<^sup>d \<rightarrow>\<^sub>a word_assn' TYPE(8) \<times>\<^sub>a brd_assn"
    unfolding brd_read_def brd_assn_def
    apply (annot_snat_const size_T)
    by sepref
    
  sepref_def brd_is_eof_impl [llvm_inline] is "RETURN o brd_is_eof" :: "brd_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding brd_is_eof_def brd_assn_def
    by sepref



  
(* Binary Interface *)
(*
  These are nondetermistic specifications, that merely specify that the iterator is advanced.
  No specification about the actually parsed data is made. 
  This is not required for our partial correctness guarantee: 
    if the proof is accepted, the formula was unsat. 
    If it's mis-parsed, it most likely won't be accepted, causing incompleteness, but not unsoundness.
    
*)
      
definition brd_read_ulito :: "brd \<Rightarrow> (dv_lit option \<times> brd) nres" where
  "brd_read_ulito brd \<equiv> do { 
    ASSERT(brd_invar brd); 
    SPEC (\<lambda>(_,brd). brd_invar brd) }"
      
definition brd_read_signed_id :: "brd \<Rightarrow> (nat \<times> brd) nres" where
  "brd_read_signed_id brd \<equiv> do { 
    ASSERT(brd_invar brd); 
    SPEC (\<lambda>(_,brd). brd_invar brd)  }"

definition brd_read_unsigned_id :: "brd \<Rightarrow> (nat \<times> brd) nres" where
  "brd_read_unsigned_id brd \<equiv> do { 
    ASSERT(brd_invar brd); 
    SPEC (\<lambda>(_,brd). brd_invar brd)   }"
    
    
lemmas brd_read_ulito_correct[refine_vcg] = mk_vcg_rule_PQ[OF brd_read_ulito_def]
lemmas brd_read_signed_id_correct[refine_vcg] = mk_vcg_rule_PQ[OF brd_read_signed_id_def]
lemmas brd_read_unsigned_id_correct[refine_vcg] = mk_vcg_rule_PQ[OF brd_read_unsigned_id_def]
  
sepref_register brd_read_ulito brd_read_signed_id brd_read_unsigned_id
        
abbreviation (input) "char_a \<equiv> 97::8 word"  
abbreviation (input) "char_d \<equiv> 100::8 word"  
    
lemma "of_char CHR ''a'' = char_a" by simp  
lemma "of_char CHR ''d'' = char_d" by simp  
  
text \<open>Binary encoding parser with generic result type. 
  Note that LLVM's shl instruction requires both operands to be of the same bit-length. 
  To avoid casts, we also adapt the shift operand to that bit-length
\<close>  
definition brd_parse_benc :: "brd \<Rightarrow> ('l::len word \<times> brd) nres" where "brd_parse_benc brd \<equiv> doN {
  ASSERT(brd_invar brd);
  (res,_,brd,_) \<leftarrow> WHILEIT
    (\<lambda>(res,shift,brd,brk). brd_invar brd \<and> shift < LENGTH('l)+7 ) 
    (\<lambda>(res,shift,brd,brk). \<not>brk \<and> shift < unat_const TYPE('l) (LENGTH('l))) 
    (\<lambda>(res,shift,brd,brk). doN {
      (c::char_t word,brd)\<leftarrow>brd_read brd;
      ASSERT(shift < LENGTH('l));
      let res = res OR ((UCAST(char_t \<rightarrow> 'l)(c AND 0x7F)) << shift);
      let shift = shift + unat_const TYPE('l) 7;
      RETURN (res,shift,brd,c AND 0x80 = 0)
    }) (0::'l word,unat_const TYPE('l) 0,brd,False);
  
  RETURN (res,brd)
}"

lemma brd_parse_benc_correct[refine_vcg]: "brd_invar brd \<Longrightarrow> brd_parse_benc brd \<le> SPEC (\<lambda>(_::'l::len word,brd). brd_invar brd)"
  unfolding brd_parse_benc_def
  apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(res,shift,brd,brk). LENGTH('l)+6-shift)"])
  by auto

sepref_register brd_parse_benc

      
sepref_def brd_parse_benc_size_impl is "brd_parse_benc" :: "brd_assn\<^sup>d \<rightarrow>\<^sub>a word_assn' size_T \<times>\<^sub>a brd_assn"
  unfolding brd_parse_benc_def
  unfolding len_of_size_t_unfold
  supply [simp] = is_up'
  supply [[goals_limit=1]]
  by sepref
    
sepref_def brd_parse_benc_lit_impl [llvm_inline] is "brd_parse_benc" :: "brd_assn\<^sup>d \<rightarrow>\<^sub>a word_assn' lit_size_T \<times>\<^sub>a brd_assn"
  unfolding brd_parse_benc_def
  unfolding len_of_lit_t_unfold
  supply [simp] = is_up'
  supply [[goals_limit=1]]
  by sepref
      
definition "brd_parse_benc_ulito brd \<equiv> doN {
  (res :: lit_size_t word,brd) \<leftarrow> brd_parse_benc brd;
  if res = 0x1 then
    RETURN (ulito_None,brd)  \<comment> \<open>We rely on literals not being \<open>-0\<close> (e.g. 1). TODO: check if we can get rid of that! \<close>
  else doN {
    l \<leftarrow> mk_ulito (unat res);
    RETURN (l,brd)
  }
}"  
  
lemma brd_parse_benc_ulito_refine: "(brd_parse_benc_ulito, brd_read_ulito) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding brd_parse_benc_ulito_def brd_read_ulito_def
  apply refine_vcg
  apply (clarsimp_all simp: unat_eq_1)
  done

sepref_def brd_parse_benc_ulito_impl is "brd_parse_benc_ulito" :: "brd_assn\<^sup>d \<rightarrow>\<^sub>a ulito_assn \<times>\<^sub>a brd_assn"
  unfolding brd_parse_benc_ulito_def
  by sepref

  
lemmas brd_read_ulito_hnr[sepref_fr_rules] = brd_parse_benc_ulito_impl.refine[FCOMP brd_parse_benc_ulito_refine]    
  
definition "brd_parse_benc_uid brd \<equiv> doN {
  (res :: size_t word,brd) \<leftarrow> brd_parse_benc brd;
  if (res < 0x7FFFFFFFFFFFFFFF) then
    RETURN (mk_cid (snat res),brd)
  else 
    RETURN (mk_cid (snat_const size_T 0),brd)
}"  

(* TODO: We can get rid of the bounds check, if we allow arbitrary snats for the
  ID, and only convert to cid_assn after if has been checked for validity.
*)
definition "brd_parse_benc_sid brd \<equiv> doN {
  (res :: size_t word,brd) \<leftarrow> brd_parse_benc brd;
  let res = (shiftr res (snat_const size_T 1));
  if (res < 0x7FFFFFFFFFFFFFFF) then
    RETURN (mk_cid (snat res),brd)
  else 
    RETURN (mk_cid (snat_const size_T 0),brd)
}"  

lemma brd_parse_benc_uid_refine: "(brd_parse_benc_uid, brd_read_unsigned_id) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding brd_parse_benc_uid_def brd_read_unsigned_id_def
  apply refine_vcg
  by auto

lemma brd_parse_benc_sid_refine: "(brd_parse_benc_sid, brd_read_signed_id) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding brd_parse_benc_sid_def brd_read_signed_id_def
  apply refine_vcg
  by auto

  
    
context
begin
  private lemma brd_parse_benc_uid_impl_aux1: "res < 0x7FFFFFFFFFFFFFFF \<Longrightarrow> res < 0x8000000000000000" for res :: "size_t word"
    by (simp add: word_less_nat_alt)

  private lemma brd_parse_benc_uid_impl_aux2: "res < 0x7FFFFFFFFFFFFFFF \<Longrightarrow> snat res < 0x7FFFFFFFFFFFFFFF" for res :: "size_t word"
    apply (subst snat_eq_unat_aux1)
    by (simp_all add: word_less_nat_alt)
      
    
  (* TODO: Move *)  
  lemma prod_case_Mbind_assoc: "doM { r \<leftarrow> case p of (a,b) \<Rightarrow> f a b; g r } 
       = doM { let (a,b) = p; r \<leftarrow> f a b; g r }"
    by (cases p) simp
       
  lemma nested_prod_case_conv: "
    (case (case p of (a, b) \<Rightarrow> (fa a b, fb a b)) of (a',b') \<Rightarrow> f a' b')
    = (case p of (a,b) \<Rightarrow> f (fa a b) (fb a b))
  " by (cases p) simp 
    
    
  sepref_definition brd_parse_benc_uid_impl [llvm_code] is "brd_parse_benc_uid" :: "brd_assn\<^sup>d \<rightarrow>\<^sub>a cid_assn \<times>\<^sub>a brd_assn"
    unfolding brd_parse_benc_uid_def
    supply [simp] = brd_parse_benc_uid_impl_aux1 brd_parse_benc_uid_impl_aux2
    (* Manual, very aggressive inlining *)
    supply [sepref_opt_simps] = brd_parse_benc_size_impl_def brd_read_impl_def prod_case_Mbind_assoc nested_prod_case_conv
    by sepref    
  
  sepref_definition brd_parse_benc_sid_impl [llvm_code] is "brd_parse_benc_sid" :: "brd_assn\<^sup>d \<rightarrow>\<^sub>a cid_assn \<times>\<^sub>a brd_assn"
    unfolding brd_parse_benc_sid_def
    supply [simp] = brd_parse_benc_uid_impl_aux1 brd_parse_benc_uid_impl_aux2
    (* Manual, very aggressive inlining *)
    supply [sepref_opt_simps] = brd_parse_benc_size_impl_def brd_read_impl_def prod_case_Mbind_assoc nested_prod_case_conv
    by sepref    
    
end

lemmas brd_read_unsigned_id_hnr[sepref_fr_rules] = brd_parse_benc_uid_impl.refine[FCOMP brd_parse_benc_uid_refine]
lemmas brd_read_signed_id_hnr[sepref_fr_rules] = brd_parse_benc_sid_impl.refine[FCOMP brd_parse_benc_sid_refine]




(* Remaining Size *)    
(*
  We add a remaining-size attribute, which limits how many bytes can be read from a stream.
  
  This is used to prove that there won't be any integer overflows in the subsequent program.
  Using this one counter, we don't need to check all possible counters for overflow.
*)
    
type_synonym brd_rs = "nat \<times> brd"

definition brd_rs_invar :: "brd_rs \<Rightarrow> bool" where "brd_rs_invar \<equiv> \<lambda>(rsz,brd). brd_invar brd"

definition brd_rs_remsize :: "brd_rs \<Rightarrow> nat" where "brd_rs_remsize \<equiv> \<lambda>(rsz,brd). rsz"

definition brd_rs_no_size_left :: "brd_rs \<Rightarrow> bool" where "brd_rs_no_size_left \<equiv> \<lambda>(rsz,brd). rsz=0"


definition brd_rs_new :: "nat \<Rightarrow> brd_rs" where
  "brd_rs_new n \<equiv> (n, brd_new)"

definition brd_rs_read :: "brd_rs \<Rightarrow> (8 word \<times> brd_rs) nres" where
  "brd_rs_read \<equiv> \<lambda>(rsz,brd). doN {
    ASSERT (rsz>0);
    (r,brd) \<leftarrow> brd_read brd;
    RETURN (r,(rsz-1,brd))
  }"


definition brd_rs_read_ulito :: "brd_rs \<Rightarrow> (dv_lit option \<times> brd_rs) nres" where
  "brd_rs_read_ulito \<equiv> \<lambda>(rsz,brd). doN {
    ASSERT (rsz>0);
    (r,brd) \<leftarrow> brd_read_ulito brd;
    RETURN (r,(rsz-1,brd))
  }"


definition brd_rs_read_unsigned_id :: "brd_rs \<Rightarrow> (nat \<times> brd_rs) nres" where
  "brd_rs_read_unsigned_id \<equiv> \<lambda>(rsz,brd). doN {
    ASSERT (rsz>0);
    (r,brd) \<leftarrow> brd_read_unsigned_id brd;
    RETURN (r,(rsz-1,brd))
  }"

definition brd_rs_read_unsigned_id_ndecr :: "brd_rs \<Rightarrow> (nat \<times> brd_rs) nres" where
  "brd_rs_read_unsigned_id_ndecr \<equiv> \<lambda>(rsz,brd). doN {
    (r,brd) \<leftarrow> brd_read_unsigned_id brd;
    RETURN (r,rsz,brd)
  }"
  
  
definition brd_rs_read_signed_id :: "brd_rs \<Rightarrow> (nat \<times> brd_rs) nres" where
  "brd_rs_read_signed_id \<equiv> \<lambda>(rsz,brd). doN {
    ASSERT (rsz>0);
    (r,brd) \<leftarrow> brd_read_signed_id brd;
    RETURN (r,(rsz-1,brd))
  }"

definition brd_rs_read_signed_id_ndecr :: "brd_rs \<Rightarrow> (nat \<times> brd_rs) nres" where
  "brd_rs_read_signed_id_ndecr \<equiv> \<lambda>(rsz,brd). doN {
    (r,brd) \<leftarrow> brd_read_signed_id brd;
    RETURN (r,rsz,brd)
  }"
  
  
lemma brd_rs_new_correct[simp]:
  "brd_rs_invar (brd_rs_new n)"  
  "brd_rs_remsize (brd_rs_new n) = n"  
  unfolding brd_rs_invar_def brd_rs_remsize_def brd_rs_new_def 
  by auto
  
lemma brd_rs_no_size_left_correct[simp]: "brd_rs_no_size_left brd \<longleftrightarrow> brd_rs_remsize brd = 0"  
  unfolding brd_rs_no_size_left_def brd_rs_remsize_def
  by auto
    
lemma brd_rs_read_correct[refine_vcg]: "\<lbrakk> brd_rs_invar brd; brd_rs_remsize brd > 0 \<rbrakk> 
  \<Longrightarrow> brd_rs_read brd \<le> SPEC (\<lambda>(_,brd'). brd_rs_remsize brd' < brd_rs_remsize brd \<and> brd_rs_invar brd')"
  unfolding brd_rs_read_def brd_rs_remsize_def brd_rs_invar_def
  apply refine_vcg
  by auto
    
lemma brd_rs_read_ulito_correct[refine_vcg]: "\<lbrakk> brd_rs_invar brd; brd_rs_remsize brd > 0 \<rbrakk> 
  \<Longrightarrow> brd_rs_read_ulito brd \<le> SPEC (\<lambda>(_,brd'). brd_rs_remsize brd' < brd_rs_remsize brd \<and> brd_rs_invar brd')"
  unfolding brd_rs_read_ulito_def brd_rs_remsize_def brd_rs_invar_def
  apply refine_vcg
  by auto

lemma brd_rs_read_unsigned_id_correct[refine_vcg]: "\<lbrakk> brd_rs_invar brd; brd_rs_remsize brd > 0 \<rbrakk> 
  \<Longrightarrow> brd_rs_read_unsigned_id brd \<le> SPEC (\<lambda>(_,brd'). brd_rs_remsize brd' < brd_rs_remsize brd \<and> brd_rs_invar brd')"
  unfolding brd_rs_read_unsigned_id_def brd_rs_remsize_def brd_rs_invar_def
  apply refine_vcg
  by auto

lemma brd_rs_read_unsigned_id_ndecr_correct[refine_vcg]: "\<lbrakk> brd_rs_invar brd \<rbrakk> 
  \<Longrightarrow> brd_rs_read_unsigned_id_ndecr brd \<le> SPEC (\<lambda>(_,brd'). brd_rs_remsize brd' = brd_rs_remsize brd \<and> brd_rs_invar brd')"
  unfolding brd_rs_read_unsigned_id_ndecr_def brd_rs_remsize_def brd_rs_invar_def
  apply refine_vcg
  by auto
  
  
lemma brd_rs_read_signed_id_correct[refine_vcg]: "\<lbrakk> brd_rs_invar brd; brd_rs_remsize brd > 0 \<rbrakk> 
  \<Longrightarrow> brd_rs_read_signed_id brd \<le> SPEC (\<lambda>(_,brd'). brd_rs_remsize brd' < brd_rs_remsize brd \<and> brd_rs_invar brd')"
  unfolding brd_rs_read_signed_id_def brd_rs_remsize_def brd_rs_invar_def
  apply refine_vcg
  by auto

lemma brd_rs_read_signed_id_ndecr_correct[refine_vcg]: "\<lbrakk> brd_rs_invar brd \<rbrakk> 
  \<Longrightarrow> brd_rs_read_signed_id_ndecr brd \<le> SPEC (\<lambda>(_,brd'). brd_rs_remsize brd' = brd_rs_remsize brd \<and> brd_rs_invar brd')"
  unfolding brd_rs_read_signed_id_ndecr_def brd_rs_remsize_def brd_rs_invar_def
  apply refine_vcg
  by auto
  

sepref_register brd_rs_read brd_rs_read_ulito 
  brd_rs_read_unsigned_id brd_rs_read_signed_id
  brd_rs_read_unsigned_id_ndecr brd_rs_read_signed_id_ndecr 
  brd_rs_remsize brd_rs_no_size_left

  
definition "brd_rs_assn \<equiv> size_assn \<times>\<^sub>a brd_assn"
  
sepref_def brd_rs_new_impl is "RETURN o brd_rs_new" :: "size_assn\<^sup>k \<rightarrow>\<^sub>a brd_rs_assn"
  unfolding brd_rs_new_def brd_rs_assn_def
  by sepref

  
sepref_def brd_rs_free_impl [llvm_inline] is "mop_free" :: "brd_rs_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn"
  unfolding mop_free_alt brd_rs_assn_def
  by sepref
  
lemmas brd_rs_free[sepref_frame_free_rules] = MK_FREE_mopI[OF brd_rs_free_impl.refine]
  
    
sepref_def brd_rs_remsize_impl [llvm_inline] is "RETURN o brd_rs_remsize" :: "brd_rs_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding brd_rs_remsize_def brd_rs_assn_def
  by sepref
  
sepref_def brd_rs_no_size_left_impl [llvm_inline] is "RETURN o brd_rs_no_size_left" :: "brd_rs_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding brd_rs_no_size_left_def brd_rs_assn_def
  apply (annot_snat_const size_T)
  by sepref

sepref_def brd_rs_read_impl [llvm_inline] is "brd_rs_read" :: "brd_rs_assn\<^sup>d \<rightarrow>\<^sub>a word_assn \<times>\<^sub>a brd_rs_assn"
  unfolding brd_rs_read_def brd_rs_assn_def
  apply (annot_snat_const size_T)
  by sepref

sepref_def brd_rs_read_ulito_impl [llvm_inline] is "brd_rs_read_ulito" :: "brd_rs_assn\<^sup>d \<rightarrow>\<^sub>a ulito_assn \<times>\<^sub>a brd_rs_assn"
  unfolding brd_rs_read_ulito_def brd_rs_assn_def
  apply (annot_snat_const size_T)
  by sepref

sepref_def brd_rs_read_unsigned_id_impl [llvm_inline] is "brd_rs_read_unsigned_id" :: "brd_rs_assn\<^sup>d \<rightarrow>\<^sub>a cid_assn \<times>\<^sub>a brd_rs_assn"
  unfolding brd_rs_read_unsigned_id_def brd_rs_assn_def
  apply (annot_snat_const size_T)
  by sepref

sepref_def brd_rs_read_unsigned_id_ndecr_impl [llvm_inline] is "brd_rs_read_unsigned_id_ndecr" :: "brd_rs_assn\<^sup>d \<rightarrow>\<^sub>a cid_assn \<times>\<^sub>a brd_rs_assn"
  unfolding brd_rs_read_unsigned_id_ndecr_def brd_rs_assn_def
  by sepref
  
sepref_def brd_rs_read_signed_id_impl [llvm_inline] is "brd_rs_read_signed_id" :: "brd_rs_assn\<^sup>d \<rightarrow>\<^sub>a cid_assn \<times>\<^sub>a brd_rs_assn"
  unfolding brd_rs_read_signed_id_def brd_rs_assn_def
  apply (annot_snat_const size_T)
  by sepref

sepref_def brd_rs_read_signed_id_ndecr_impl [llvm_inline] is "brd_rs_read_signed_id_ndecr" :: "brd_rs_assn\<^sup>d \<rightarrow>\<^sub>a cid_assn \<times>\<^sub>a brd_rs_assn"
  unfolding brd_rs_read_signed_id_ndecr_def brd_rs_assn_def
  by sepref

(*  
export_llvm 
  brd_parse_benc_ulito_impl
*)  
          

end

