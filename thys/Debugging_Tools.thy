theory Debugging_Tools
imports DS_Unsigned_Literal 
begin

  (*
    Tools for debugging.
    
    While we prove our verifier to be sound, 
    making it complete requires standard debugging techniques!
  *)

  definition "word_of_ulit l \<equiv> word_of_nat (op_unat_snat_upcast TYPE(size_t) l) :: size_t word"
  sepref_register word_of_ulit
  sepref_def word_of_ulit_impl [llvm_inline] is "RETURN o word_of_ulit" :: "lit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn"
    unfolding word_of_ulit_def supply [simp] = is_up' by sepref
    
  definition "word_of_lit l \<equiv> word_of_nat (op_unat_snat_upcast TYPE(size_t) (ulit_of l)) :: size_t word"
  sepref_register word_of_lit
  sepref_def word_of_lit_impl [llvm_inline] is "RETURN o word_of_lit" :: "ulit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn"
    unfolding word_of_lit_def supply [simp] = is_up' by sepref
  
  definition "word_of_lito l \<equiv> word_of_nat (op_unat_snat_upcast TYPE(size_t) (ulito_of l)) :: size_t word"
  sepref_register word_of_lito
  sepref_def word_of_lito_impl [llvm_inline] is "RETURN o word_of_lito" :: "ulito_assn\<^sup>k \<rightarrow>\<^sub>a word_assn"
    unfolding word_of_lito_def supply [simp] = is_up' by sepref

  definition [simp]: "ll_dbg_tag_err_code (err::size_t word) (info::size_t word) \<equiv> RETURN ()"  
  lemma [refine_vcg]: "ll_dbg_tag_err_code c i \<le> SPEC (\<lambda>_. True)" by simp 
  sepref_register ll_dbg_tag_err_code
  sepref_def ll_dbg_tag_err_code_impl is "uncurry ll_dbg_tag_err_code" :: "word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn"
    unfolding ll_dbg_tag_err_code_def
    by sepref

  definition [simp]: "ll_dbg_tag_info_code (c::size_t word) (i::size_t word) \<equiv> RETURN ()"  
  lemma [refine_vcg]: "ll_dbg_tag_info_code c i \<le> SPEC (\<lambda>_. True)" by simp 
  sepref_register ll_dbg_tag_info_code
  sepref_def ll_dbg_tag_info_code_impl is "uncurry ll_dbg_tag_info_code" :: "word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn"
    unfolding ll_dbg_tag_info_code_def
    by sepref

    
  definition [simp]: "ll_dbg_tag_parsed (c::size_t word) (i::size_t word) \<equiv> RETURN ()"  
  lemma [refine_vcg]: "ll_dbg_tag_parsed c i \<le> SPEC (\<lambda>_. True)" by simp 
  sepref_register ll_dbg_tag_parsed
  sepref_def ll_dbg_tag_parsed_impl is "uncurry ll_dbg_tag_parsed" :: "word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn"
    unfolding ll_dbg_tag_parsed_def
    by sepref

  abbreviation "PARSED_CNF_LIT l \<equiv> ll_dbg_tag_parsed 0x1 (word_of_lit l)"      
    
  abbreviation "PARSED_LRAT_ADD cid \<equiv> ll_dbg_tag_parsed 0x2 (word_of_cid cid)"
  abbreviation "PARSED_LRAT_LIT l \<equiv> ll_dbg_tag_parsed 0x3 (word_of_lito l)"

  abbreviation "PARSED_LRAT_ID cid \<equiv> ll_dbg_tag_parsed 0x4 (word_of_cid cid)"
    
  abbreviation "ERROR \<equiv> \<lambda>c. ll_dbg_tag_err_code c 0"

  abbreviation "ERROR_size \<equiv> \<lambda>c s. ll_dbg_tag_err_code c (word_of_nat s)"
  abbreviation "ERROR_cid \<equiv> \<lambda>c s. ll_dbg_tag_err_code c (word_of_cid s)"
  abbreviation "ERROR_lit \<equiv> \<lambda>c s. ll_dbg_tag_err_code c (word_of_lit s)"
  abbreviation "ERROR_lito \<equiv> \<lambda>c s. ll_dbg_tag_err_code c (word_of_lito s)"

  
  abbreviation "INFO \<equiv> \<lambda>c. ll_dbg_tag_info_code c 0"

  abbreviation "INFO_size \<equiv> \<lambda>c s. ll_dbg_tag_info_code c (word_of_nat s)"
  abbreviation "INFO_cid \<equiv> \<lambda>c s. ll_dbg_tag_info_code c (word_of_cid s)"
  abbreviation "INFO_lit \<equiv> \<lambda>c s. ll_dbg_tag_info_code c (word_of_lit s)"
  abbreviation "INFO_lito \<equiv> \<lambda>c s. ll_dbg_tag_info_code c (word_of_lito s)"

  abbreviation "INFO_ulit \<equiv> \<lambda>c s. ll_dbg_tag_info_code c (word_of_ulit s)"
        
  abbreviation (input) "err_code_syntax_error \<equiv> 0x1"

end
