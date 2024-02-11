section \<open>Clause Buffer\<close>  
theory DS_Clause_Buffer
imports 
  LRAT_Sepref_Base
  DS_Unsigned_Literal
begin

  text \<open>Array list to store a clause while it is being parsed\<close>
      
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


end
