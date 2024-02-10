theory Proto_Sepref_Ghostvar
imports Isabelle_LLVM.Proto_Sepref_Borrow
begin



  text \<open>
    Not exactly a variable, but inserted as placeholder for a dropped abstract variable.
    In case the preprocessor does not get this out, we define it to be actually executable
  \<close>
  definition [llvm_inline]: "ghost_var \<equiv> init"
  
  
  definition "any_rel \<equiv> UNIV :: ('a\<times>'b) set"
  abbreviation "any_assn \<equiv> pure any_rel"

  text \<open>To drop a variable, we refine to a 'placeholder' with arbitrary 1::word type\<close>
  abbreviation drop_assn :: "_ \<Rightarrow> 1 word \<Rightarrow> assn" where "drop_assn \<equiv> any_assn"
  
  text \<open>To drop a variable, but retain information about the abstract value, we add an abstract bound\<close>
  abbreviation dropi_assn :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 1 word \<Rightarrow> assn" where "dropi_assn P \<equiv> b_assn any_assn P"
  
    
    
    
    
    
end
