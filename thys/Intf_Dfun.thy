theory Intf_Dfun
imports Isabelle_LLVM.IICF
begin

text \<open>Functions with default value\<close>

definition [to_relAPP]: "dfun_rel K V \<equiv> K\<rightarrow>V"
sepref_decl_intf ('k,'v) i_dfun is "'k \<Rightarrow> 'v"

lemma [synth_rules]: "\<lbrakk>INTF_OF_REL K TYPE('k); INTF_OF_REL V TYPE('v)\<rbrakk> 
  \<Longrightarrow> INTF_OF_REL (\<langle>K,V\<rangle>dfun_rel) TYPE(('k,'v) i_dfun)" by simp
    
context
  fixes dflt :: 'a
begin 

  definition [simp]: "op_dfun_empty = (\<lambda>_. dflt)"
  definition [simp]: "op_dfun_lookup f k = f k"
  definition [simp]: "op_dfun_upd f k v = f(k:=v)"
  definition [simp]: "op_dfun_reset f k = f(k:=dflt)"  
  definition [simp]: "op_dfun_clear (f::'b\<Rightarrow>'a) = (\<lambda>_::'b. dflt)"  
  
  sepref_register 
    op_dfun_empty :: "('k,'v) i_dfun"
    op_dfun_lookup :: "('k,'v) i_dfun \<Rightarrow> 'k \<Rightarrow> 'v"
    op_dfun_upd :: "('k,'v) i_dfun \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k,'v) i_dfun"
    op_dfun_reset :: "('k,'v) i_dfun \<Rightarrow> 'k \<Rightarrow> ('k,'v) i_dfun"
    op_dfun_clear :: "('k,'v) i_dfun \<Rightarrow> ('k,'v) i_dfun"
      
end

end
