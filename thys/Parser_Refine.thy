section \<open>Refining Grammars to Parsers\<close>
theory Parser_Refine
imports Parser_Input Ndet_Parser_Monad
begin

    
  definition "parser_spec1 g p \<equiv> \<forall>inp it xs it' r. 
    parsed inp it xs it' \<and> (xs,r)\<in>gM_rel g \<longrightarrow> p inp it \<le> RETURN ((r,False),it')"    
    
  definition "parser_spec2 P Q g p \<equiv> \<forall>inp it. i_valid inp it \<and> P inp it \<longrightarrow>
    p inp it \<le> SPEC (\<lambda>((r,err),it'). \<exists>xs. parsed inp it xs it' \<and> Q inp it r err it' \<and> (\<not>err \<longrightarrow> (xs,r)\<in>gM_rel g))"    

  definition "parser_spec2_unit P Q g p \<equiv> \<forall>inp it. i_valid inp it \<and> P inp it \<longrightarrow>
    p inp it \<le> SPEC (\<lambda>(err,it'). \<exists>xs. parsed inp it xs it' \<and> Q inp it err it' \<and> (\<not>err \<longrightarrow> (xs,())\<in>gM_rel g))"    
    
(*    
  lemma "parser_spec2 P Q g p = (\<forall>inp it. i_valid inp it \<and> P inp it \<longrightarrow> 
    p inp it \<le> SPEC (\<lambda>((r,err),it'). VALID_PARSE inp it it' \<and> Q inp it r err it' \<and> (\<not>err \<longrightarrow> PARSED inp it it' g r)))"  
    unfolding parser_spec2_def VALID_PARSE_def PARSED_def
    by (simp add: pw_le_iff refine_pw_simps) blast
*)    
    
        
  lemma parser_spec2I[intro?]: 
    assumes "\<And>inp it. \<lbrakk> i_valid inp it; P inp it \<rbrakk> \<Longrightarrow> p inp it \<le> SPEC (\<lambda>((r,err),it'). \<exists>xs. parsed inp it xs it' \<and> Q inp it r err it' \<and> (\<not>err \<longrightarrow> (xs,r)\<in>gM_rel g))"
    shows "parser_spec2 P Q g p"  
    using assms unfolding parser_spec2_def by auto
    
  lemma parser_spec2D:
    assumes "parser_spec2 P Q g p"  
    assumes "i_valid inp it"
    assumes "P inp it"
    shows "p inp it \<le> SPEC (\<lambda>((r,err),it'). \<exists>xs. parsed inp it xs it' \<and> Q inp it r err it' \<and> (\<not>err \<longrightarrow> (xs,r)\<in>gM_rel g))"
    using assms unfolding parser_spec2_def by auto
    
  lemma parser_spec2_unitI[intro?]: 
    assumes "\<And>inp it. \<lbrakk> i_valid inp it; P inp it \<rbrakk> \<Longrightarrow> p inp it \<le> SPEC (\<lambda>(err,it'). \<exists>xs. parsed inp it xs it' \<and> Q inp it err it' \<and> (\<not>err \<longrightarrow> (xs,())\<in>gM_rel g))"
    shows "parser_spec2_unit P Q g p"  
    using assms unfolding parser_spec2_unit_def by auto
    
  lemma parser_spec2_unitD:
    assumes "parser_spec2_unit P Q g p"  
    assumes "i_valid inp it"
    assumes "P inp it"
    shows "p inp it \<le> SPEC (\<lambda>(err,it'). \<exists>xs. parsed inp it xs it' \<and> Q inp it err it' \<and> (\<not>err \<longrightarrow> (xs,())\<in>gM_rel g))"
    using assms unfolding parser_spec2_unit_def by auto
    
    
  (* parser_spec2 will be enough for now, as that's partial correctness! *)
    
    
  definition "parser_spec g inp it \<equiv> doN { 
    ASSERT (i_valid inp it); 
    SPEC (\<lambda>((r,err),it'). i_remsize inp it' \<le> i_remsize inp it 
      \<and> (if err then \<forall>xs it'. parsed inp it xs it' \<longrightarrow> xs\<notin>Domain (gM_rel g)
         else \<exists>xs. parsed inp it xs it' \<and> (xs,r)\<in>gM_rel g
      ))
  }"
      


  (* TODO: Move *)  
  
  lemma parsed'_parse: 
    "parsed inp it xs1 it1 \<Longrightarrow> parsed inp it1 xs2 it2 \<Longrightarrow> parsed inp it (xs1@xs2) it2"
    by auto  
  lemma parsed'_parse1: 
    "parsed1 inp it x it1 \<Longrightarrow> parsed inp it1 xs2 it2 \<Longrightarrow> parsed inp it (x#xs2) it2"
    by auto
  
  lemma parsed'_finish: 
    "parsed inp it xs it1 \<Longrightarrow> parsed inp it xs it1"  
    "parsed1 inp it x it1 \<Longrightarrow> parsed inp it [x] it1"  
    by auto
    
    
  method g_parsed = ((determ \<open>erule parsed'_finish parsed'_parse parsed'_parse1\<close>)+) []  



context begin interpretation lang_syntax .    
    
  lemma gI_cons: "\<lbrakk> (w,r) \<in> gM_rel m; w=w'; r=r' \<rbrakk> \<Longrightarrow> (w',r')\<in>gM_rel m" by simp
  
  lemma g_starr_emptyI: "([],snd fi) \<in> gM_rel (g *& fi)"
    apply (subst g_starr_unfold)
    by igr

  lemma g_starr_stepI:
    assumes "(xs\<^sub>1,r\<^sub>1) \<in> gM_rel g"
    assumes "(xs\<^sub>2,r\<^sub>2) \<in> gM_rel (g *& fi)"
    shows "(xs\<^sub>1@xs\<^sub>2,fst fi r\<^sub>1 r\<^sub>2) \<in> gM_rel (g *& fi)"  
    apply (subst g_starr_unfold)
    using assms
    by igr

  lemma g_starl_emptyI:
    shows "([],snd fi) \<in> gM_rel (g &* fi)"
    apply (subst g_starl_unfold)
    by igr

  lemma g_starl_stepI:
    assumes "(xs\<^sub>1,r\<^sub>1) \<in> gM_rel (g &* fi)"
    assumes "(xs\<^sub>2,r\<^sub>2) \<in> gM_rel g"
    shows "(xs\<^sub>1@xs\<^sub>2,fst fi r\<^sub>1 r\<^sub>2) \<in> gM_rel (g &* fi)"  
    apply (subst g_starl_unfold)
    using assms
    by igr
    
        
  lemma g_charI: "c\<in>C \<Longrightarrow> ([c],c) \<in> gM_rel <C>"  
    by (auto simp: g_char_def)
          
  lemma g_returnI: "([],x) \<in> gM_rel (g_return x)" by igr
    
  lemma g_bindI: 
    assumes "(w\<^sub>1,a) \<in> gM_rel m"
    assumes "(w\<^sub>2,r) \<in> gM_rel (f a)"
    shows "(w\<^sub>1@w\<^sub>2,r) \<in> gM_rel ( do { x\<leftarrow>m; f x } )"  
    using assms by (simp add: igr_bind) blast
    
  lemma g_bind1I: 
    assumes "([c],a) \<in> gM_rel m"
    assumes "(w\<^sub>2,r) \<in> gM_rel (f a)"
    shows "(c#w\<^sub>2,r) \<in> gM_rel ( do { x\<leftarrow>m; f x } )"  
    using assms g_bindI[of "[c]" a m w\<^sub>2 r f] by simp
    
  lemma g_ignore_leftI: 
    assumes "(w\<^sub>1,a) \<in> gM_rel m\<^sub>1"
    assumes "(w\<^sub>2,r) \<in> gM_rel m\<^sub>2"
    shows "(w\<^sub>1@w\<^sub>2,r) \<in> gM_rel ( m\<^sub>1 \<ggreater> m\<^sub>2 )"  
    using assms unfolding g_ignore_left_def by igr

  lemma g_ignore_left1I: 
    assumes "([c],a) \<in> gM_rel m\<^sub>1"
    assumes "(w\<^sub>2,r) \<in> gM_rel m\<^sub>2"
    shows "(c#w\<^sub>2,r) \<in> gM_rel ( m\<^sub>1 \<ggreater> m\<^sub>2 )"  
    using assms g_ignore_leftI[of "[c]"] by auto

  lemma g_ignore_rightI: 
    assumes "(w\<^sub>1,r) \<in> gM_rel m\<^sub>1"
    assumes "(w\<^sub>2,a) \<in> gM_rel m\<^sub>2"
    shows "(w\<^sub>1@w\<^sub>2,r) \<in> gM_rel ( m\<^sub>1 \<lless> m\<^sub>2 )"  
    using assms unfolding g_ignore_right_def 
    by igr
        
    
  lemma g_unionI_left: "(w,r)\<in>gM_rel a \<Longrightarrow> (w,r)\<in>gM_rel ( a <|> b )" by igr 
  lemma g_unionI_right: "(w,r)\<in>gM_rel b \<Longrightarrow> (w,r)\<in>gM_rel ( a <|> b )" by igr 
    
    
  lemma g_applyI:
    assumes "(w,r) \<in> gM_rel m"
    shows "(w,f r) \<in> gM_rel (m <&> f)"
    using assms
    by (simp add: igr_eq_iff igr_simps; blast)  
    
  lemma g_mk_empty_leftI: "([]@xs,r)\<in>gM_rel g \<Longrightarrow> (xs,r)\<in>gM_rel g" by simp
  lemma g_mk_empty_rightI: "(xs@[],r)\<in>gM_rel g \<Longrightarrow> (xs,r)\<in>gM_rel g" by simp
  

end



end
