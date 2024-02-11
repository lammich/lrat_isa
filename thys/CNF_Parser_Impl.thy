section \<open>CNF Parser\<close>

theory CNF_Parser_Impl
imports CNF_Grammar Debugging_Tools DS_Clause_Database
begin

context begin interpretation lang_syntax .    

(* TODO: Move *)
  lemma bind_K_return_conv: "m \<ggreater> g_return x = m <&> (\<lambda>_. x)"
    by (simp add: g_ignore_left_def igr_eq_iff igr_simps)  


    
      
  lemma g_lift2_then_apply_extract_first: "(g_lift2 f m\<^sub>1 m\<^sub>2) <&> g = do { a\<leftarrow>m\<^sub>1; m\<^sub>2 <&> (g o f a) }"
    unfolding g_apply_def g_lift2_def  
    by simp
  
  lemma g_lift2_then_apply: "g_lift2 f a b <&> g = g_lift2 (\<lambda>x y. g (f x y)) a b"  
    unfolding g_apply_def g_lift2_def  
    by simp
    



        
subsection \<open>Parse character\<close>
      
  definition "p_char pc inp it \<equiv> doN { 
      ASSERT (i_valid inp it);
      if i_eof inp it then RETURN ((0,True),it) 
      else doN {
        (c,it')\<leftarrow>i_read inp it; 
        
        if c=pc then
          RETURN ((c,False),it')
        else
          RETURN ((c,True), it')
      } 
    }"
  
  lemma p_char_correct: "parser_spec2 top (\<lambda>inp it _ err it'. \<not>err \<longrightarrow> i_remsize inp it = i_remsize inp it'+1) (g_char {c}) (p_char c)"
    apply rule
    unfolding p_char_def
    apply (refine_vcg)
    apply (clarsimp_all simp: parsed_remsize parsed1_remsize)
    
    apply (intro exI conjI)
    apply g_parsed
    
    apply (blast intro: g_charI)
    
    
    apply (intro exI conjI)
    apply g_parsed
    done    
  

  abbreviation "rdm_parser_assn A \<equiv> (A \<times>\<^sub>a bool1_assn) \<times>\<^sub>a rdmem_it_assn"  
  abbreviation "rdm_parser_unit_assn \<equiv> bool1_assn \<times>\<^sub>a rdmem_it_assn"  
    
  sepref_register p_char  
  sepref_def p_char_impl is "uncurry2 p_char" :: "id_assn\<^sup>k *\<^sub>a rdmem_inp_assn\<^sup>k *\<^sub>a rdmem_it_assn\<^sup>d \<rightarrow>\<^sub>a rdm_parser_assn id_assn" 
    unfolding p_char_def
    by sepref
    
subsection \<open>Skip to\<close>
    
  definition "parse_skip_to ct inp it \<equiv> doN {
    (it,_,err) \<leftarrow> WHILEIT 
    (\<lambda>(it',brk,err). (err \<longrightarrow> brk) \<and> (\<exists>xs.
          parsed inp it xs it' 
        \<and> (\<not>brk \<longrightarrow> (xs,()) \<in> gM_rel (< -{ct} > &* ceIgnore ) )
        \<and> (brk \<and> \<not>err \<longrightarrow> (xs,()) \<in> gM_rel (< -{ct} > &* ceIgnore \<ggreater> <{ct}> \<ggreater> g_return () ) )
    ))
    (\<lambda>(it,brk,_). \<not>brk) (\<lambda>(it,_,_). doN {
      ASSERT (i_valid inp it);
      if i_eof inp it then RETURN (it,True,True)
      else doN {
        (c,it) \<leftarrow> i_read inp it;
        if c=ct then RETURN (it,True,False)
        else RETURN (it,False,False)      
      }
    }) (it,False,False);
    
    RETURN (err,it)
  }"

  definition "cnf_aux_skip_to ct \<equiv> < -{ct} > *&ceIgnore \<ggreater> <{ct}> \<ggreater> g_return ()"
      

        
  lemma parse_skip_to_correct: "parser_spec2_unit top top (cnf_aux_skip_to ct) (parse_skip_to ct)"
    unfolding cnf_aux_skip_to_def acam_ignore.g_starr_conv_l
    apply rule
    subgoal for inp it
      unfolding parse_skip_to_def 
      apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(it,brk,err). i_remsize inp it + (1-of_bool err))"])
      apply (clarsimp_all simp: parsed_remsize parsed1_remsize)
      subgoal
        apply (rule gI_cons)
        apply (rule g_starl_emptyI)
        by auto
        
      subgoal
        apply (rule exI)
        apply g_parsed
        done
        
      subgoal
        apply (simp add: bind_K_return_conv)
        apply (rule exI, rule conjI)
        apply g_parsed
        
        apply (rule g_applyI)
        apply (rule g_ignore_leftI)
        apply assumption
        apply (rule g_charI)
        by simp
      subgoal
        apply (rule exI, rule conjI)
        apply g_parsed
        apply (rule gI_cons)
        apply (rule g_starl_stepI; simp?)
        apply (rule g_charI)
        by auto
        
      done
    done    

  sepref_register parse_skip_to
  
  sepref_def parse_skip_to_impl is "uncurry2 parse_skip_to" :: "id_assn\<^sup>k *\<^sub>a rdmem_inp_assn\<^sup>k *\<^sub>a rdmem_it_assn\<^sup>d \<rightarrow>\<^sub>a rdm_parser_unit_assn"  
    unfolding parse_skip_to_def
    by sepref   
    

  subsection \<open>Skip block (p...\n or c...\n block)\<close>      
    
  definition "parse_skip_block cb inp it \<equiv> doN {
    ((_,err),it) \<leftarrow> p_char cb inp it;
    if err then RETURN (err,it)
    else parse_skip_to char_LF inp it
  }"  

  definition "cnf_aux_block cb \<equiv> do {<{cb}>; cnf_aux_skip_to char_LF }"
  
  lemma parse_skip_block_correct:
    "parser_spec2_unit top (\<lambda>inp it err it'. \<not>err \<longrightarrow> i_remsize inp it' < i_remsize inp it) ( cnf_aux_block cb ) (parse_skip_block cb)"
    apply rule
    subgoal for inp it
      unfolding parse_skip_block_def cnf_aux_block_def
      apply (refine_vcg 
        parser_spec2D[OF p_char_correct]
        parser_spec2_unitD[OF parse_skip_to_correct]
      )

      apply clarsimp_all
      
      apply (intro exI conjI impI)
      apply g_parsed
      
      
      apply (simp add: parsed_remsize; fail)
              
      apply (blast intro: g_bindI)
      done
    done            

  sepref_register parse_skip_block
  
  sepref_def parse_skip_block_impl is "uncurry2 parse_skip_block" :: "id_assn\<^sup>k *\<^sub>a rdmem_inp_assn\<^sup>k *\<^sub>a rdmem_it_assn\<^sup>d \<rightarrow>\<^sub>a rdm_parser_unit_assn"  
    unfolding parse_skip_block_def
    by sepref

    
  subsection \<open>Variable\<close>  
      
  (* Refine towards executable version *)        
  lemma cnf_variable_refine1: "cnf_variable = (do {
      a \<leftarrow> <digits1>;
      <digits> &* (\<lambda>c s. 10 * c + val_of_digit s, val_of_digit a)
    }) <&> var_of_nat"
  proof -
    {
      fix f a
      have "<digits> *& ceCons <&> (\<lambda>x. var_of_nat (fold f x a)) = <digits> *& ceCons <&> (\<lambda>x. (fold f x a)) <&> var_of_nat"
        by (simp add: comp_def)
      also have "<digits> *& ceCons <&> (\<lambda>x. (fold f x a)) = <digits> &* (\<lambda>c s. f s c,a)"
        by (simp add: g_starr_fold_conv)
      finally have " <digits> *& ceCons <&> (\<lambda>x. var_of_nat (fold f x a)) = <digits> &* (\<lambda>c s. f s c, a) <&> var_of_nat" .
    } note aux=this
    
    show ?thesis      
      unfolding cnf_variable_def nat_of_ascii_def var_of_ascii_def
      apply (simp add: g_lift2_then_apply_extract_first comp_def)
      apply (subst aux)
      by igr (* TODO: bind-apply simp lemma*)
      
  qed      
    
  
  definition "mx_valid mx \<equiv> 0<mx \<and> 10*mx+9<max_size"  
    
  definition "parse_unsigned_loop mx v\<^sub>0 inp it \<equiv> doN {
    ASSERT(mx_valid mx);
  
    (it,res,brk) \<leftarrow> WHILEIT 
      (\<lambda>(it',res,brk). \<exists>xs. 
          parsed inp it xs it' 
        \<and> (xs,res) \<in> gM_rel (<digits> &* (\<lambda>c s. 10 * c + val_of_digit s, v\<^sub>0)) 
        \<and> (brk \<and> \<not>i_eof inp it' \<longrightarrow> hd (i_rem inp it') \<notin> digits)
      ) 
      (\<lambda>(it,res,brk). \<not>brk \<and> \<not>i_eof inp it \<and> res\<le>mx) 
      (\<lambda>(it,res,brk). doN {
        c \<leftarrow> i_peek inp it;
      
        if c\<in>digits then doN {
          it \<leftarrow> i_next inp it;
          let c = val_of_digit c;
          let c = op_unat_snat_upcast size_T c;
          ASSERT (c \<in> {0..9});
          ASSERT ( 10*res + c < max_size );
          let res = 10*res + c;
          RETURN (it,res,brk)
        } else RETURN (it,res,True)        
    }) (it,v\<^sub>0,False);
    
    let err = res>mx;
  
    RETURN ((res,err),it)
  }"
    
  lemma val_of_digit_le9: "c\<in>digits \<Longrightarrow> val_of_digit c \<le> 9"
    using val_of_digit_lt10[of c] by linarith 
  
  lemma parsed1_from_peek_nextI:
    assumes "i_rem inp it' = tl (i_rem inp it)" "i_valid inp it'" "i_remsize inp it' < i_remsize inp it"    
    shows "parsed1 inp it (hd (i_rem inp it)) it'"
    using assms
    unfolding parsed1_def i_remsize_def
    apply (cases inp; cases it; cases it')
    by (auto)
    
    
  lemma parse_unsigned_loop_correct:
    assumes "mx_valid mx"
    shows "parser_spec2 top (\<lambda>inp it r err it'. \<not>err \<longrightarrow> r\<le>mx \<and> (i_eof inp it' \<or> hd (i_rem inp it') \<notin> digits))
      (<digits> &* (\<lambda>c s. 10 * c + val_of_digit s, v\<^sub>0))
      (parse_unsigned_loop mx v\<^sub>0)
    "   
    apply rule
    subgoal for inp it
      unfolding parse_unsigned_loop_def
      apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(it,res,brk). i_remsize inp it + (1-of_bool brk))"])
      apply (simp add: assms)
          
      apply (clarsimp_all)
      
      subgoal
        apply (rule gI_cons)
        apply (rule g_starl_emptyI)
        by auto
        
      subgoal by (simp add: val_of_digit_le9)
      
      subgoal
        unfolding mx_valid_def by simp
      
      subgoal
        apply (drule (2) parsed1_from_peek_nextI)
        
        apply (intro exI conjI)
        apply g_parsed

        apply (rule gI_cons)
        apply (rule g_starl_stepI)
        apply assumption        
        apply (rule g_charI)
        apply simp
        apply simp
        by simp

      subgoal for it' brk res xs
      
        apply (intro exI conjI)
        apply g_parsed
        by auto
      
      done        
    done    
              
    
  sepref_register parse_unsigned_loop  
  
  sepref_def parse_unsigned_loop_impl [llvm_inline] is "uncurry3 parse_unsigned_loop" 
    :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a rdmem_inp_assn\<^sup>k *\<^sub>a rdmem_it_assn\<^sup>d \<rightarrow>\<^sub>a rdm_parser_assn size_assn"
    unfolding parse_unsigned_loop_def is_whitespace_alt val_of_digit_def is_digit_alt
    supply [simp] = is_up'
    apply (annot_snat_const size_T)
    by sepref  
    
    
    

  definition "parse_variable inp it \<equiv> doN {
    ASSERT (\<not>i_eof inp it \<and> i_valid inp it);
    
    (c,it)\<leftarrow>i_read inp it;
    
    if c\<notin>digits1 then doN {
      RETURN ((some_var,True),it)
    }
    else doN {
      let c = val_of_digit c;
      let c = op_unat_snat_upcast size_T c;
    
      ((v,err),it) \<leftarrow> parse_unsigned_loop max_var_incl_size c inp it;
      
      if err then doN {
        RETURN ((some_var,err),it)
      } else doN {
        v \<leftarrow> mk_dimacs_var v;
        RETURN ((v,err),it)
      }
      
    }
  }"  
  
  
  lemma fold_digits_bound: "v\<^sub>0 \<le> fold (\<lambda>s c. 10 * c + val_of_digit s) xs v\<^sub>0"  
    apply (induction xs arbitrary: v\<^sub>0)
    apply simp
    apply (simp) 
    apply (rule order_trans[rotated])
    apply assumption
    by simp
    
  lemma parse_digits_bound:
    assumes "(xs,res) \<in> gM_rel (<digits> &* (\<lambda>c s. 10 * c + val_of_digit s, v\<^sub>0))"
    shows "res \<ge> v\<^sub>0"
    using assms
    apply -
    apply (subst (asm) g_starr_fold_conv[symmetric])
    supply [simp] = fold_digits_bound
    by igr'
  
  
  lemma parse_variable_correct:
    shows "parser_spec2 (\<lambda>inp it. \<not>i_eof inp it) (\<lambda>inp it r err it'. \<not>err \<longrightarrow> i_eof inp it' \<or> hd (i_rem inp it') \<notin> digits)
            cnf_variable (parse_variable)"
      
    apply rule
    unfolding parse_variable_def cnf_variable_refine1
    apply (refine_vcg parser_spec2D[OF parse_unsigned_loop_correct])      
    
    apply (clarsimp_all simp: max_snat_def mx_valid_def)
    
    subgoal
      apply (intro exI conjI)
      apply g_parsed
      done

    subgoal
      apply (intro exI conjI)
      apply g_parsed
      done
        
    subgoal
      apply (drule parse_digits_bound)
      apply (auto 
        simp: val_of_digit_def is_digit1_alt
        simp: is_digit_alt word_unat_eq_iff word_le_nat_alt unat_sub
      )
      done
      
    subgoal
      apply (intro exI conjI)
      apply g_parsed
      
      apply (rule g_applyI)
      apply (rule g_bind1I)
      apply (rule g_charI; simp)
      by simp
      
    done    

    
  sepref_register parse_variable
  sepref_def parse_variable_impl [llvm_inline] is "uncurry parse_variable" :: "rdmem_inp_assn\<^sup>k *\<^sub>a rdmem_it_assn\<^sup>d \<rightarrow>\<^sub>a rdm_parser_assn dimacs_var_assn"  
    unfolding parse_variable_def val_of_digit_def is_digit1_alt
    supply [simp] = is_up'
    by sepref
    

  subsection \<open>Literal\<close>  
        
  definition "parse_literal inp it\<^sub>0 \<equiv> doN {
    ASSERT (\<not>i_eof inp it\<^sub>0);
    
    c\<leftarrow>i_peek inp it\<^sub>0;
    
    (sign,it) \<leftarrow> if c=char_MINUS then doN {
      it \<leftarrow> i_next inp it\<^sub>0;
      ASSERT (parsed1 inp it\<^sub>0 char_MINUS it); \<comment> \<open>TODO: make rule for i_next, that creates parsed-info!\<close>
      RETURN (True,it)
    } else RETURN (False,it\<^sub>0);

    ASSERT (i_valid inp it);
    
    if i_eof inp it then
      RETURN ((some_lit,True),it)
    else doN {
      ((v,err),it) \<leftarrow> parse_variable inp it;

      let l = (if sign then Neg v else Pos v);

      RETURN ((l,err),it)
    }   
  }"  
    
    
  lemma parse_literal_correct:
    shows "parser_spec2 (\<lambda>inp it. \<not>i_eof inp it) (\<lambda>inp it r err it'. \<not>err \<longrightarrow> i_eof inp it' \<or> hd (i_rem inp it') \<notin> digits)
            cnf_literal (parse_literal)"
  
    apply rule
    unfolding parse_literal_def
    apply (refine_vcg parser_spec2D[OF parse_variable_correct])      
    
    apply (clarsimp_all)
            
    subgoal 
      apply (drule (1) parsed1_from_peek_nextI, simp)
      by simp
      
    subgoal
      apply (intro exI conjI)
      apply g_parsed
      done
      
    subgoal
      apply (intro exI conjI)
      apply g_parsed
      
      apply clarsimp
        
      unfolding cnf_literal_def
      
      apply (rule g_unionI_left)
      apply (rule g_applyI)
      apply (rule g_ignore_left1I)
      apply (rule g_charI, simp)
      by simp
      
    subgoal
      apply (intro exI conjI)
      apply g_parsed
      
      apply clarsimp
        
      unfolding cnf_literal_def
      apply (rule g_unionI_right)
      apply (rule g_applyI)
      by simp    
    done  


  sepref_register parse_literal
  
  sepref_def parse_literal_impl [llvm_inline] is "uncurry parse_literal" :: "rdmem_inp_assn\<^sup>k *\<^sub>a rdmem_it_assn\<^sup>d \<rightarrow>\<^sub>a rdm_parser_assn ulit_assn"
    unfolding parse_literal_def
    by sepref

  subsection \<open>Whitespace\<close>  
           
  definition "parse_whitespace inp it \<equiv> doN {
    (it,_)\<leftarrow>WHILEIT 
      (\<lambda>(it',brk). \<exists>xs. parsed inp it xs it' \<and> (xs,()) \<in> gM_rel (<whitespace> &* ceIgnore ) )
      (\<lambda>(it,brk). \<not>brk \<and> \<not>i_eof inp it)
      (\<lambda>(it,brk). doN {
        c \<leftarrow> i_peek inp it;
        
        if c\<in>whitespace then doN {
          it \<leftarrow> i_next inp it;
          RETURN (it,False)
        } else
          RETURN (it,True)
      })
      (it,False);
      
    RETURN (False,it)  
  }"
    
  lemma parse_whitespace_correct: "parser_spec2_unit top (\<lambda>inp it err it'. \<not>err) cnf_ws parse_whitespace"
    apply rule
    subgoal for inp it
      unfolding cnf_ws_def acam_ignore.g_starr_conv_l
      unfolding parse_whitespace_def 
      
      apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(it,brk). i_remsize inp it + (1-of_bool brk))"])
      apply (clarsimp_all)
      
      subgoal
        apply (rule gI_cons)
        apply (rule g_starl_emptyI)
        by auto
      
      subgoal
        apply (drule (2) parsed1_from_peek_nextI)
        
        apply (intro exI conjI)
        apply g_parsed
        
        apply (rule gI_cons)
        apply (rule g_starl_stepI, assumption)
        apply (rule g_charI)
        apply simp
        apply simp
        apply simp
        done
      done
    done    

  sepref_register parse_whitespace
  sepref_def parse_whitespace_impl [llvm_inline] is "uncurry parse_whitespace" :: "rdmem_inp_assn\<^sup>k *\<^sub>a rdmem_it_assn\<^sup>d \<rightarrow>\<^sub>a rdm_parser_unit_assn"
    unfolding parse_whitespace_def is_whitespace_alt
    by sepref 
    
    
  definition "parse_whitespace1 inp it \<equiv> doN {
    ASSERT(i_valid inp it);
    if i_eof inp it then RETURN (True,it)
    else doN {
      (c,it) \<leftarrow> i_read inp it;
      if c\<in>whitespace then doN {
        (_,it) \<leftarrow> parse_whitespace inp it;
        RETURN (False,it)
      } else RETURN (True,it)
    }
  }"  
    
  lemma parse_whitespace1_correct: "parser_spec2_unit top (\<lambda>inp it err it'. \<not>err\<longrightarrow>i_remsize inp it' < i_remsize inp it) cnf_ws1 parse_whitespace1"
    apply rule
    subgoal for inp it
      unfolding cnf_ws1_def 
      unfolding parse_whitespace1_def 
      apply (refine_vcg parser_spec2_unitD[OF parse_whitespace_correct])
      apply clarsimp_all
      
      subgoal
        apply (intro exI conjI)
        apply g_parsed
      
        apply (simp add: parsed1_remsize parsed_remsize; fail)
        apply (rule g_ignore_left1I)
        apply (rule g_charI, simp)
        by simp
      
      subgoal
        apply (intro exI conjI)
        by g_parsed
        
      done
    done    

  sepref_register parse_whitespace1
  sepref_def parse_whitespace1_impl [llvm_inline] is "uncurry parse_whitespace1" :: "rdmem_inp_assn\<^sup>k *\<^sub>a rdmem_it_assn\<^sup>d \<rightarrow>\<^sub>a rdm_parser_unit_assn"
    unfolding parse_whitespace1_def is_whitespace_alt
    by sepref 
    
    
    
  subsection \<open>Clause\<close>         
        
  definition "parse_clause inp it \<equiv> doN {
    (res,it,err,brk) \<leftarrow> WHILEIT 
      (\<lambda>(res,it',err,brk). (err\<longrightarrow>brk) \<and> (\<exists>xs. 
          parsed inp it xs it' 
        \<and> (\<not>err \<longrightarrow> (
            (\<not>brk \<longrightarrow> (xs,res) \<in> gM_rel ( (cnf_literal \<lless> cnf_ws1) &* ceRevInsert)) 
          \<and> (brk \<longrightarrow> (xs,res) \<in> gM_rel ( (cnf_literal \<lless> cnf_ws1) &* ceRevInsert \<lless> <{char_0}>))  
          ))
      )) 
      (\<lambda>(res,it,err,brk). \<not>brk) 
      (\<lambda>(res,it,err,brk). doN {
      
        if i_eof inp it then
          RETURN (res,it,True,True)
        else doN {
          c\<leftarrow>i_peek inp it;
          
          if c=char_0 then doN {
            it' \<leftarrow> i_next inp it;
            ASSERT(parsed1 inp it char_0 it');
            ASSERT(i_remsize inp it' < i_remsize inp it);
            RETURN (res,it',False,True)
          } else doN {
            ((l,err),it') \<leftarrow> parse_literal inp it;
            (err',it') \<leftarrow> parse_whitespace1 inp it';
            
            if err \<or> err' then doN {
              ASSERT(i_remsize inp it' \<le> i_remsize inp it);
              RETURN (res,it',True,True)
            } else doN {
              ASSERT(i_remsize inp it' < i_remsize inp it);
              let res = insert l res;
              RETURN (res,it',False,False)     
            }  
          }
        }
      }) 
      ({},it,False,False);

      
    ASSERT(brk);  
    RETURN ((res,err),it)  
  }"

  lemma parse_clause_correct: "parser_spec2 top top cnf_clause (parse_clause)"
    apply rule
    subgoal for inp it
      unfolding cnf_clause_def acam_insert.g_starr_conv_l
      unfolding parse_clause_def
      apply (refine_vcg 
        WHILEIT_rule[where R="measure (\<lambda>(res,it,err,brk). i_remsize inp it + (1-of_bool brk))"]
        parser_spec2D[OF parse_literal_correct]  
        parser_spec2_unitD[OF parse_whitespace1_correct]  
      )
      apply (clarsimp_all simp: parsed_remsize) 
      
      subgoal
        apply (rule gI_cons)
        apply (rule g_starl_emptyI)
        by auto
      
      subgoal by blast
      
      subgoal by (drule (2) parsed1_from_peek_nextI, simp)
      subgoal
        apply (intro exI conjI)
        apply g_parsed
      
        apply (rule g_ignore_rightI)
        apply assumption
        apply (rule g_charI)
        by simp 
    
      subgoal
        apply (intro exI conjI)
        apply g_parsed
        done
      
      subgoal
        apply (intro exI conjI)
        apply g_parsed
        
        apply (rule gI_cons)
        apply (rule g_starl_stepI)
        apply (assumption)
        apply (rule g_ignore_rightI)
        apply (assumption)
        apply (assumption)
        apply simp
        apply simp
        done
        
      done        
    done          

    
  subsection \<open>Formula\<close>
    
  (* Operation that allows clause insertion to fail (e.g. out of memory).
    Not strictly necessary here, but makes later refinement easier
  *)  
  definition "parser_insert_cl cl fml \<equiv> SPEC (\<lambda>(err,fml'). \<not>err \<longrightarrow> fml' = insert cl fml)"    

  definition "parse_cnf_loop v\<^sub>0 inp it \<equiv> doN {
    (res,it,brk,err) \<leftarrow> WHILEIT 
      (\<lambda>(res,it',brk,err). \<exists>xs.
          (err\<longrightarrow>brk) 
        \<and> parsed inp it xs it'
        \<and> (\<not>err \<and> \<not>brk \<longrightarrow> (xs,res) \<in> gM_rel ((<whitespace> \<ggreater> (cnf_ws \<ggreater> cnf_clause)) &*(\<lambda>s x. insert x s,v\<^sub>0) ))
        \<and> (\<not>err \<and> brk \<longrightarrow> (xs,res) \<in> gM_rel ((<whitespace> \<ggreater> (cnf_ws \<ggreater> cnf_clause)) &*(\<lambda>s x. insert x s,v\<^sub>0) \<lless> cnf_ws ) )
      )
      (\<lambda>(res,it,brk,err). \<not>brk \<and> \<not>i_eof inp it)
      (\<lambda>(res,it,brk,err). doN {
        
        (c,it')\<leftarrow>i_read inp it;  \<comment> \<open>Read next character. It must be whitespace.\<close>
        
        ASSERT(i_remsize inp it' \<le> i_remsize inp it);
        if c\<notin>whitespace then
          RETURN (res,it',True,True)
        else doN {
          (_,it') \<leftarrow> parse_whitespace inp it'; \<comment> \<open>Parse more whitespace\<close>
          ASSERT(i_remsize inp it' \<le> i_remsize inp it);
          
          \<comment> \<open>If we have EOF, we finish. Otherwise we parse next clause.\<close>
          ASSERT (i_valid inp it');
          if i_eof inp it' then
            RETURN (res,it',True,False)
          else doN {
            ((cl,err),it') \<leftarrow> parse_clause inp it';
          
            if err then RETURN (res,it',True,True)
            else doN {
              (err,res) \<leftarrow> parser_insert_cl cl res;
              RETURN (res,it',err,err)
            }
          }
        }
      })
      (v\<^sub>0,it,False,False);
  
    RETURN ((res,err),it)  
  }"
  
  definition "cnf_aux_loop v\<^sub>0 \<equiv> (cnf_ws1 \<ggreater> cnf_clause) &*(\<lambda>s x. insert x s,v\<^sub>0) \<lless> cnf_ws"

  lemma ws_oneI: "\<lbrakk> x\<in>whitespace; (xs,()) \<in> gM_rel cnf_ws \<rbrakk> \<Longrightarrow> (x # xs, r) \<in> gM_rel cnf_ws"
    unfolding cnf_ws_def
    thm gI_cons
    apply (rule gI_cons[of "[x]@xs"])
    apply (rule g_starr_stepI)
    apply (rule g_charI, assumption)
    apply assumption
    by auto
  
  
  lemma parse_cnf_loop_correct: "parser_spec2 top top (cnf_aux_loop v\<^sub>0) (parse_cnf_loop v\<^sub>0)"
    apply rule
    subgoal for inp it
      unfolding parse_cnf_loop_def cnf_ws1_def cnf_aux_loop_def parser_insert_cl_def
      apply (refine_vcg 
        WHILEIT_rule[where R="measure (\<lambda>(res,it,brk,err). i_remsize inp it + (1-of_bool brk))"]
        parser_spec2D[OF parse_clause_correct]  
        parser_spec2_unitD[OF parse_whitespace_correct]  
      )
      apply (clarsimp_all simp: parsed_remsize parsed1_remsize g_ignore_left_assoc) 
      
      subgoal
        apply (rule gI_cons)
        apply (rule g_starl_emptyI)
        by auto
        
      subgoal
        apply (intro exI conjI)
        by g_parsed
        
      subgoal
        apply (intro exI conjI)
        apply g_parsed
        
        apply (rule g_ignore_rightI)
        apply assumption
        
        apply (rule ws_oneI, assumption)
        by assumption
              
      subgoal
        apply (intro exI conjI)
        apply g_parsed
        done
        
      subgoal
        apply (intro exI conjI)
        apply g_parsed

        apply clarsimp
        
        apply (rule gI_cons)        
        apply (rule g_starl_stepI)
        apply assumption
        
        apply (rule g_ignore_left1I)
        apply (rule g_charI)
        apply simp
        
        apply (rule g_ignore_leftI)
        apply assumption
        apply assumption
        
        apply simp
        apply simp
        done                

      subgoal for it' brk err res xs
        apply (cases err; cases brk; simp)
        
        subgoal by blast
        
        subgoal
          apply (intro exI conjI)
          apply g_parsed
        
          apply assumption
          done
          
        subgoal
          apply (intro exI conjI)
        
          apply g_parsed

          apply (rule g_ignore_rightI[where w\<^sub>2="[]", simplified])
          apply assumption
          unfolding cnf_ws_def
          by (rule g_starr_emptyI)
      done
    done
  done        

    
  lemma cnf_ws_join: "do { cnf_ws; cnf_ws; f } = do { cnf_ws; f }"
    unfolding cnf_ws_def
    using acam_ignore.g_starr_join[unfolded g_lift2_def, of "<whitespace>"]
    by (simp flip: g_monad_laws(3))


  definition "cnf_aux_formula \<equiv> cnf_ws \<ggreater> 
      (g_return {} <|> do { v\<^sub>0 \<leftarrow> cnf_clause; cnf_aux_loop {v\<^sub>0} })"
    
    
  
  lemma cnf_aux_dimacs: "cnf_dimacs = do { cnf_comments; (g_return () <|> cnf_p_header); cnf_aux_formula }"
  proof -
    have "do {cnf_ws; cnf_cnf \<lless> cnf_ws} = cnf_aux_formula"    
      unfolding cnf_cnf_def g_ignore_left_def g_ignore_right_def g_lift2_def cnf_aux_loop_def cnf_aux_formula_def
      by (simp add: union_bind_distrib_right union_bind_distrib_left g_starr_insert_first_elem_conv cnf_ws_join)
    thus ?thesis
      unfolding cnf_dimacs_def
      by (simp add: g_option_ignore_conv g_ignore_left_def)
  qed  
  
    
  
  definition "parse_cnf_aux_formula inp it\<^sub>0 \<equiv> doN {
    (_,it) \<leftarrow> parse_whitespace inp it\<^sub>0;
    ASSERT (i_valid inp it \<and> i_remsize inp it \<le> i_remsize inp it\<^sub>0);
  
    let res = {};
    
    if i_eof inp it then
      RETURN ((res,False),it)
    else doN {
      ((cl,err),it) \<leftarrow> parse_clause inp it;
      
      if err then RETURN ((res,True),it)
      else doN {
        (err,res) \<leftarrow> parser_insert_cl cl res;
        if err then RETURN ((res,err),it)
        else parse_cnf_loop res inp it
      }
    }
  }"
  
  
  lemma parse_cnf_aux_formula_correct: "parser_spec2 top top cnf_aux_formula (parse_cnf_aux_formula)"
    apply rule
    subgoal for inp it
      unfolding parse_cnf_aux_formula_def cnf_aux_formula_def parser_insert_cl_def
      apply (refine_vcg 
        parser_spec2D[OF parse_clause_correct]  
        parser_spec2_unitD[OF parse_whitespace_correct]  
        parser_spec2D[OF parse_cnf_loop_correct]  
      )
      apply (clarsimp_all simp: parsed_remsize) 
      
      subgoal
        apply (intro exI conjI)
        apply g_parsed
        
        apply (rule g_mk_empty_rightI)
        apply (rule g_ignore_leftI)
        apply assumption
        apply (rule g_unionI_left)
        by (rule g_returnI)
        
      subgoal
        apply (intro exI conjI)
        apply g_parsed
        done  
        
      subgoal
        apply (intro exI conjI)
        apply g_parsed
        done  
          
      subgoal
        apply (intro exI conjI)
        apply g_parsed
        
        apply clarsimp
        apply (erule g_ignore_leftI)
        apply (rule g_unionI_right)
        apply (erule g_bindI)
        by assumption
      done  
    done    
        
    
  subsection \<open>Comments and Header\<close>  
  
  lemma cnf_comment_alt: "cnf_comment = cnf_aux_block char_c"
    unfolding cnf_comment_def cnf_aux_block_def cnf_aux_skip_to_def g_ignore_left_def by simp
    
  lemma cnf_p_header_alt: "cnf_p_header = cnf_aux_block char_p"
    unfolding cnf_p_header_def cnf_aux_block_def cnf_aux_skip_to_def g_ignore_left_def by simp
    
    
  definition "parse_comments inp it \<equiv> doN {
    (it,err,_)\<leftarrow>WHILEIT 
      (\<lambda>(it',err,brk). (err\<longrightarrow>brk) \<and> (\<exists>xs.
          parsed inp it xs it'
        \<and> (\<not>err \<longrightarrow> (xs,()) \<in> gM_rel ((cnf_ws <|> cnf_aux_block char_c) &* ceIgnore))    
      ))
      (\<lambda>(it,err,brk). \<not>brk \<and> \<not>i_eof inp it)
      (\<lambda>(it,err,brk). doN {
        c\<leftarrow>i_peek inp it;
        
        if c\<in>whitespace then doN {
          (err,it') \<leftarrow> parse_whitespace1 inp it;
          RETURN (it',err,err) \<comment> \<open>Error cannot happen, but this way makes termination easier to prove!\<close>
        } else if c=char_c then doN {
          (err,it') \<leftarrow> parse_skip_block char_c inp it;
          RETURN (it',err,err)
        } else RETURN (it,False,True)
      })
      (it,False,False);
      
    RETURN (err,it)
  }"  


  lemma cnf_ws_ws1I: "(w,r)\<in>gM_rel cnf_ws1 \<Longrightarrow> (w,r)\<in>gM_rel cnf_ws"
    unfolding cnf_ws_def cnf_ws1_def g_ignore_left_def
    apply (subst g_starr_unfold)
    by igr
    
    
    
  
  lemma parse_comments_correct: "parser_spec2_unit top top cnf_comments parse_comments"
    apply rule
    subgoal for inp it
      unfolding parse_comments_def
      apply (refine_vcg
        WHILEIT_rule[ where R="measure (\<lambda>(it,err,brk). i_remsize inp it + of_bool(\<not>brk))" ]
        parser_spec2_unitD[OF parse_skip_block_correct]
        parser_spec2_unitD[OF parse_whitespace1_correct]
      )

      apply (clarsimp_all simp: parsed_remsize)
  
      subgoal
        apply (rule gI_cons)
        apply (rule g_starl_emptyI)
        by auto
      
      subgoal
        apply (intro exI conjI)
        apply g_parsed
        
        apply clarsimp

        apply (rule gI_cons)
        apply (rule g_starl_stepI)
        apply assumption        
        apply (rule g_unionI_left)
        apply (erule cnf_ws_ws1I)
        by simp_all        
      
      subgoal
        apply (intro exI conjI)
        apply g_parsed
        
        apply clarsimp
        
        apply (rule gI_cons)
        apply (rule g_starl_stepI)
        apply assumption
        
        apply (erule g_unionI_right)
        apply (rule refl)
        by simp
              
      subgoal 
        apply (intro exI conjI)
        apply g_parsed
        by assumption
        
      subgoal  
        unfolding cnf_comment_alt cnf_comments_def acam_ignore.g_starr_conv_l
        by blast
      done    
    done
    
  sepref_register parse_comments
  sepref_def parse_comments_impl is "uncurry parse_comments" :: "rdmem_inp_assn\<^sup>k *\<^sub>a rdmem_it_assn\<^sup>d \<rightarrow>\<^sub>a rdm_parser_unit_assn"  
    unfolding parse_comments_def is_whitespace_alt
    by sepref
    
  
  definition "parse_maybe_p_header inp it \<equiv> doN {
    ASSERT (i_valid inp it);
    if i_eof inp it then RETURN ((True),it)
    else doN {
      c\<leftarrow>i_peek inp it;
      if c=char_p then parse_skip_block char_p inp it
      else RETURN ((False),it)
    }
  }"

  lemma parse_maybe_p_header_correct: "parser_spec2_unit top top ( g_return () <|> cnf_p_header) (parse_maybe_p_header)"
    apply rule
    subgoal for inp it
      unfolding parse_maybe_p_header_def
      apply (refine_vcg
        parser_spec2_unitD[OF parse_skip_block_correct]
      )

      apply (clarsimp_all)
      
      subgoal
        apply (intro exI conjI)
        apply g_parsed
        
        apply clarsimp
        unfolding cnf_p_header_alt
        by (erule g_unionI_right)
      
      subgoal
        by (blast intro: g_unionI_left g_returnI)  
      done  
    done

  sepref_register parse_maybe_p_header
  sepref_def parse_maybe_p_header_impl is "uncurry parse_maybe_p_header" :: "rdmem_inp_assn\<^sup>k *\<^sub>a rdmem_it_assn\<^sup>d \<rightarrow>\<^sub>a rdm_parser_unit_assn"  
    unfolding parse_maybe_p_header_def
    by sepref
    
    
      
  subsection \<open>DIMACS File\<close>
    
  definition "parse_dimacs inp it\<^sub>0 \<equiv> doN {
    ((err\<^sub>1),it) \<leftarrow> parse_comments inp it\<^sub>0;
    ((err\<^sub>2),it) \<leftarrow> parse_maybe_p_header inp it;
    ASSERT (i_remsize inp it \<le> i_remsize inp it\<^sub>0);
    ((res,err\<^sub>3),it) \<leftarrow> parse_cnf_aux_formula inp it;
    
    ASSERT (i_valid inp it);
    let err\<^sub>4 = \<not>i_eof inp it;
    
    RETURN ((res,err\<^sub>1\<or>err\<^sub>2\<or>err\<^sub>3\<or>err\<^sub>4),it)
  }"
  
  
  lemma not_implies_casesE:
    assumes "\<not>P \<longrightarrow> Q"
    obtains "P" | "\<not>P" "Q"
    using assms by blast
  
  lemma parse_dimacs_correct: "parser_spec2 top (\<lambda>inp it r err it'. \<not>err \<longrightarrow> i_eof inp it') cnf_dimacs (parse_dimacs)"
    apply rule
    subgoal for inp it
      unfolding parse_dimacs_def
      apply (refine_vcg
        parser_spec2_unitD[OF parse_comments_correct]
        parser_spec2_unitD[OF parse_maybe_p_header_correct]
        parser_spec2D[OF parse_cnf_aux_formula_correct]
      )
      
      apply (clarsimp_all simp: parsed_remsize)
      
      (* Avoiding exponential blowup, by handling each error case first *)
      
      apply (erule not_implies_casesE, intro exI conjI, g_parsed, simp) []
      apply (erule not_implies_casesE, intro exI conjI, g_parsed, simp) []
      apply (erule not_implies_casesE, intro exI conjI, g_parsed, simp) []
            
      apply (intro allI exI conjI)
      apply (g_parsed)
  
      unfolding cnf_aux_dimacs
      by (blast intro: g_bindI)
    done
    

    
end             


subsection \<open>Builder State\<close>
(*
  Building the initial formula in the clause database 
*)


(* next_id \<times> clause_builder \<times> cdb *)  
type_synonym builder_state = "nat \<times> cbld \<times> cdb"

text \<open>The invariants take an extra argument for the capacity to reserve for proof checking\<close>
definition bs_invar :: "nat \<Rightarrow> nat \<Rightarrow> builder_state \<Rightarrow> bool" where 
  "bs_invar cap\<^sub>1 cap\<^sub>2 \<equiv> \<lambda>(ncid,cbld,cdb). 
      0<ncid 
    \<and> cbld_invar cbld \<and> cap\<^sub>1+cap\<^sub>2\<le>cbld_\<alpha>_cap cbld
    \<and> dom cdb \<subseteq> {0..<ncid}
    \<and> ulit_of`(\<Union>(ran cdb)) \<subseteq> {0..cbld_\<alpha>_maxlit cbld}
    "
  
definition bs_\<alpha>F :: "builder_state \<Rightarrow> dimacs_var cnf" where "bs_\<alpha>F \<equiv> \<lambda>(ncid,cbld,cdb). ran cdb"
  
definition bs_\<alpha>C :: "builder_state \<Rightarrow> dimacs_var clause" where "bs_\<alpha>C \<equiv> \<lambda>(ncid,cbld,cdb). cbld_\<alpha>_clause cbld"

  
lemma bs_invar_antimono: "bs_invar cap\<^sub>1 cap' bs \<Longrightarrow> cap\<le>cap' \<Longrightarrow> bs_invar cap\<^sub>1 cap bs"
  unfolding bs_invar_def by auto
  
      
definition builder_init :: "nat \<Rightarrow> nat \<Rightarrow> builder_state nres" where
  "builder_init cap\<^sub>1 cap\<^sub>2 \<equiv> doN {
    let ncid = mk_cid 1;
    let cbld = cbld_new (cap\<^sub>1+cap\<^sub>2);
    let cdb = cdb_empty; 
    RETURN (ncid,cbld,cdb)
  }" 
  
   
definition builder_add_lit :: "dimacs_var literal \<Rightarrow> builder_state \<Rightarrow> builder_state nres" where
  "builder_add_lit l \<equiv> \<lambda>(ncid,cbld,cdb). do {
    ASSERT (cbld_invar cbld);
    cbld \<leftarrow> cbld_add_lit l cbld;
    RETURN (ncid,cbld,cdb)
  }"  
  


(* TODO: Move *)  
definition "dyn_check_incr_cid cid \<equiv> 
  if dest_cid cid \<le> max_size_incl - 2 then
    RETURN (mk_cid (dest_cid cid + 1),False) 
  else 
    RETURN (cid,True)
  "

lemma dyn_check_incr_cid_correct[refine_vcg]: "dyn_check_incr_cid cid \<le> SPEC (\<lambda>(cid',err). \<not>err \<longrightarrow> cid'=mk_cid (dest_cid cid + 1))"    
  unfolding dyn_check_incr_cid_def
  apply refine_vcg
  by auto        
  
sepref_register dyn_check_incr_cid  
  
sepref_def dyn_check_incr_cid_impl [llvm_inline] is "dyn_check_incr_cid" :: "cid_assn\<^sup>k \<rightarrow>\<^sub>a cid_assn \<times>\<^sub>a bool1_assn"  
  unfolding dyn_check_incr_cid_def
  apply (annot_snat_const size_T)
  by sepref
  

      
definition builder_finish_clause :: "builder_state \<Rightarrow> (bool \<times> builder_state) nres" where
  "builder_finish_clause \<equiv> \<lambda>(ncid,cbld,cdb). doN {
    (ncid',err) \<leftarrow> dyn_check_incr_cid ncid;
    if \<not>err then doN {
      (cl,cbld) \<leftarrow> cbld_finish_clause cbld;
      ASSERT (cdb ncid = None);
      cdb \<leftarrow> cdb_insert ncid cl cdb;
      RETURN (err,(ncid',cbld,cdb))
    } else doN {
      cbld \<leftarrow> cbld_abort_clause cbld;
      RETURN (err,(ncid,cbld,cdb))
    }
  }"
  

definition builder_abort_clause :: "builder_state \<Rightarrow> builder_state nres" where
  "builder_abort_clause \<equiv> \<lambda>(ncid,cbld,cdb). doN {
    cbld \<leftarrow> cbld_abort_clause cbld;
    RETURN (ncid,cbld,cdb)
  }"
  
    
lemma builder_init_correct[refine_vcg]: "builder_init cap\<^sub>1 cap\<^sub>2 \<le> SPEC (\<lambda>bs. bs_invar cap\<^sub>1 cap\<^sub>2 bs \<and> bs_\<alpha>F bs = {} \<and> bs_\<alpha>C bs = {})"
  unfolding builder_init_def
  apply refine_vcg
  unfolding bs_invar_def bs_\<alpha>F_def bs_\<alpha>C_def cdb_empty_def
  by auto

lemma builder_add_lit_correct[refine_vcg]: 
  "\<lbrakk> bs_invar cap\<^sub>1 cap\<^sub>2 bs; cap\<^sub>2\<noteq>0\<rbrakk> \<Longrightarrow>
    builder_add_lit l bs \<le> SPEC (\<lambda>bs'. 
      bs_invar cap\<^sub>1 (cap\<^sub>2-1) bs' 
    \<and> bs_\<alpha>F bs' = bs_\<alpha>F bs
    \<and> bs_\<alpha>C bs' = insert l (bs_\<alpha>C bs))"
  unfolding builder_add_lit_def
  apply refine_vcg
  unfolding bs_invar_def bs_\<alpha>F_def bs_\<alpha>C_def
  apply (auto) 
  by force
  
  

lemma builder_finish_clause_correct[refine_vcg]: "\<lbrakk> bs_invar cap\<^sub>1 cap\<^sub>2 bs; cap\<^sub>2\<noteq>0 \<rbrakk> \<Longrightarrow>
  builder_finish_clause bs \<le> SPEC (\<lambda>(err,bs'). 
      bs_invar cap\<^sub>1 (cap\<^sub>2-1) bs' 
    \<and> bs_\<alpha>C bs' = {}
    \<and> (\<not>err \<longrightarrow> 
        bs_\<alpha>F bs' = (insert (bs_\<alpha>C bs) (bs_\<alpha>F bs))
    ))"    
  unfolding builder_finish_clause_def
  apply (refine_vcg)
  unfolding bs_invar_def bs_\<alpha>F_def bs_\<alpha>C_def
  apply clarsimp_all
  apply (auto simp: image_Un cbld_\<alpha>_maxlit_bound)
  done

  
lemma builder_abort_clause_correct[refine_vcg]: "\<lbrakk> bs_invar cap\<^sub>1 cap\<^sub>2 bs \<rbrakk> \<Longrightarrow>
  builder_abort_clause bs \<le> SPEC (\<lambda>bs'. 
      bs_invar cap\<^sub>1 cap\<^sub>2 bs' 
      \<and> bs_\<alpha>F bs' = bs_\<alpha>F bs
      \<and> bs_\<alpha>C bs' = {}
    )"
  unfolding builder_abort_clause_def
  apply (refine_vcg)
  unfolding bs_invar_def bs_\<alpha>F_def bs_\<alpha>C_def
  apply clarsimp_all
  done  

(*  
lemma cdb_lits_in_maxlit: "\<lbrakk> cdb_invar cdb; l\<in>cdb_lits cdb \<rbrakk> \<Longrightarrow> var_of_lit l \<in> maxlit_vdom (cdb_maxlit cdb)"  
  unfolding cdb_invar_def cdb_lits_def maxlit_vdom_def cdb_maxlit_def
  apply (clarsimp)
  apply (rule exI[where x="ulit_of l"])
  by auto
*)
(*      
lemma builder_finish_building_correct[refine_vcg]: "\<lbrakk> bs_ob_invar cap\<^sub>1 cap\<^sub>2 bsob \<rbrakk> \<Longrightarrow>
  builder_finish_building bsob \<le> SPEC (\<lambda>csop. cs_op_invar cap\<^sub>1 csop \<and> checker_invar (bs_ob_\<alpha> bsob) (cs_op_\<alpha> csop))"  
  unfolding builder_finish_building_def
  apply refine_vcg
  unfolding cs_op_invar_def cs_op_\<alpha>_def bs_ob_invar_def  bs_ob_\<alpha>_def
  by (auto simp: cdb_lits_in_maxlit)
*)



(* Implementation: Builder *)    
  
    
definition "bs_assn \<equiv> cid_assn \<times>\<^sub>a cbld_assn \<times>\<^sub>a cdb_assn"

sepref_register 
  builder_init 
  builder_add_lit 
  builder_finish_clause 
  builder_abort_clause 
 
sepref_def builder_init_impl is "uncurry builder_init" 
  :: "[\<lambda>(cap\<^sub>1,cap\<^sub>2). cap\<^sub>1+cap\<^sub>2+1<max_size]\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> bs_assn"   
  unfolding builder_init_def bs_assn_def
  apply (annot_snat_const size_T)
  by sepref
 
sepref_def builder_add_lit_impl is "uncurry builder_add_lit" :: "ulit_assn\<^sup>k *\<^sub>a bs_assn\<^sup>d \<rightarrow>\<^sub>a bs_assn"
  unfolding builder_add_lit_def bs_assn_def
  by sepref
   
sepref_def builder_finish_clause_impl is builder_finish_clause :: "bs_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a bs_assn"
  unfolding builder_finish_clause_def bs_assn_def
  by sepref

  
sepref_def builder_abort_clause_impl is builder_abort_clause :: "bs_assn\<^sup>d \<rightarrow>\<^sub>a bs_assn"
  unfolding builder_abort_clause_def bs_assn_def
  by sepref
  
subsection \<open>Parsing with Builder State\<close>
  

definition "parse_clause2 bs inp it \<equiv> doN {
  (bs,it,err,brk) \<leftarrow> WHILET 
    (\<lambda>(bs,it,err,brk). \<not>brk) 
    (\<lambda>(bs,it,err,brk). doN {
    
      ASSERT (i_valid inp it);
      if i_eof inp it then
        RETURN (bs,it,True,True)
      else doN {
        c\<leftarrow>i_peek inp it;
        
        if c=char_0 then doN {
          it' \<leftarrow> i_next inp it;
          ASSERT(i_remsize inp it = i_remsize inp it' + 1);
          
          RETURN (bs,it',False,True)
        } else doN {
          ((l,err),it) \<leftarrow> parse_literal inp it;
          (err',it) \<leftarrow> parse_whitespace1 inp it;
          
          if err \<or> err' then
            RETURN (bs,it,True,True)
          else doN {
            bs \<leftarrow> builder_add_lit l bs;
            RETURN (bs,it,False,False)     
          }  
        }
      }
    }) 
    (bs,it,False,False);

  ASSERT (brk);  
  RETURN ((bs,err),it)  
}"

term parse_clause

definition "bs_clause_rel cap\<^sub>1 cap\<^sub>2 fml \<equiv> { (bs,cl). 
    bs_invar cap\<^sub>1 cap\<^sub>2 bs
  \<and> bs_\<alpha>F bs = fml
  \<and> bs_\<alpha>C bs = cl     
}"

abbreviation "parse_clause2_loop_state_rel cap\<^sub>1 bs\<^sub>0 inp \<equiv> { 
  ((bs,it,err,brk), (cl,it',err',brk')). 
    (bs,cl) \<in> bs_clause_rel cap\<^sub>1 (i_remsize inp it + of_bool (\<not>err \<and> brk)) (bs_\<alpha>F bs\<^sub>0)    
  \<and> (err \<longrightarrow> brk)  
  \<and> (it,it')\<in>Id  
  \<and> (err,err')\<in>Id
  \<and> (brk,brk')\<in>Id  
}"

lemma builder_add_lit_refine_aux: 
  assumes "((bs,it,err,brk), (cl,it',err',brk')) \<in> parse_clause2_loop_state_rel cap\<^sub>1 bs\<^sub>0 inp"
  assumes "(l,l')\<in>Id"
  assumes "i_remsize inp it'' < i_remsize inp it'"
  shows "builder_add_lit l bs \<le> \<Down>(bs_clause_rel cap\<^sub>1 (i_remsize inp it'') (bs_\<alpha>F bs\<^sub>0)) (RETURN (insert l' cl))"
  using assms
  unfolding bs_clause_rel_def
  apply refine_vcg
  apply (clarsimp; assumption)
  by (auto elim: bs_invar_antimono)

  
lemma parse_clause2_refine: "\<lbrakk> bs_invar cap\<^sub>1 (i_remsize inp it) bs\<^sub>0; bs_\<alpha>C bs\<^sub>0={}  \<rbrakk> \<Longrightarrow> parse_clause2 bs\<^sub>0 inp it 
  \<le> \<Down>{(((bs,err),it) , ((cl,err),it)) | bs cl err it. (bs,cl)\<in>bs_clause_rel cap\<^sub>1 (i_remsize inp it + of_bool (\<not>err)) (bs_\<alpha>F bs\<^sub>0) } 
  (parse_clause inp it)"
  unfolding parse_clause2_def parse_clause_def
  
  apply (rewrite at "let x=insert _ _ in _" let_to_bind_conv)
  
  apply (refine_rcg builder_add_lit_refine_aux)
  
  thm refine2
  
  supply [refine_dref_RELATES] = RELATESI[of "parse_clause2_loop_state_rel cap\<^sub>1 bs\<^sub>0 inp"]
  apply refine_dref_type
  
  apply (all \<open>(clarsimp;fail)?\<close>)
  unfolding bs_clause_rel_def
  apply (simp_all add: parsed1_remsize)
  
  apply (auto elim!: bs_invar_antimono; fail) 
  
  apply (intro impI conjI; elim conjE)
  apply simp
  apply simp
  apply (rule refl)+
  apply simp
  apply simp
  apply (rule refl)+
  apply simp
  apply simp
  apply (rule refl)+

  apply (auto)
  done


    
definition "os_fml_rel cap\<^sub>1 inp it \<equiv> br bs_\<alpha>F (\<lambda>bs. bs_invar cap\<^sub>1 (i_remsize inp it) bs \<and> bs_\<alpha>C bs = {})"  

lemma parse_clause2_refine'[refine]: "\<lbrakk> (os\<^sub>0,fml) \<in> os_fml_rel cap\<^sub>1 inp it; (inp,inp')\<in>Id; (it,it')\<in>Id \<rbrakk> \<Longrightarrow> 
  parse_clause2 os\<^sub>0 inp it 
  \<le> \<Down>{(((bs,err),it) , ((cl,err),it)) | bs cl err it. (bs,cl)\<in>bs_clause_rel cap\<^sub>1 (i_remsize inp it + of_bool (\<not>err)) fml }
  (parse_clause inp' it')"
  unfolding os_fml_rel_def in_br_conv
  apply clarify
  apply (rule order_trans[OF parse_clause2_refine])
  apply assumption
  by simp_all


term parser_insert_cl

lemma builder_finish_clause_refine[refine]:
  assumes "(bs,cl)\<in>bs_clause_rel cap\<^sub>1 (i_remsize inp it + 1) fml"
  shows "builder_finish_clause bs \<le> \<Down>(bool_rel \<times>\<^sub>r os_fml_rel cap\<^sub>1 inp it) (parser_insert_cl cl fml)"        
  using assms unfolding os_fml_rel_def bs_clause_rel_def parser_insert_cl_def
  apply clarify
  apply (rule order_trans[OF builder_finish_clause_correct])
  apply assumption
  apply simp
  by (auto simp: pw_le_iff refine_pw_simps in_br_conv)
  
abbreviation "parse_cnf_loop_state_rel cap\<^sub>1 inp \<equiv> {((os,it,brk,err),(fml,it',brk',err')).
    (os,fml)\<in>os_fml_rel cap\<^sub>1 inp it'
  \<and> (it,it')\<in>Id
  \<and> (brk,brk')\<in>Id
  \<and> (err,err')\<in>Id  
   }"  
  
  
definition "parse_cnf_loop_abort_clause_aux bs it \<equiv> doN {
  os \<leftarrow> builder_abort_clause bs;
  RETURN (os,it,True,True)
}"
  
lemma parse_cnf_loop_abort_clause_aux_refine[refine]:
  assumes "(bs,cl)\<in>bs_clause_rel cap\<^sub>1 (i_remsize inp it') fml" "(it,it')\<in>Id"
  shows "parse_cnf_loop_abort_clause_aux bs it \<le>\<Down>(parse_cnf_loop_state_rel cap\<^sub>1 inp) (RETURN (fml,it',True,True))"
  unfolding parse_cnf_loop_abort_clause_aux_def
  using assms
  apply refine_vcg
  unfolding bs_clause_rel_def
  apply (clarsimp; assumption)
  unfolding os_fml_rel_def
  by (auto simp: in_br_conv)
  
  
definition "parse_cnf_loop2 os inp it \<equiv> doN {
  (os,it,brk,err) \<leftarrow> WHILEIT 
    (\<lambda>(os,it,brk,err). i_valid inp it)
    (\<lambda>(os,it,brk,err). \<not>brk \<and> \<not>i_eof inp it)
    (\<lambda>(os,it,brk,err). doN {
      
      (c,it)\<leftarrow>i_read inp it; 
      
      if c\<notin>whitespace then
        RETURN (os,it,True,True)
      else doN {
        (_,it) \<leftarrow> parse_whitespace inp it;
        
        ASSERT (i_valid inp it);
        
        if i_eof inp it then
          RETURN (os,it,True,False)
        else doN {
          ((bs,err),it) \<leftarrow> parse_clause2 os inp it;
        
          if err then doN {
            parse_cnf_loop_abort_clause_aux bs it
          } else doN {
            (err,os) \<leftarrow> builder_finish_clause bs;
            RETURN (os,it,err,err)
          }
        }
      }
    })
    (os,it,False,False);

  RETURN ((os,err),it)  
}"

lemma os_fml_rel_antimono: "x\<in>os_fml_rel cap\<^sub>1 inp it \<Longrightarrow> i_remsize inp it' \<le> i_remsize inp it \<Longrightarrow> x\<in>os_fml_rel cap\<^sub>1 inp it'"   
  unfolding os_fml_rel_def
  apply (cases x)
  by (auto simp: in_br_conv elim: bs_invar_antimono)
   
   
lemma parse_cnf_loop2_refine[refine]:
  assumes "(os,fml)\<in>os_fml_rel cap\<^sub>1 inp it" "(inp,inp')\<in>Id" "(it,it')\<in>Id"
  shows "parse_cnf_loop2 os inp it 
    \<le> \<Down>{ (((os,err),it), ((fml,err),it)) | os fml err it. (os,fml)\<in>os_fml_rel cap\<^sub>1 inp it } 
    (parse_cnf_loop fml inp' it' )"
  using assms
  unfolding parse_cnf_loop2_def parse_cnf_loop_def  
  
  supply [refine_dref_RELATES] = RELATESI[of "parse_cnf_loop_state_rel cap\<^sub>1 inp"]
  apply refine_rcg
  apply refine_dref_type
  apply clarsimp_all
  
  apply (erule os_fml_rel_antimono)
  apply (simp;fail)
  
  apply (erule os_fml_rel_antimono)
  apply (simp;fail)
  
  apply (erule os_fml_rel_antimono)
  apply (simp;fail)
  
  
  apply (simp;fail)
  apply (simp;fail)
  apply (simp;fail)
  
  done     
  
      
definition "parse_cnf_aux_abort_clause_aux bs it \<equiv> doN {
  os \<leftarrow> builder_abort_clause bs;
  RETURN ((os,True),it)
}"
  

definition "parse_cnf_aux_formula2 cap\<^sub>1 inp it\<^sub>0 \<equiv> doN {
  (_,it) \<leftarrow> parse_whitespace inp it\<^sub>0;
  
  ASSERT (i_valid inp it \<and> i_remsize inp it\<le>i_remsize inp it\<^sub>0);

  ASSERT(i_remsize inp it + cap\<^sub>1 + 1 < max_size);

  os \<leftarrow> builder_init cap\<^sub>1 (i_remsize inp it);
  
  if i_eof inp it then
    RETURN ((os,False),it)
  else doN {
    ((bs,err),it) \<leftarrow> parse_clause2 os inp it;

    if err then doN {
      parse_cnf_aux_abort_clause_aux bs it
    } else doN {
      (err,os) \<leftarrow> builder_finish_clause bs;
      if err then RETURN ((os,err),it)
      else parse_cnf_loop2 os inp it
    }
  }
}"
  
lemma builder_init_refine[refine]: "builder_init cap\<^sub>1 (i_remsize inp it) \<le>\<Down>(os_fml_rel cap\<^sub>1 inp it) (RETURN {})"
  apply refine_vcg
  unfolding os_fml_rel_def in_br_conv
  by auto

term "(bs,cl) \<in> bs_clause_rel cap\<^sub>1 (i_remsize inp it) fml"  
  
lemma parse_cnf_aux_abort_clause_aux_refine[refine]: "\<lbrakk> (bs,cl) \<in> bs_clause_rel cap\<^sub>1 (i_remsize inp it) fml; (it,it')\<in>Id  \<rbrakk> \<Longrightarrow> 
  parse_cnf_aux_abort_clause_aux bs it 
  \<le>\<Down>{ (((os,err),it), ((fml,err),it)) | os fml err it. (os,fml)\<in>os_fml_rel cap\<^sub>1 inp it }
  (RETURN ((fml,True),it'))"
  unfolding parse_cnf_aux_abort_clause_aux_def bs_clause_rel_def
  apply refine_vcg
  apply (clarify; assumption)
  unfolding os_fml_rel_def in_br_conv
  by auto
  
  
  
lemma parse_cnf_aux_formula2_refine[refine]: "\<lbrakk> (inp,inp')\<in>Id; (it,it')\<in>Id; i_remsize inp it + cap\<^sub>1 + 1 < max_size \<rbrakk> 
  \<Longrightarrow> parse_cnf_aux_formula2 cap\<^sub>1 inp it 
  \<le>\<Down>{ (((os,err),it), ((fml,err),it)) | os fml err it. (os,fml)\<in>os_fml_rel cap\<^sub>1 inp it } 
  (parse_cnf_aux_formula inp' it')"  
  unfolding parse_cnf_aux_formula2_def parse_cnf_aux_formula_def
  apply refine_rcg
  apply refine_dref_type
  
  apply clarsimp_all
  
  apply assumption
  apply assumption
  apply assumption
  apply assumption
  apply assumption
  done        
  
  
definition "parse_dimacs2 cap\<^sub>1 inp it\<^sub>0 \<equiv> doN {
  ((err\<^sub>1),it) \<leftarrow> parse_comments inp it\<^sub>0;
  ((err\<^sub>2),it) \<leftarrow> parse_maybe_p_header inp it;
  ASSERT (i_remsize inp it \<le> i_remsize inp it\<^sub>0);
  
  ((res,err\<^sub>3),it) \<leftarrow> parse_cnf_aux_formula2 cap\<^sub>1 inp it;
  
  ASSERT (i_valid inp it);
  let err\<^sub>4 = \<not>i_eof inp it;
  
  RETURN ((res,err\<^sub>1\<or>err\<^sub>2\<or>err\<^sub>3\<or>err\<^sub>4),it)
}"
  
lemma parse_dimacs2_refine: "\<lbrakk>(inp,inp')\<in>Id; (it,it')\<in>Id; i_remsize inp it + cap\<^sub>1 + 1 < max_size\<rbrakk> 
  \<Longrightarrow> parse_dimacs2 cap\<^sub>1 inp it 
  \<le>\<Down>{ (((os,err),it), ((fml,err),it)) | os fml err it. (os,fml)\<in>os_fml_rel cap\<^sub>1 inp it }
  (parse_dimacs inp' it')"  
  unfolding parse_dimacs2_def parse_dimacs_def
  apply refine_rcg
  apply refine_dref_type
  apply simp_all
  apply blast    
  by blast
  
lemma parse_dimacs2_correct[refine_vcg]: "\<lbrakk> i_valid inp it; i_remsize inp it + cap\<^sub>1 + 1 < max_size \<rbrakk> \<Longrightarrow> 
    parse_dimacs2 cap\<^sub>1 inp it 
  \<le> SPEC (\<lambda>((os,err),it'). bs_invar cap\<^sub>1 0 os \<and> bs_\<alpha>C os = {}
    \<and> (\<not>err \<longrightarrow> (\<exists>xs. parsed inp it xs it' \<and> i_eof inp it' \<and> (xs,bs_\<alpha>F os) \<in> gM_rel cnf_dimacs )))"
  apply (rule order_trans[OF parse_dimacs2_refine])
  apply (rule IdI)
  apply (rule IdI)
  apply simp
  
  apply (rule order_trans)
  apply (rule monoD[OF conc_fun_mono])
  apply (rule parser_spec2D[OF parse_dimacs_correct])
  
  apply simp
  apply simp

  apply (auto simp: pw_le_iff refine_pw_simps os_fml_rel_def in_br_conv elim: bs_invar_antimono)
  done
  

definition read_dimacs_file :: "input \<Rightarrow> (builder_state \<times> nat \<times> bool) nres" 
where "read_dimacs_file inp \<equiv> doN {
  if i_size inp < max_size_incl then doN {
    let cap\<^sub>1 = max_size_incl - i_size inp - 1;
    it \<leftarrow> i_make_iterator inp;
    
    ((os,err),_) \<leftarrow> parse_dimacs2 cap\<^sub>1 inp it;
    
    RETURN (os,cap\<^sub>1,err)
  } else doN {
    os \<leftarrow> builder_init 0 0; \<comment> \<open>This is an error, we just need some builder to return\<close>
    RETURN (os,0,True)  
  }  
}"  
    

(* TODO: Move *)  
lemma parsed_to_end: "parsed inp it xs it' \<Longrightarrow> i_remsize inp it' = 0 \<Longrightarrow> xs = i_rem inp it"
  unfolding parsed_def
  by (auto simp: i_remsize_def)


lemma read_dimacs_file_correct[refine_vcg]: "read_dimacs_file inp 
  \<le> SPEC (\<lambda>(os,cap\<^sub>1,err). bs_invar cap\<^sub>1 0 os \<and> bs_\<alpha>C os = {} \<and> (\<not>err \<longrightarrow> (i_data inp,bs_\<alpha>F os) \<in> gM_rel cnf_dimacs) )"
  unfolding read_dimacs_file_def
  apply refine_vcg
  apply (auto dest: parsed_to_end)
  done

  
  
(* TODO, ctd here: refine down to LLVM, to test if we have all assumptions. 
  Then continue with formula parser *)
  
term parse_clause2

sepref_register parse_clause2
sepref_def parse_clause2_impl is "uncurry2 parse_clause2" 
  :: "bs_assn\<^sup>d *\<^sub>a rdmem_inp_assn\<^sup>k *\<^sub>a rdmem_it_assn\<^sup>d \<rightarrow>\<^sub>a rdm_parser_assn bs_assn"
  unfolding parse_clause2_def
  by sepref
    
sepref_register parse_cnf_loop2
sepref_def parse_cnf_loop2_impl is "uncurry2 parse_cnf_loop2" 
  :: "bs_assn\<^sup>d *\<^sub>a rdmem_inp_assn\<^sup>k *\<^sub>a rdmem_it_assn\<^sup>d \<rightarrow>\<^sub>a rdm_parser_assn bs_assn"
  unfolding parse_cnf_loop2_def is_whitespace_alt
  unfolding parse_cnf_loop_abort_clause_aux_def
  by sepref

sepref_register parse_cnf_aux_formula2
sepref_def parse_cnf_aux_formula2_impl is "uncurry2 parse_cnf_aux_formula2" 
  :: "size_assn\<^sup>k *\<^sub>a rdmem_inp_assn\<^sup>k *\<^sub>a rdmem_it_assn\<^sup>d \<rightarrow>\<^sub>a rdm_parser_assn bs_assn"
  unfolding parse_cnf_aux_formula2_def
  unfolding parse_cnf_aux_abort_clause_aux_def
  by sepref
    
sepref_register parse_dimacs2
sepref_def parse_dimacs2_impl is "uncurry2 parse_dimacs2" 
  :: "size_assn\<^sup>k *\<^sub>a rdmem_inp_assn\<^sup>k *\<^sub>a rdmem_it_assn\<^sup>d \<rightarrow>\<^sub>a rdm_parser_assn bs_assn"
  unfolding parse_dimacs2_def
  by sepref
    
sepref_register read_dimacs_file
sepref_def read_dimacs_file_impl is "read_dimacs_file" 
  :: "rdmem_inp_assn\<^sup>k \<rightarrow>\<^sub>a bs_assn \<times>\<^sub>a size_assn \<times>\<^sub>a bool1_assn"
  unfolding read_dimacs_file_def
  apply (annot_snat_const size_T)
  by sepref

export_llvm read_dimacs_file_impl
  
  
end
