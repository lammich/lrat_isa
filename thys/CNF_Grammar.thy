section \<open>DIMACS CNF Grammar\<close>
theory CNF_Grammar
imports Main Parser_Refine SAT_Basic DS_Unsigned_Literal
begin
  (* TODO: Move *)

  context begin interpretation lang_syntax .  
    
    lemma L_star_nempty: "L\<^sup>\<star> \<noteq> {}" using l_star_emptyI by blast

  end
  
  
  
  
  
  
  subsection \<open>Lexical Matters\<close>

  subsubsection \<open>ASCII characters\<close>
  
  (* TODO: Base that on HOL type char! Currently, char is poorly connected to 8 word. *)
  
  abbreviation (input) "char_SPACE \<equiv> 0x20::8 word"
  
  abbreviation (input) "char_TAB \<equiv> 0x09::8 word"
  abbreviation (input) "char_LF \<equiv> 0x0A::8 word"
  abbreviation (input) "char_VT \<equiv> 0x0B::8 word"
  abbreviation (input) "char_FF \<equiv> 0x0C::8 word"
  abbreviation (input) "char_CR \<equiv> 0x0D::8 word"

  abbreviation (input) "char_0 \<equiv> 0x30::8 word"
  abbreviation (input) "char_1 \<equiv> 0x31::8 word"
  abbreviation (input) "char_2 \<equiv> 0x32::8 word"
  abbreviation (input) "char_3 \<equiv> 0x33::8 word"
  abbreviation (input) "char_4 \<equiv> 0x34::8 word"
  abbreviation (input) "char_5 \<equiv> 0x35::8 word"
  abbreviation (input) "char_6 \<equiv> 0x36::8 word"
  abbreviation (input) "char_7 \<equiv> 0x37::8 word"
  abbreviation (input) "char_8 \<equiv> 0x38::8 word"
  abbreviation (input) "char_9 \<equiv> 0x39::8 word"

  abbreviation (input) "char_MINUS \<equiv> 0x2D::8 word"  
  
  abbreviation (input) "char_c \<equiv> 99::8 word"  
  abbreviation (input) "char_p \<equiv> 112::8 word"  

  
  abbreviation word_of_char :: "char \<Rightarrow> 8 word" where "word_of_char \<equiv> of_char"  
      
  lemma "word_of_char (CHR '' '') = char_SPACE" by simp 
  
  lemma "word_of_char (CHR 0x09) = char_TAB" by simp 
  lemma "word_of_char (CHR 0x0A) = char_LF"  by simp 
  lemma "word_of_char (CHR 0x0B) = char_VT"  by simp 
  lemma "word_of_char (CHR 0x0C) = char_FF"  by simp 
  lemma "word_of_char (CHR 0x0D) = char_CR"  by simp 

  lemma "word_of_char CHR ''0'' = char_0" by simp 
  lemma "word_of_char CHR ''1'' = char_1" by simp 
  lemma "word_of_char CHR ''2'' = char_2" by simp 
  lemma "word_of_char CHR ''3'' = char_3" by simp 
  lemma "word_of_char CHR ''4'' = char_4" by simp 
  lemma "word_of_char CHR ''5'' = char_5" by simp 
  lemma "word_of_char CHR ''6'' = char_6" by simp 
  lemma "word_of_char CHR ''7'' = char_7" by simp 
  lemma "word_of_char CHR ''8'' = char_8" by simp 
  lemma "word_of_char CHR ''9'' = char_9" by simp 
  
  lemma "word_of_char CHR ''-'' = char_MINUS" by simp  
  
  lemma "word_of_char CHR ''c'' = char_c" by simp  
  lemma "word_of_char CHR ''p'' = char_p" by simp  
  
  
  definition "whitespace \<equiv> {char_SPACE, char_TAB, char_LF, char_VT, char_FF, char_CR}"
  
  lemma is_whitespace_alt: "c\<in>whitespace \<longleftrightarrow> c=char_SPACE \<or> c\<ge>char_TAB \<and> c\<le>char_CR"  
    unfolding whitespace_def
    by (auto simp: word_unat_eq_iff word_le_nat_alt)

  definition "digits \<equiv> {char_0,char_1,char_2,char_3,char_4,char_5,char_6,char_7,char_8,char_9}"  
  
  definition "digits1 \<equiv> digits-{char_0}"

  lemma is_digit_alt: "c\<in>digits \<longleftrightarrow> c\<ge>char_0 \<and> c\<le>char_9"
    unfolding digits_def
    apply (clarsimp simp: word_unat_eq_iff word_le_nat_alt)
    by presburger    

  
  lemma is_digit1_alt: "c\<in>digits1 \<longleftrightarrow> char_1 \<le> c \<and> c \<le> char_9"
    unfolding digits1_def 
    apply (clarsimp simp: is_digit_alt word_unat_eq_iff word_le_nat_alt)
    by presburger    


  subsection \<open>Parsing Numbers\<close>  

  subsubsection \<open>Digits\<close>
          
  definition val_of_digit :: "8 word \<Rightarrow> nat" where "val_of_digit c = Word.unsigned (c - char_0)"
      
  lemma val_of_digit[simp]:
    "val_of_digit char_0 = (0::nat)"  
    "val_of_digit char_1 = (1::nat)" 
    "val_of_digit char_2 = (2::nat)" 
    "val_of_digit char_3 = (3::nat)" 
    "val_of_digit char_4 = (4::nat)" 
    "val_of_digit char_5 = (5::nat)" 
    "val_of_digit char_6 = (6::nat)" 
    "val_of_digit char_7 = (7::nat)" 
    "val_of_digit char_8 = (8::nat)" 
    "val_of_digit char_9 = (9::nat)" 
    unfolding val_of_digit_def
    by simp_all

  definition digit_of_val :: "nat \<Rightarrow> 8 word" where "digit_of_val n \<equiv> (of_nat n + char_0)"  
    
  lemma digit_of_val[simp]: 
    "digit_of_val 0 = char_0"
    "digit_of_val 1 = char_1"
    "digit_of_val 2 = char_2"
    "digit_of_val 3 = char_3"
    "digit_of_val 4 = char_4"
    "digit_of_val 5 = char_5"
    "digit_of_val 6 = char_6"
    "digit_of_val 7 = char_7"
    "digit_of_val 8 = char_8"
    "digit_of_val 9 = char_9"
    
    "digit_of_val (Suc 0) = char_1"
    
    unfolding digit_of_val_def 
    by simp_all
  
    
  lemma val_of_digit_eq_simps[simp]: 
    "c\<in>digits \<Longrightarrow> val_of_digit c = 0 \<longleftrightarrow> c=char_0"
    "c\<in>digits \<Longrightarrow> val_of_digit c = 1 \<longleftrightarrow> c=char_1"
    "c\<in>digits \<Longrightarrow> val_of_digit c = 2 \<longleftrightarrow> c=char_2"
    "c\<in>digits \<Longrightarrow> val_of_digit c = 3 \<longleftrightarrow> c=char_3"
    "c\<in>digits \<Longrightarrow> val_of_digit c = 4 \<longleftrightarrow> c=char_4"
    "c\<in>digits \<Longrightarrow> val_of_digit c = 5 \<longleftrightarrow> c=char_5"
    "c\<in>digits \<Longrightarrow> val_of_digit c = 6 \<longleftrightarrow> c=char_6"
    "c\<in>digits \<Longrightarrow> val_of_digit c = 7 \<longleftrightarrow> c=char_7"
    "c\<in>digits \<Longrightarrow> val_of_digit c = 8 \<longleftrightarrow> c=char_8"
    "c\<in>digits \<Longrightarrow> val_of_digit c = 9 \<longleftrightarrow> c=char_9"

    "c\<in>digits \<Longrightarrow> val_of_digit c = Suc 0 \<longleftrightarrow> c=char_1"
        
    unfolding val_of_digit_def digits_def
    by auto

    
  lemma n_less_10_cases_eq: "n<10 \<longleftrightarrow> n\<in>{0,1,2,3,4,5,6,7,8,9::nat}"
    apply simp
    by presburger  
    
  lemma digit_of_val_eq_simps[simp]: 
    "n<10 \<Longrightarrow> digit_of_val n = char_0 \<longleftrightarrow> n=0"
    "n<10 \<Longrightarrow> digit_of_val n = char_1 \<longleftrightarrow> n=1"
    "n<10 \<Longrightarrow> digit_of_val n = char_2 \<longleftrightarrow> n=2"
    "n<10 \<Longrightarrow> digit_of_val n = char_3 \<longleftrightarrow> n=3"
    "n<10 \<Longrightarrow> digit_of_val n = char_4 \<longleftrightarrow> n=4"
    "n<10 \<Longrightarrow> digit_of_val n = char_5 \<longleftrightarrow> n=5"
    "n<10 \<Longrightarrow> digit_of_val n = char_6 \<longleftrightarrow> n=6"
    "n<10 \<Longrightarrow> digit_of_val n = char_7 \<longleftrightarrow> n=7"
    "n<10 \<Longrightarrow> digit_of_val n = char_8 \<longleftrightarrow> n=8"
    "n<10 \<Longrightarrow> digit_of_val n = char_9 \<longleftrightarrow> n=9"
    unfolding digit_of_val_def n_less_10_cases_eq
    by auto


  lemma digit_of_val_inv[simp]: "c\<in>digits \<Longrightarrow> digit_of_val (val_of_digit c) = c"
    unfolding digits_def by auto      
    
  lemma val_of_digit_inv[simp]: "n<10 \<Longrightarrow> val_of_digit (digit_of_val n) = n"
    unfolding n_less_10_cases_eq
    by auto        
    
  lemma digit_of_val_is_digit[simp]: "n<10 \<Longrightarrow> digit_of_val n \<in> digits"  
    unfolding n_less_10_cases_eq digits_def
    by auto        
    
  lemma val_of_digit_lt10[simp]: "c\<in>digits \<Longrightarrow> val_of_digit c < 10"  
    unfolding digits_def
    by auto
    

  subsubsection \<open>Base-10 natural numbers\<close>      
  (* Number of string  *)
  definition "nat_of_ascii str \<equiv> fold (\<lambda>d s. 10*s+val_of_digit d) str 0"   

  (* Sanity check: alternative definition *)  
  lemma nat_of_ascii_alt: 
    "nat_of_ascii [] = 0"
    "nat_of_ascii (s@[d]) = 10*nat_of_ascii s + val_of_digit d"  
    by (simp_all add: nat_of_ascii_def)

  (* Sanity check: alternative definition *)  
  lemma nat_of_ascii_Cons:
    "nat_of_ascii (d#ds) = val_of_digit d * 10^length ds + nat_of_ascii ds"
  proof (induction ds rule: rev_induct)
    case Nil
    
    have "nat_of_ascii [d] = nat_of_ascii ([]@[d])" by simp
    also have "\<dots> = val_of_digit d"
      apply (subst nat_of_ascii_alt)
      by (simp add: nat_of_ascii_alt)
    finally show ?case by (simp add: nat_of_ascii_alt)
  next
    case (snoc x xs)
    
    have "nat_of_ascii (d # xs @ [x]) = nat_of_ascii ((d # xs) @ [x])" by simp
    also have "\<dots> = 10*(nat_of_ascii (d # xs)) + val_of_digit x" 
      apply (subst nat_of_ascii_alt)
      by simp
    also note snoc.IH
    finally show ?case by (simp add: nat_of_ascii_alt) 
  qed

  (* Sanity check: to ensure we're parsing left-to-right *)
  lemma "nat_of_ascii [char_1,char_2,char_3] = 123" by eval
  lemma "nat_of_ascii [char_1,char_2,char_3,char_0] = 1230" by eval
  lemma "nat_of_ascii [char_0] = 0" by eval
  
  
  (* String of number (Pretty print a number) *)
  fun ascii_of_nat :: "nat \<Rightarrow> 8 word list" where
    "ascii_of_nat n = (if n<10 then [digit_of_val n] 
                       else ascii_of_nat (n div 10) @ [digit_of_val (n mod 10)])"  
      
  lemmas [simp del] = ascii_of_nat.simps  

  lemma ascii_of_nat_simps:
    "n<10 \<Longrightarrow> ascii_of_nat n = [digit_of_val n]"
    "n\<ge>10 \<Longrightarrow> ascii_of_nat n = ascii_of_nat (n div 10) @ [digit_of_val (n mod 10)]"
    apply (subst ascii_of_nat.simps; simp)
    apply (subst ascii_of_nat.simps; simp)
    done      

  (* Sanity check: parsing a pretty-printed number yields same number again *)      
  lemma nat_of_ascii_inv[simp]: "nat_of_ascii (ascii_of_nat n) = n"
    apply (induction n rule: ascii_of_nat.induct)
    apply (subst ascii_of_nat.simps)
    by (auto simp: nat_of_ascii_def)
    
  lemma ascii_of_nat_eq_single_conv[simp]: "ascii_of_nat n = [c] \<longleftrightarrow> n<10 \<and> c = digit_of_val n"
    apply (subst ascii_of_nat.simps)
    apply (subst ascii_of_nat.simps)
    by auto    
    
  
  lemma ascii_of_nat_range: "ascii_of_nat n \<in> {[char_0]} \<union> { c#cs | c cs. c\<in>digits \<and> c\<noteq>char_0 \<and> set cs \<subseteq> digits }"
    apply (induction n rule: ascii_of_nat.induct)
    apply (subst ascii_of_nat.simps)
    by auto    
    
  lemma ascii_of_nat_ne[simp]: "ascii_of_nat n \<noteq> []" 
    using ascii_of_nat_range[of n] 
    by force 
    
  lemma ascii_of_nat_hd0[simp]: "hd (ascii_of_nat n) = char_0 \<longleftrightarrow> n=0"
    using ascii_of_nat_range[of n] 
    by (auto simp: ascii_of_nat_simps)
      
  context begin interpretation lang_syntax .

  (* Sanity check: Range of pretty printer as regular language "0|[1-9][0-9]*" *)
  lemma ascii_of_nat_range': "ascii_of_nat n \<in> \<lbrace>{char_0}\<rbrace> \<union> \<lbrace>digits1\<rbrace>\<cdot>\<lbrace>digits\<rbrace>\<^sup>\<star>"
  proof (induction n rule: ascii_of_nat.induct)
    case (1 n)
    
    have aux: "(\<lbrace>digits1\<rbrace> \<cdot> \<lbrace>digits\<rbrace>\<^sup>\<star>) \<cdot> \<lbrace>digits\<rbrace> \<subseteq> \<lbrace>digits1\<rbrace> \<cdot> \<lbrace>digits\<rbrace>\<^sup>\<star>"
      unfolding digits1_def
      apply (rewrite in "_ \<subseteq> \<hole>" L_star_unfold_right)
      apply igr'
      by (metis append_Cons empty_append_eq_id insert_Diff_single insert_iff)
    
    show ?case 
    proof (cases "n<10")
      case True
      then show ?thesis
        unfolding digits1_def
        apply (subst ascii_of_nat.simps; simp)
        apply (cases "n=0"; simp)
        apply (blast intro: l_char_classI)
      
        apply (rule disjI2)
        apply (rule l_concatConsI)
        apply (rule l_char_classI)
        apply simp
      
        apply (rule l_star_emptyI)
        done
        
    next
      case False
      with 1 have IH: "ascii_of_nat (n div 10) \<in> \<lbrace>digits1\<rbrace> \<cdot> \<lbrace>digits\<rbrace>\<^sup>\<star>"
        by (force simp: in_char_class)
      
      from False show ?thesis
        apply (subst ascii_of_nat.simps; simp)
        apply (rule disjI2)
      
        apply (rule set_mp[OF aux])
        apply (rule l_concatI)
        apply (rule IH)
        by (auto simp: in_char_class)
    qed    
  qed    

  lemma in_ab_star_iff: "s \<in> a \<cdot> b\<^sup>\<star> \<longleftrightarrow> (\<exists>n. s \<in> a \<cdot> L_pow b n)"
    by igr

  lemma val_of_digits1_neZ: "d\<in>digits1 \<Longrightarrow> val_of_digit d \<noteq> 0"  
    unfolding digits1_def
    using val_of_digit_eq_simps(1) by blast

  (* Sanity check: strings that do not start with zero are parsed to positive numbers *)      
  lemma nat_of_1ascii_gtZ: "s\<in>\<lbrace>digits1\<rbrace>\<cdot>\<lbrace>digits\<rbrace>\<^sup>\<star> \<Longrightarrow> nat_of_ascii s>0"  
    apply (cases s)
    by (auto
      simp: nat_of_ascii_Cons 
      dest: val_of_digits1_neZ
      elim!: l_concatE l_char_classE)
    
  (* Sanity check: printing a parsed number yields the same string. *)    
  lemma ascii_of_nat_inv:
    assumes "s \<in> \<lbrace>{char_0}\<rbrace> \<union> \<lbrace>digits1\<rbrace>\<cdot>\<lbrace>digits\<rbrace>\<^sup>\<star>" 
    shows "ascii_of_nat (nat_of_ascii s) = s"
  proof -
    have "s \<in> \<lbrace>digits1\<rbrace>\<cdot>\<lbrace>digits\<rbrace>\<^sup>\<star> \<Longrightarrow> nat_of_ascii s>0 \<and> ascii_of_nat (nat_of_ascii s) = s"  
      unfolding digits1_def
      apply (clarsimp simp: in_ab_star_iff)
      subgoal for n
        apply (induction n arbitrary: s)
        subgoal for s
          apply (simp) 
          apply (erule l_char_classE)
          apply (simp add: nat_of_ascii_def)
          using val_of_digit_eq_simps(1) by blast
      
        subgoal for n s
          apply (subst (asm) L_pow_unfold_left; simp)
          apply (erule l_concatE)
          apply (erule l_char_classE)
          apply (simp add: nat_of_ascii_alt)
          apply (subst ascii_of_nat.simps)
          by fastforce
        done    
      done
    moreover have "s \<in> \<lbrace>{char_0}\<rbrace> \<Longrightarrow> ascii_of_nat (nat_of_ascii s) = s"        
      by (simp add: in_char_class nat_of_ascii_def)
    ultimately show ?thesis using assms by blast
  qed      


  subsubsection \<open>Parsing Variables\<close>
  definition "var_of_ascii \<equiv> var_of_nat o nat_of_ascii"
  definition "ascii_of_var \<equiv> ascii_of_nat o nat_of_var"
  
  lemma var_of_ascii_inv[simp]: "var_of_ascii (ascii_of_var v) = v"
    unfolding var_of_ascii_def ascii_of_var_def
    by simp
  
  lemma ascii_of_var_inv: "s \<in> \<lbrace>digits1\<rbrace>\<cdot>\<lbrace>digits\<rbrace>\<^sup>\<star> \<Longrightarrow> ascii_of_var (var_of_ascii s) = s"
    unfolding var_of_ascii_def ascii_of_var_def
    by (auto simp: ascii_of_nat_inv nat_of_1ascii_gtZ)
  
    
  
  end  

subsection \<open>DIMACS CNF Grammar\<close>
(*
  Grammar for the simplified DIMACS CNF format that is used in SAT competitions:
  
  comments can only be at start of the file.

  we generalize this format slightly by making the header optional, and ignoring its contents.
*)
  
  context begin
    interpretation lang_syntax .  
  
  definition "cnf_ws \<equiv> <whitespace> *&ceIgnore"
  definition "cnf_ws1 \<equiv> <whitespace> \<ggreater> cnf_ws"
  
    
  definition "cnf_variable = (<digits1> <#> (<digits> *&ceCons )) <&> (var_of_ascii)"
  
  definition "cnf_literal = (<{char_MINUS}> \<ggreater> cnf_variable) <&> Neg <|> cnf_variable <&> Pos"
      
  definition "cnf_clause = (cnf_literal \<lless> cnf_ws1) *& ceInsert \<lless> <{char_0}>"

  definition "cnf_cnf = 
      g_return {} 
    <|> (g_lift2 insert cnf_clause ((cnf_ws1 \<ggreater> cnf_clause) *&ceInsert))"
  
    
  definition "cnf_comment = do {<{char_c}>; < -{char_LF} > *&ceIgnore; <{char_LF}>; g_return () }"
  definition "cnf_p_header = do {<{char_p}>; < -{char_LF} > *&ceIgnore; <{char_LF}>; g_return () }"
  
  definition "cnf_comments = do { (cnf_ws <|> cnf_comment)*&ceIgnore }"
    
  definition "cnf_dimacs = do { cnf_comments; cnf_p_header?; cnf_ws; cnf_cnf \<lless> cnf_ws }"
  
  end
  

(* For paper: *)

(*
  The syntax and grammar rules presented in the paper (proved to be the same grammar as what we define above)
*)
experiment
begin
        
context begin interpretation lang_syntax .    
    
  no_notation L_star ("_\<^sup>\<star>" [101] 100)

  abbreviation g_star ("_\<^sup>\<star>" [101] 100) where "g_star g \<equiv> g *&ceCons"
  
  (* TODO: Move *)  
  lemma g_starr_bind_ignore_conv: "NO_MATCH ceIgnore fi \<Longrightarrow> do { (g *&fi); m } = do { g *&ceIgnore; m }"
  proof -
    have "g_lang (g_powr g fi n) = g_lang (g_powr g ceIgnore n)" for n
      by (simp add: g_lang_powr)
    thus ?thesis
      by igr
  qed    
      
  lemma set_as_fold: "set xs = fold insert xs {}"
    using union_set_fold by force
      
  lemma "a\<lless>b = g_lift2 (\<lambda>a _. a) a b" unfolding g_ignore_right_def by igr

  lemma starl_insert_is_cons_set: "a *& ceInsert = (a *& ceCons ) <&> set"
    apply (simp add: set_as_fold[abs_def])
    apply (subst g_starr_fold_conv)
    by (simp add: acam_insert.g_starr_conv_l)
    
    
  lemma 
    "cnf_variable = do { x\<leftarrow><digits1>; xs\<leftarrow>(<digits>\<^sup>\<star>); g_return (var_of_ascii (x#xs))}"
    "cnf_literal = do {<{char_MINUS}>; cnf_variable <&> Neg} <|> cnf_variable <&> Pos"
    "cnf_clause = (cnf_literal \<lless> cnf_ws1)\<^sup>\<star> <&> set \<lless> <{char_0}>"
    unfolding cnf_variable_def cnf_literal_def cnf_clause_def cnf_cnf_def
      g_ignore_left_def starl_insert_is_cons_set
    apply igr
    apply igr
    apply igr
    done
    
  lemma "cnf_cnf = 
        g_return {} 
      <|> (do { c\<leftarrow>cnf_clause; cs \<leftarrow> (do {cnf_ws1; cnf_clause})\<^sup>\<star>; g_return ({c} \<union> set cs) }) "
    unfolding cnf_cnf_def g_ignore_left_def starl_insert_is_cons_set
    by igr
    
  lemma     
    "cnf_comment = do {<{char_c}>; < -{char_LF} >\<^sup>\<star>; <{char_LF}>; g_return () }"
    "cnf_p_header = do {<{char_p}>; < -{char_LF} >\<^sup>\<star>; <{char_LF}>; g_return () }"
    "cnf_comments = do { (cnf_ws <|> cnf_comment)\<^sup>\<star>; g_return () }"
    "cnf_dimacs = do { cnf_comments; cnf_p_header?; cnf_ws; cnf_cnf \<lless> cnf_ws }"
    unfolding cnf_comment_def cnf_p_header_def cnf_comments_def cnf_dimacs_def
    by (simp_all add: g_starr_bind_ignore_conv)
    
    
end

end

subsection \<open>Language of the DIMACS CNF Grammar\<close>  
(*
  We derive a succinct presentation of the language of our grammar
*)

context begin interpretation lang_syntax .    
    
  named_theorems cnf_lang_thms    
    
  lemma gl_cnf_variable: "g_lang (cnf_variable) = \<lbrace>digits1\<rbrace> \<cdot> \<lbrace>digits\<rbrace>\<^sup>\<star>"
    unfolding cnf_variable_def
    apply (subst g_lang_simps | intro gl_indep_intros)+
    by simp
      
  concrete_definition l_cnf_variable [cnf_lang_thms] is [simp] gl_cnf_variable

  
  lemma gl_cnf_ws: "g_lang (cnf_ws) = \<lbrace>whitespace\<rbrace>\<^sup>\<star>"
    unfolding cnf_ws_def   
    apply (subst g_lang_simps | intro gl_indep_intros)+
    by simp
    
  concrete_definition l_cnf_ws [cnf_lang_thms] is [simp] gl_cnf_ws
    
  lemma gl_cnf_ws1: "g_lang (cnf_ws1) = \<lbrace>whitespace\<rbrace>\<cdot>\<lbrace>whitespace\<rbrace>\<^sup>\<star>"
    unfolding cnf_ws_def cnf_ws1_def   
    apply (subst g_lang_simps | intro gl_indep_intros)+
    by simp
  
  concrete_definition l_cnf_ws1 [cnf_lang_thms] is [simp] gl_cnf_ws1

  lemma gl_cnf_literal: "g_lang (cnf_literal) = \<lbrace>{char_MINUS}\<rbrace>\<^sup>? \<cdot> l_cnf_variable"
    unfolding cnf_literal_def
    apply (subst g_lang_simps | intro gl_indep_intros)+
    by (simp add: l_join_same_tail)
    
  concrete_definition l_cnf_literal [cnf_lang_thms] is [simp] gl_cnf_literal
        
  lemma gl_cnf_clause: "g_lang (cnf_clause) = (l_cnf_literal \<cdot> l_cnf_ws1)\<^sup>\<star> \<cdot> \<lbrace>{char_0}\<rbrace>"
    unfolding cnf_clause_def
    apply (subst g_lang_simps | intro gl_indep_intros)+
    by (simp add: l_join_same_tail)
    
  concrete_definition l_cnf_clause [cnf_lang_thms] is [simp] gl_cnf_clause

      
  lemma gl_cnf_cnf: "g_lang (cnf_cnf) = (l_cnf_clause \<cdot> (l_cnf_ws1 \<cdot> l_cnf_clause)\<^sup>\<star>)\<^sup>?"
    unfolding cnf_cnf_def   
    apply (subst g_lang_simps | intro gl_indep_intros)+
    by (simp add: L_opt_def)
        
  concrete_definition l_cnf_cnf [cnf_lang_thms] is [simp] gl_cnf_cnf
  
  lemma gl_cnf_comment: "g_lang cnf_comment = \<lbrace>{char_c}\<rbrace> \<cdot> \<lbrace>-{char_LF}\<rbrace>\<^sup>\<star> \<cdot> \<lbrace>{char_LF}\<rbrace>"
    unfolding cnf_comment_def
    apply (subst g_lang_simps | intro gl_indep_intros)+
    by simp

  concrete_definition l_cnf_comment [cnf_lang_thms] is [simp] gl_cnf_comment
      
  lemma gl_cnf_comments: "g_lang cnf_comments = (l_cnf_ws \<union> l_cnf_comment)\<^sup>\<star>"
    unfolding cnf_comments_def
    apply (subst g_lang_simps | intro gl_indep_intros)+
    by simp
        
  concrete_definition l_cnf_comments [cnf_lang_thms] is [simp] gl_cnf_comments
    
  lemma gl_cnf_p_header: "g_lang cnf_p_header = \<lbrace>{char_p}\<rbrace> \<cdot> \<lbrace>-{char_LF}\<rbrace>\<^sup>\<star> \<cdot> \<lbrace>{char_LF}\<rbrace>"
    unfolding cnf_p_header_def
    apply (subst g_lang_simps | intro gl_indep_intros)+
    by simp
  
  concrete_definition l_cnf_p_header [cnf_lang_thms] is [simp] gl_cnf_p_header
    
  lemma gl_cnf_dimacs: "g_lang cnf_dimacs = l_cnf_comments \<cdot> l_cnf_p_header\<^sup>? \<cdot> l_cnf_ws \<cdot> l_cnf_cnf \<cdot> l_cnf_ws"  
    unfolding cnf_dimacs_def
    apply (subst g_lang_simps | intro gl_indep_intros)+
    by simp
    
  concrete_definition l_cnf_dimacs [cnf_lang_thms] is [simp] gl_cnf_dimacs

  text \<open>
    Sanity check: the regular language induced by our grammar monad:
  \<close>     

  theorem dimacs_reg_language:
    "g_lang cnf_dimacs = l_cnf_dimacs"

    "l_cnf_dimacs \<equiv> l_cnf_comments \<cdot> l_cnf_p_header\<^sup>? \<cdot> l_cnf_ws \<cdot> l_cnf_cnf \<cdot> l_cnf_ws"    
    
    "l_cnf_ws \<equiv> \<lbrace>whitespace\<rbrace>\<^sup>\<star>"
    "l_cnf_ws1 \<equiv> \<lbrace>whitespace\<rbrace> \<cdot> \<lbrace>whitespace\<rbrace>\<^sup>\<star>"
    
    "l_cnf_comments \<equiv> (l_cnf_ws \<union> l_cnf_comment)\<^sup>\<star>"
    "l_cnf_comment \<equiv> \<lbrace>{char_c}\<rbrace> \<cdot> \<lbrace>- {char_LF}\<rbrace>\<^sup>\<star> \<cdot> \<lbrace>{char_LF}\<rbrace>"
    
    "l_cnf_p_header \<equiv> \<lbrace>{char_p}\<rbrace> \<cdot> \<lbrace>- {char_LF}\<rbrace>\<^sup>\<star> \<cdot> \<lbrace>{char_LF}\<rbrace>"
    
    "l_cnf_cnf \<equiv> (l_cnf_clause \<cdot> (l_cnf_ws1 \<cdot> l_cnf_clause)\<^sup>\<star>)\<^sup>?"
      
    "l_cnf_clause \<equiv> (l_cnf_literal \<cdot> l_cnf_ws1)\<^sup>\<star> \<cdot> \<lbrace>{char_0}\<rbrace>"

    "l_cnf_literal \<equiv> \<lbrace>{char_MINUS}\<rbrace>\<^sup>? \<cdot> l_cnf_variable"
    "l_cnf_variable \<equiv> \<lbrace>digits1\<rbrace> \<cdot> \<lbrace>digits\<rbrace>\<^sup>\<star>"
    by (auto simp: cnf_lang_thms)    
    

end




  (* TODO: Clean up whole unambiguous reasoning! 
    Currently, it has some redundant parts, and contains just enough lemmas to show unambiguous cnf_dimacs!
  *)  
  
  
  
  
  
subsection \<open>Unmabiguity of CNF Grammar\<close>  
context begin interpretation lang_syntax .    
  
  lemma g_uniq_variable[g_uniq_intros]:
    assumes LH: "lh1 C \<inter> digits = {}"
    shows "g_uniq cnf_variable C"
    unfolding cnf_variable_def
    
    apply (intro g_uniq_intros)
    using LH apply (simp add: glang_char lh1_def)
    apply igr_force 
    done
    
    
  lemma lh1_variable[simp]: "lh1 l_cnf_variable = digits1"  
    unfolding l_cnf_variable_def
    by simp
    
  lemma has_eps_variable[simp]: "\<not>has_eps l_cnf_variable"  
    unfolding l_cnf_variable_def
    by simp
       
  lemma g_uniq_literal[g_uniq_intros]:
    assumes LH: "lh1 C \<inter> digits = {}"
    shows "g_uniq cnf_literal C"
    unfolding cnf_literal_def g_ignore_left_lift2
    apply (intro g_uniq_intros g_uniq_mk_unitI LH)
    
    apply (rule lh1_disjI)
    apply (simp add: g_lang_simps)
    by (auto simp add: g_lang_simps is_digit1_alt)

  lemma is_el_ws1[simp]: "\<not> is_el l_cnf_ws1"
    unfolding l_cnf_ws1_def
    by (simp add: whitespace_def)
  
  lemma digits1_ne[simp]: "digits1 \<noteq> {}"  
    by (simp add: digits1_def digits_def)
    
  lemma is_el_variable[simp]: "\<not>is_el l_cnf_variable"  
    unfolding l_cnf_variable_def
    by simp
    
  
  lemma lh1_literal[simp]: "lh1 l_cnf_literal = insert char_MINUS digits1"  
    unfolding l_cnf_literal_def
    by simp

  lemma lh1_ws1[simp]: "lh1 l_cnf_ws1 = whitespace"  
    unfolding l_cnf_ws1_def
    by simp
    
  lemma has_eps_literal[simp]: "\<not> has_eps (l_cnf_literal)"  
    unfolding l_cnf_literal_def
    by (simp add: g_lang_simps l_cnf_variable_def)
    
  lemma has_eps_ws1[simp]: "\<not> has_eps l_cnf_ws1"  
    unfolding l_cnf_ws1_def
    by simp
    
    
  lemma ws_dj_digits: "whitespace \<inter> digits = {}" 
    by (auto simp: is_whitespace_alt digits_def)  

  lemma ws_dj_digits1: "whitespace \<inter> digits1 = {}"
    by (auto simp: whitespace_def is_digit1_alt)
    
  lemmas ws_digits_dj_simps[simp] = disjointD[OF ws_dj_digits] disjointD[OF ws_dj_digits1]
    
  lemma g_uniq_ws[g_uniq_intros]:
    assumes LH: "lh1 C \<inter> whitespace = {}"
    shows "g_uniq cnf_ws C"  
    unfolding cnf_ws_def
    apply (intro g_uniq_intros)
    
    apply (rule lh1_disjI)
    apply (simp add: g_lang_simps)
    using LH
    apply (auto simp add: g_lang_simps)
    done
        
  lemma g_uniq_ws1[g_uniq_intros]:
    assumes LH: "lh1 C \<inter> whitespace = {}"
    shows "g_uniq cnf_ws1 C"  
    unfolding cnf_ws1_def g_ignore_left_lift2
    by (intro g_uniq_intros g_uniq_mk_unitI LH)
    
    
  lemma g_uniq_clause[g_uniq_intros]:
    shows "g_uniq cnf_clause C"
    apply (cases "is_el C")
    apply simp
    
    unfolding cnf_clause_def g_ignore_right_lift2
    apply (intro g_uniq_intros g_uniq_mk_unitI)

    apply (rule lh1_disjI)
    apply (simp add: g_lang_simps)
    apply (simp add: g_lang_simps is_digit1_alt)
    
    apply (auto simp add: g_lang_simps) []
    
    apply (simp add: g_lang_simps is_whitespace_alt)
    apply auto []
    done
    

  lemma lh1_ws[simp]: "lh1 l_cnf_ws = whitespace"  
    unfolding l_cnf_ws_def
    by simp
        
  lemma is_el_ws[simp]: "\<not>is_el l_cnf_ws"
    unfolding l_cnf_ws_def
    by simp
    
    
  lemma lh1_clause[simp]: "lh1 l_cnf_clause = (insert char_MINUS digits)"  
    unfolding l_cnf_clause_def
    apply (simp add: digits1_def) by (auto simp: is_digit_alt)
      
  lemma has_eps_clause[simp]: "\<not>has_eps l_cnf_clause"  
    unfolding l_cnf_clause_def
    by simp
    
  lemma l_charset_must_clause[simp]: "l_charset_must l_cnf_clause = {char_0}"
    unfolding l_cnf_clause_def
    by simp
  
  lemma l_charset_literal[simp]: "l_charset l_cnf_literal = insert char_MINUS digits"  
    unfolding l_cnf_literal_def l_cnf_variable_def digits1_def digits_def
    by auto
    
  lemma l_charset_whitespace1[simp]: "l_charset (l_cnf_ws1) = whitespace"  
    unfolding l_cnf_ws1_def whitespace_def
    by simp
    
  lemma l_charset_whitespace[simp]: "l_charset (l_cnf_ws) = whitespace"  
    unfolding l_cnf_ws_def whitespace_def
    by simp
    
    
  
  lemma g_uniq_cnf[g_uniq_intros]:
    shows "g_uniq cnf_cnf l_cnf_ws"
    unfolding cnf_cnf_def g_ignore_left_lift2

    apply (intro g_uniq_intros g_uniq_mk_unitI)
    apply (simp add: g_lang_simps)
    subgoal
      apply (rule L_disj_charset_must_mayI)
      apply simp
      by (auto simp: is_whitespace_alt)

    apply (auto simp add: g_lang_simps is_whitespace_alt) []

    apply (simp add: g_lang_simps)
    apply (rule lh1_disjI)
    apply (simp)
    apply (auto simp add: is_whitespace_alt) []
    done
            

  definition "to_unit_g L \<equiv> GR (L \<times> {()})"  (* TODO: Probably superseeds mk_unit! *)
  
  lemma igr_to_unit_g[igr_simps]: "(w,r)\<in>gM_rel (to_unit_g L) \<longleftrightarrow> w\<in>L"
    unfolding to_unit_g_def by igr
    
  lemma to_unit_g1: "NO_MATCH (to_unit_g XXX) a \<Longrightarrow> do { a; b } = do { to_unit_g (g_lang a); b  }"
    by igr

  lemma to_unit_g1': "NO_MATCH (to_unit_g XXX) a \<Longrightarrow> a = to_unit_g (g_lang a)"
    by igr

  lemma to_unit_g2: "do { to_unit_g L\<^sub>1; to_unit_g L\<^sub>2; a } = do { to_unit_g (L\<^sub>1\<cdot>L\<^sub>2); a }"  
    by igr_fastforce 
            
  lemma to_unit_g2': "do { to_unit_g L\<^sub>1; to_unit_g L\<^sub>2 } = to_unit_g (L\<^sub>1\<cdot>L\<^sub>2)"  
    by igr_fastforce 
    
  lemmas to_unit_g = to_unit_g1 to_unit_g1' to_unit_g2 to_unit_g2'
    
  
  lemma g_uniq_unit_simp[simp]: "g_uniq (to_unit_g L) C = L_uniq L C"
    unfolding g_uniq_def L_uniq_def
    by igr'

  lemma g_uniq_unitI[g_uniq_intros]: "L_uniq L C \<Longrightarrow> g_uniq (to_unit_g L) C"
    by simp
      
  lemma L_uniq_concat[g_uniq_intros]:
    assumes "L_uniq L\<^sub>1 (L\<^sub>2\<cdot>C)"
    assumes "L_uniq L\<^sub>2 C"
    shows "L_uniq (L\<^sub>1\<cdot>L\<^sub>2) C"
    using assms
    unfolding L_uniq_def
    by (smt (verit, best) append.assoc igr_L_concat same_append_eq)
    
    
  find_theorems cnf_cnf  
    
  definition "cnf_cnf1_aux \<equiv> g_lift2 insert cnf_clause ((cnf_ws1 \<ggreater> cnf_clause) *& ceInsert)"
  
  lemma cnf_eq_cnf1_aux: "cnf_cnf = g_return {} <|> cnf_cnf1_aux"  
    unfolding cnf_cnf_def cnf_cnf1_aux_def ..
    
   
  lemma g_lift2_distrib_union1: "g_lift2 f (a<|>b) c = g_lift2 f a c <|> g_lift2 f b c"  
    by igr
     
  find_theorems l_cnf_comments
  
  definition "l_cnf_aux_prelude \<equiv> l_cnf_comments \<cdot> l_cnf_p_header\<^sup>? \<cdot> l_cnf_ws"
  
  definition "L_sng x \<equiv> {x}"
  lemma L_sng_igr[igr_simps]: "x\<in>L_sng w \<longleftrightarrow> x=w" unfolding L_sng_def by auto
  
  lemma L_sng_Nil1[simp]: 
    "L \<cdot> L_sng [] = L"
    "L_sng [] \<cdot> L = L"
    by igr'+
  
  lemma L_conc_insert_distrib1: "insert x a \<cdot> b = L_sng x\<cdot>b \<union> a\<cdot>b" by igr_fastforce 
  lemma L_conc_insert_distrib2: "a \<cdot> insert x b = a\<cdot>L_sng x \<union> a\<cdot>b" by igr_fastforce 
  
  lemma L_union_distrib1: "(a\<union>b)\<cdot>c = (a\<cdot>c) \<union> (b\<cdot>c)" by igr_fastforce
  lemma L_union_distrib2: "a\<cdot>(b\<union>c) = (a\<cdot>b) \<union> (a\<cdot>c)" by igr_fastforce
  
  lemma un_star_conc_add: "[]\<in>a \<Longrightarrow> (a \<union> b)\<^sup>\<star> \<cdot> a = (a \<union> b)\<^sup>\<star>"
    apply safe
    
    apply (igr_simp; clarsimp)
    subgoal for w\<^sub>1 n w\<^sub>2
      apply (rule exI[where x="Suc n"])
      apply (simp only: L_pow_unfold_left)
      by igr
    subgoal by igr
    done

    
    

  lemma L_star_conc[simp]: "L\<^sup>\<star>\<cdot>L\<^sup>\<star> = L\<^sup>\<star>"  
    supply [intro] = exI[where x="_+_"] exI[where x="0"]
    by igr_fastforce
    
  lemma L_star_conc2[simp]: "A\<cdot>L\<^sup>\<star>\<cdot>L\<^sup>\<star> = A\<cdot>L\<^sup>\<star>"
    by (simp flip: L_concat_simps(5))
    
  lemma [simp]: "l_cnf_ws \<cdot> l_cnf_ws = l_cnf_ws"  
    unfolding l_cnf_ws_def by simp
    
      
    
  lemma L_star_subsetI:
    assumes "\<And>n. L_pow a n \<subseteq> b"
    shows "a\<^sup>\<star> \<subseteq> b"  
    using assms by igr_force 
    
  lemma un_star_to_seq_star:
    assumes "[]\<in>a" "a\<cdot>a=a"  
    shows "(a\<union>b)\<^sup>\<star> = a\<cdot>(b\<cdot>a)\<^sup>\<star>"
  proof (intro equalityI L_star_subsetI)
    fix n
    show "L_pow (a \<union> b) n \<subseteq> a \<cdot> (b \<cdot> a)\<^sup>\<star>"
    proof (induction n)
      case 0
      then show ?case using \<open>[]\<in>a\<close> l_star_emptyI by igr'
    next
      case (Suc n)
      
      note a_expand = \<open>a\<cdot>a=a\<close>[symmetric]
      
      from \<open>[]\<in>a\<close> have a_ignore: "b\<subseteq>a\<cdot>c" if "b\<subseteq>c" for b c
        using that
        by igr_force  
      
      
      show ?case
        apply (simp add: L_union_distrib1)
        apply rule
        
        apply (rewrite in "_ \<subseteq> \<hole>" a_expand)
        apply (simp flip: L_concat_simps(5))
        apply (rule L_concat_mono[OF order_refl])
        apply (rule order_trans[OF Suc.IH order_refl])
        
        apply (rewrite in "_ \<subseteq> \<hole>" L_star_unfold)
        apply (rule a_ignore)
        using L_concat_mono[OF order_refl Suc.IH] 
        by auto
        
    qed
  next  
    have "(b \<cdot> a)\<^sup>\<star> \<subseteq> (a \<union> b)\<^sup>\<star>" 
    proof (rule L_star_subsetI)  
      fix n
      show "L_pow (b \<cdot> a) n \<subseteq> (a \<union> b)\<^sup>\<star>"
        apply (induction n)
        apply simp
        apply (rewrite in "_ \<subseteq> \<hole>" L_star_unfold)
        apply (rewrite in "_ \<subseteq> \<hole>" L_star_unfold)
        apply (simp add: L_union_distrib1 L_union_distrib2)
        by (metis L_concat_mono L_concat_simps(5) dual_order.refl le_supI1 le_supI2 subset_insertI2)
    qed
    then show "a \<cdot> (b \<cdot> a)\<^sup>\<star> \<subseteq> (a \<union> b)\<^sup>\<star>"
      apply (rewrite in "_ \<subseteq> \<hole>" L_star_unfold)
      by (meson L_concat_mono sup.cobounded1 sup.coboundedI2)
  qed    
    
  lemma l_cnf_ws_emp[simp]: "[]\<in>l_cnf_ws" unfolding l_cnf_ws_def by (simp)
    
  lemma l_cnf_aux_prelude1: "l_cnf_aux_prelude = l_cnf_comments \<cdot> (l_cnf_p_header \<cdot> l_cnf_ws)\<^sup>?"
    unfolding L_opt_def l_cnf_comments_def l_cnf_aux_prelude_def
    by (simp add: L_conc_insert_distrib1 L_conc_insert_distrib2 L_union_distrib1 L_union_distrib2 un_star_conc_add)
    
  lemma l_cnf_comments_alt: "l_cnf_comments = l_cnf_ws \<cdot> (l_cnf_comment \<cdot> l_cnf_ws)\<^sup>\<star>"  
    unfolding l_cnf_comments_def
    by (simp add: un_star_to_seq_star)
    
  lemma [simp]: "l_cnf_aux_prelude \<cdot> l_cnf_ws = l_cnf_aux_prelude"  
    unfolding l_cnf_aux_prelude1 l_cnf_comments_def L_opt_def l_cnf_ws_def
    by (simp add: L_conc_insert_distrib1 L_conc_insert_distrib2 L_union_distrib1 L_union_distrib2 un_star_conc_add)
    
    
  lemma g_lang_unit_g[simp]: "g_lang (to_unit_g L) = L"  
    unfolding g_lang_def to_unit_g_def
    by auto
    
  lemma to_unit_g_Nil: "to_unit_g {[]} = g_return ()"  
    unfolding to_unit_g_def
    by igr
    
  lemma to_unit_g_powr[simp]: "g_powr (to_unit_g a) fi n = to_unit_g (L_pow a n)"  
    apply (induction n)
    apply (simp add: to_unit_g_Nil)
    apply (simp add: g_lift2_def to_unit_g)
    done
    
    
  lemma to_unit_g_starr: "to_unit_g a *& fi = to_unit_g (a\<^sup>\<star>)"
    by igr'  
    
  lemma L_uniq_starI[g_uniq_intros]: "\<lbrakk>a \<cdot> a\<^sup>\<star> \<cdot> C \<inter> C = {}; L_uniq a (a\<^sup>\<star> \<cdot> C)\<rbrakk> \<Longrightarrow> L_uniq (a\<^sup>\<star>) C"
    using g_uniq_starrI[of "to_unit_g a" _ ceIgnore]
    by (simp add: to_unit_g_starr)
  
  lemma L_uniq_char[g_uniq_intros]: "L_uniq \<lbrace>cs\<rbrace> C"  
    unfolding L_uniq_def by igr'
    
  lemma L_uniq_ws[g_uniq_intros]:
    assumes LH: "whitespace \<inter> lh1 C = {}"
    shows "L_uniq l_cnf_ws C"  
    unfolding l_cnf_ws_def
    apply (intro g_uniq_intros)
    apply (rule lh1_disjI)
    apply simp
    apply (simp add: LH)
    done
    
  lemma has_eps_comment[simp]: "\<not>has_eps l_cnf_comment"  
    unfolding l_cnf_comment_def
    by auto

  lemma has_eps_p_header[simp]: "\<not>has_eps l_cnf_p_header"  
    unfolding l_cnf_p_header_def
    by auto
    
  lemma lh1_comment[simp]: "lh1 l_cnf_comment = {char_c}"  
    unfolding l_cnf_comment_def by auto

  lemma lh1_p_header[simp]: "lh1 l_cnf_p_header = {char_p}"  
    unfolding l_cnf_p_header_def by auto
    
  lemma L_uniq_comment[g_uniq_intros]: "L_uniq l_cnf_comment C"  
    unfolding l_cnf_comment_def
    apply (intro g_uniq_intros)
    apply (rule lh1_disjI)
    apply simp
    apply simp
    done
    
  lemma L_uniq_p_header[g_uniq_intros]: "L_uniq l_cnf_p_header C"  
    unfolding l_cnf_p_header_def
    apply (intro g_uniq_intros)
    apply (rule lh1_disjI)
    apply simp
    apply simp
    done
  
  lemma to_unit_g_union[simp]: "to_unit_g a <|> to_unit_g b = to_unit_g (a\<union>b)"
    unfolding to_unit_g_def
    by igr
  
  lemma L_uniq_union[g_uniq_intros]: "\<lbrakk>L_uniq a C; L_uniq b C; a \<cdot> C \<inter> b \<cdot> C = {}\<rbrakk> \<Longrightarrow> L_uniq (a \<union> b) C"  
    using g_uniq_unionI[of "to_unit_g a" C "to_unit_g b"] by simp
    
  lemma L_opt_sng_alt: "L\<^sup>? = L_sng [] \<union> L"  
    unfolding L_sng_def L_opt_def
    by igr
    
  lemma L_uniq_sng[g_uniq_intros]: "L_uniq (L_sng []) C"  
    unfolding L_sng_def L_uniq_def by igr
    
  lemma L_uniq_opt[g_uniq_intros]: "\<lbrakk>L_uniq L C; C \<inter> L \<cdot> C = {}\<rbrakk> \<Longrightarrow> L_uniq (L\<^sup>?) C"  
    unfolding L_opt_sng_alt
    apply (intro g_uniq_intros)[]
    apply simp
    apply simp
    done
    

  lemma L_uniq_aux_prelude[g_uniq_intros]: "\<lbrakk>\<not>is_el C; whitespace \<inter> lh1 C = {}; char_p \<notin> lh1 C; char_c \<notin> lh1 C\<rbrakk> 
    \<Longrightarrow> L_uniq l_cnf_aux_prelude C"  
    unfolding l_cnf_aux_prelude1 l_cnf_comments_alt
    apply (intro g_uniq_intros)

    apply (simp_all add: is_whitespace_alt)
    
    apply (rule lh1_disjI)
    apply simp
    apply simp

    apply (rule lh1_disjI)
    apply simp
    apply simp
    done
    
  lemma cnf_dimacs_aux_eq: "cnf_dimacs = do {
    to_unit_g l_cnf_aux_prelude;
    do {
      g_return {}
    } <|> do {
      x \<leftarrow> cnf_cnf1_aux;
      _ \<leftarrow> to_unit_g l_cnf_ws;
      g_return x
    }}"
    unfolding cnf_dimacs_def g_ignore_right_def
    by (simp 
      add: cnf_eq_cnf1_aux g_lang_simps l_cnf_aux_prelude_def[symmetric] to_unit_g
      add: union_bind_distrib_left union_bind_distrib_right g_union_assoc
      )
    
  definition "l_cnf1_aux = l_cnf_clause \<cdot> (l_cnf_ws1 \<cdot> l_cnf_clause)\<^sup>\<star>"  
  lemma g_lang_cnf1_aux[g_lang_simps]: "g_lang cnf_cnf1_aux = l_cnf1_aux"
    unfolding cnf_cnf1_aux_def l_cnf1_aux_def
    by (simp_all add: g_lang_simps)
    
  lemma is_el_clause[simp]: "\<not> is_el l_cnf_clause"  
    unfolding l_cnf_clause_def
    by auto
  
  lemma is_el_cnf1_aux[simp]: "\<not> is_el l_cnf1_aux"
    unfolding l_cnf1_aux_def
    by simp
    
  lemma has_eps_cnf1_aux[simp]: "\<not> has_eps l_cnf1_aux"  
    unfolding l_cnf1_aux_def
    by auto
    
  lemma lh1_cnf1_aux[simp]: "lh1 l_cnf1_aux = insert char_MINUS digits"  
    unfolding l_cnf1_aux_def
    by simp
    

    

  lemma g_uniq_cnf1_aux[g_uniq_intros]: "g_uniq cnf_cnf1_aux l_cnf_ws"
    unfolding cnf_cnf1_aux_def g_ignore_left_lift2

    apply (intro g_uniq_intros g_uniq_mk_unitI)
    apply (simp add: g_lang_simps)
    subgoal
      apply (rule L_disj_charset_must_mayI)
      apply simp
      by (auto simp: is_whitespace_alt)

    apply (auto simp add: g_lang_simps is_whitespace_alt) []
    done
        
  lemma g_uniq_cnf_dimacs[g_uniq_intros]: "g_uniq cnf_dimacs {[]}"
    unfolding cnf_dimacs_aux_eq
    apply (intro g_uniq_intros g_uniq_mk_unitI)
    
    apply (simp_all add: g_lang_simps)

    apply (subst g_lang_simps | intro gl_indep_intros)+
    apply (auto simp add: g_lang_simps is_whitespace_alt)[]
    
    apply (subst g_lang_simps | intro gl_indep_intros)+
    apply (auto simp add: g_lang_simps is_whitespace_alt is_digit_alt)[]

    apply (subst g_lang_simps | intro gl_indep_intros)+
    apply (auto simp add: g_lang_simps is_whitespace_alt is_digit_alt)[]

    apply (subst g_lang_simps | intro gl_indep_intros)+
    apply simp
    
    apply (subst g_lang_simps | intro gl_indep_intros)+
    apply simp
    
    apply (rule g_uniq_intros)    
    
    apply (subst g_lang_simps | intro gl_indep_intros)+
    apply (simp flip: has_eps_def)
    done
    
  theorem unamb_dimacs: "unambiguous cnf_dimacs"
    by (simp add: unambiguous_eq_uniq g_uniq_cnf_dimacs)
  
  (* For paper *)
  corollary "(w,f)\<in>gM_rel cnf_dimacs \<and> (w,f')\<in>gM_rel cnf_dimacs \<Longrightarrow> f=f'"
    using unamb_dimacs unfolding unambiguous_def single_valued_def by blast
    
    
    
    
  (*
  lemma append_Cons_eq_iff2:
    assumes "x\<notin>set s\<^sub>1'" "x'\<notin>set s\<^sub>1"
    shows "s\<^sub>1@x#s\<^sub>2 = s\<^sub>1'@x'#s\<^sub>2' \<longleftrightarrow> s\<^sub>1=s\<^sub>1' \<and> x=x' \<and> s\<^sub>2=s\<^sub>2'"
    using assms
    by (auto elim: list_match_lel_lel)
    
    
    
        
  lemma append3_eq_conv:
    assumes "a\<noteq>[]" "a'\<noteq>[]" "b\<noteq>[]" "b'\<noteq>[]" "set a \<inter> set b' = {}" "set a' \<inter> set b = {}"
    shows "a@b@c = a'@b'@c' \<longleftrightarrow> a=a' \<and> b@c = b'@c'"  
    apply (rule)
    subgoal
      apply (subst (asm) append_eq_append_conv2)
      using assms
      by (auto simp: neq_Nil_conv append_eq_Cons_conv Cons_eq_append_conv)
    subgoal by simp
    done

    
  lemma append_dj_sets_base:
    assumes A: "a\<noteq>[]" "a'\<noteq>[]" "b\<noteq>[]" "b'\<noteq>[]" 
    assumes B: "set a \<inter> set b' = {}" "set a' \<inter> set b = {}"
    shows "a@b = a'@b' \<longleftrightarrow> a=a' \<and> b=b'"      
    using B
    by (auto simp: append_eq_append_conv2 A)
    
  lemma append_dj_sets_step:
    assumes A: "a\<noteq>[]" "a'\<noteq>[]" "b\<noteq>[]" "b'\<noteq>[]" "c\<noteq>[]" "c'\<noteq>[]"
    assumes B: "set a \<inter> set b' = {}" "set a' \<inter> set b = {}" "set b \<inter> set c' = {}" "set b' \<inter> set c = {}"
    shows "a@b@c@r = a'@b'@c'@r' \<longleftrightarrow> a=a' \<and> b=b' \<and> c@r = c'@r'"      
    apply (rule)
    subgoal
      apply (subst (asm) append3_eq_conv; clarsimp simp: A B)
      apply (subst (asm) append3_eq_conv; clarsimp simp: A B)
      done
    by auto  

  *)  
    
    
end


end
