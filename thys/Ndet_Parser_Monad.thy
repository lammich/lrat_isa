theory Ndet_Parser_Monad
imports LRAT_Sepref_Base "HOL-Library.Complete_Partial_Order2"
begin

  (* TODO: Move *)  
  lemmas disjointD = disjoint_iff[THEN iffD1, rule_format]

  (* TODO: Move *)  
  fun nat2ss_induct where
    "nat2ss_induct 0 0 = ()"  
  | "nat2ss_induct 0 _ = ()"  
  | "nat2ss_induct _ 0 = ()"  
  | "nat2ss_induct (Suc n\<^sub>1) (Suc n\<^sub>2) = nat2ss_induct n\<^sub>1 n\<^sub>2" 
    
  thm nat2ss_induct.induct
  

section \<open>Language Algebra\<close>
text \<open>We define concatenation, power, and Kleene star on sets of lists (Languages)\<close>

  (* Partially taken from afp/Kleene_Algebra *)  
    
  type_synonym 'a lang = "'a list set"

  locale lang_syntax begin
    no_notation hfunspec ("(_\<^sup>?)" [1000] 999)
  
  end
  
  subsection \<open>Character Class\<close>
  definition char_class where "char_class C = {[c] | c. c\<in>C}"

  notation (in lang_syntax) char_class ("\<lbrace>_\<rbrace>")
  
  context begin interpretation lang_syntax .
  lemma in_char_class: "s\<in>\<lbrace>C\<rbrace> \<longleftrightarrow> (\<exists>c\<in>C. s=[c])"
    unfolding char_class_def by auto    
  
  end
    
  subsection \<open>Concat\<close>
  definition L_concat :: "'a lang \<Rightarrow> 'a lang \<Rightarrow> 'a lang"  where 
    "L_concat A B \<equiv> { a@b | a b. a\<in>A \<and> b\<in>B }"
  
  notation (in lang_syntax) L_concat (infixl "\<cdot>" 75)

  context begin interpretation lang_syntax .

  lemma "L\<^sub>1 \<cdot> L\<^sub>2 = { w\<^sub>1@w\<^sub>2 | w\<^sub>1 w\<^sub>2. w\<^sub>1\<in>L\<^sub>1 \<and> w\<^sub>2\<in>L\<^sub>2 }" unfolding L_concat_def by blast

  lemma L_concat_simps[simp]: 
    "a\<cdot>{} = {}"
    "{}\<cdot>a = {}"
    
    "a\<cdot>{[]} = a"
    "{[]}\<cdot>a = a"
    
    "a\<cdot>(b\<cdot>c) = a\<cdot>b\<cdot>c"
    unfolding L_concat_def 
    apply simp_all
    subgoal by (metis (no_types, opaque_lifting) append.assoc)
    done    
    
  lemma L_concat_mono: "a\<subseteq>a' \<Longrightarrow> b\<subseteq>b' \<Longrightarrow> a\<cdot>b \<subseteq> a'\<cdot>b'" 
    unfolding L_concat_def 
    by blast
    
  lemma L_concat_iff: "x\<in>a\<cdot>b \<longleftrightarrow> (\<exists>x\<^sub>1 x\<^sub>2. x=x\<^sub>1@x\<^sub>2 \<and> x\<^sub>1\<in>a \<and> x\<^sub>2\<in>b)" 
    unfolding L_concat_def by auto 

  subsection \<open>Power\<close>  
        
  definition L_pow :: "'a lang \<Rightarrow> nat \<Rightarrow> 'a lang" where "L_pow L n \<equiv> (((\<cdot>)L) ^^ n) {[]}"
  
  lemma L_pow_simps[simp]:
    "L_pow L 0 = {[]}"
    "L_pow L (Suc n) = L \<cdot> L_pow L n"
    unfolding L_pow_def
    by auto
  
  lemma L_pow_add[simp]: "L_pow L (n+m) = L_pow L n \<cdot> L_pow L m"
    apply (induction n)
    by auto 
  
  lemma L_pow_unfold_left: "L_pow L (Suc n) = L_pow L n \<cdot> L" 
    using L_pow_add[of L n 1, simplified] by simp 

  subsection \<open>Star\<close>
                
  definition L_star :: "'a lang \<Rightarrow> 'a lang" where "L_star L = (\<Union>n. L_pow L n)"  

  end
  
  notation (in lang_syntax) L_star ("_\<^sup>\<star>" [101] 100)
  
  context begin
  
  interpretation lang_syntax .
        
  lemma L_star_unfold: "L_star L = {[]} \<union> L \<cdot> L_star L"
    unfolding L_star_def
    apply rule
    subgoal
      apply clarsimp
      subgoal for w n
        apply (cases n; simp)
        by (auto simp: L_concat_iff)
      done
    subgoal
      apply safe
      subgoal by (auto intro: exI[where x=0]) 
      apply (clarsimp simp: L_concat_iff)
      subgoal for x1 x2 n
        apply (rule exI[where x="Suc n"])
        by (auto simp: L_concat_iff)
      done
    done
    
  subsection \<open>Optional\<close>
    
  definition L_opt where "L_opt L \<equiv> insert [] L"  

  end

  notation (in lang_syntax) L_opt ("_\<^sup>?" [101] 100)
    
  context begin
  
  interpretation lang_syntax .
      
  lemma L_opt_simps[simp]: 
    "{}\<^sup>? = {[]}"
    "{[]}\<^sup>? = {[]}"
    unfolding L_opt_def by auto
    
  lemma L_opt_add_simps:
    "(a\<union>b)\<^sup>? = a\<^sup>? \<union> b\<^sup>?"
    unfolding L_opt_def by auto

  lemma l_join_same_tail: "a\<cdot>b \<union> b = a\<^sup>? \<cdot> b"
    unfolding L_opt_def L_concat_def
    by auto
    
    
  end  


  experiment
  begin
      
    context begin interpretation lang_syntax .
  
      
    definition "l_char \<equiv> \<lbrace> { c . 65\<le>c \<and> c\<le>90 } :: 8 word set \<rbrace>"
    definition "l_space \<equiv> \<lbrace> { 32 } :: 8 word set \<rbrace>"
      
    definition "l_id \<equiv> l_char \<cdot> l_char\<^sup>\<star>"
  
    definition "l_idlist \<equiv> l_id \<cdot> ( l_space \<cdot> l_space\<^sup>\<star> \<cdot> l_id )\<^sup>\<star>"  
    
      
    end
  
  end
  
section \<open>Grammar Monad\<close>
text \<open>We define a grammar monad, that produces a relation between input and abstract syntax tree\<close>    
    
datatype ('a,'r) gM = GR (gM_rel: "('a list \<times> 'r) set")

lemma gM_rel_eq_iff: "gM_rel m = gM_rel m' \<longleftrightarrow> m=m'"
  by (cases m; auto)  
  

subsection \<open>Pointwise Reasoning\<close>    
  named_theorems igr_inits
  named_theorems igr_simps
    
  lemma igr_eq_iff[igr_inits]: "m=m' \<longleftrightarrow> (\<forall>w r. (w,r)\<in>gM_rel m \<longleftrightarrow> (w,r)\<in>gM_rel m')"
    by (cases m; cases m') auto  
  
  method igr = 
    simp add: igr_inits igr_simps; blast

  method igr_simp = 
    (simp add: igr_inits igr_simps) []
        
  method igr' = 
    (auto simp add: igr_inits igr_simps) []
    
  method igr_force =
    (force simp add: igr_inits igr_simps)
       
  method igr_fastforce =
    (fastforce simp add: igr_inits igr_simps)

subsection \<open>Basic Combinators\<close>    

subsubsection \<open>Empty, return, this\<close>
  text \<open>The empty language\<close>
  definition "g_empty \<equiv> GR {}"
  
  text \<open>Empty word\<close>
  definition "g_return x \<equiv> GR {([],x)}"

  text \<open>Set of words\<close>  
  definition "g_this S \<equiv> GR {(xs,xs) | xs. xs\<in>S}"
  
  lemma igr_empty[igr_simps]: "wr\<notin>gM_rel g_empty"
    unfolding g_empty_def by auto  
        
  lemma igr_return[igr_simps]: "(w,r) \<in> gM_rel (g_return x) \<longleftrightarrow> w=[] \<and> r=x"
    unfolding g_return_def by auto  

  lemma igr_this[igr_simps]: "(w,r) \<in> gM_rel (g_this S) \<longleftrightarrow> w=r \<and> r\<in>S"
    unfolding g_this_def by auto
  
  lemma empty_return_simps[simp]:
    "g_empty \<noteq> g_return x"
    "g_return x \<noteq> g_empty"
    "g_return x = g_return y \<longleftrightarrow> x=y"
    by igr+

  lemma g_empty_this_simps[simp]:
    "g_this {} = g_empty"
    "g_empty = g_this P \<longleftrightarrow> P={}"  
    "g_this P = g_empty \<longleftrightarrow> P={}"
    by igr+
    
  lemma g_this_return_simps[simp]:  
    "g_this P = g_return x \<longleftrightarrow> (P={[]} \<and> x=[])"  
    "g_return x = g_this P \<longleftrightarrow> (P={[]} \<and> x=[])"  
    unfolding g_this_def g_return_def 
    by igr+
    

  subsubsection \<open>Bind\<close>          
  definition "g_bind m (\<lambda>x. f x) \<equiv> GR { (xs@ys,r) | xs ys r x. (xs,x) \<in> gM_rel m \<and> (ys,r) \<in> gM_rel (f x) }"
  adhoc_overloading Monad_Syntax.bind g_bind
  
  lemma igr_bind[igr_simps]: "(w,r)\<in>gM_rel (do {x\<leftarrow>m; f x}) \<longleftrightarrow> (\<exists>w\<^sub>1 x w\<^sub>2. (w\<^sub>1,x)\<in>gM_rel m \<and> (w\<^sub>2,r)\<in>gM_rel (f x) \<and> w=w\<^sub>1@w\<^sub>2 )"  
    unfolding g_bind_def
    by auto
  
  lemma g_monad_laws[simp]:
    "do { x\<leftarrow>g_return a; f x } = f a"
    "do { x\<leftarrow>m; g_return x } = m"
    "do { y \<leftarrow> do { x\<leftarrow>m; f x }; g y } = do {x\<leftarrow>m; y\<leftarrow>f x; g y}" 
    apply igr
    apply igr
    apply (igr'; fastforce)
    done
       
  lemma g_bind_empty_laws[simp]: 
    "g_empty \<bind> f = g_empty"
    "do { m; g_empty } = g_empty"
    by igr+

  subsubsection \<open>Union\<close>    
      
  definition g_union where "g_union a b \<equiv> GR (gM_rel a \<union> gM_rel b)"
  
  notation (in lang_syntax) g_union (infixl "<|>" 60)
  
  definition g_Union where "g_Union M \<equiv> GR (\<Union>(gM_rel`M))"

  
  context begin
  
  interpretation lang_syntax .
  
  lemma igr_union[igr_simps]: "wr \<in> gM_rel (a <|> b) \<longleftrightarrow> wr\<in>gM_rel a \<or> wr\<in>gM_rel b"
    unfolding g_union_def by auto  
  
  lemma igr_Union[igr_simps]: "wr \<in> gM_rel (g_Union M) \<longleftrightarrow> (\<exists>m\<in>M. wr \<in> gM_rel m)" 
    unfolding g_Union_def by auto
    

  lemma g_Union_simps[simp]:
    "g_Union {} = g_empty"  
    "g_Union (insert m M) = m <|> g_Union M"  
    by igr+
    
  lemma g_union_empty_laws[simp]: 
    "g_empty <|> m = m"
    "m <|> g_empty = m"  
    by igr+
    
  lemma g_union_ac: 
    "a <|> b <|> c = a <|> (b <|> c)"
    "a <|> b = b <|> a"
    "b <|> (a <|> c) = a <|> (b <|> c)"
    by igr+
    
  lemma g_union_assoc: "a<|>(b<|>c) = a<|>b<|>c" by igr
    
  lemma union_bind_distrib_right: "((x <|> y) \<bind> z) = (x \<bind> z) <|> (y \<bind> z)"
    by igr+

  lemma union_bind_distrib_left: "do {r\<leftarrow>x; y r <|> z r} = (do {r\<leftarrow>x; y r}) <|> (do {r\<leftarrow>x; z r})"
    by igr+
        
  lemma g_union_idem[simp]: "a <|> a = a"
    by igr+

  lemma g_Union_distrib_bind: "do { x\<leftarrow>g_Union M; c x } = g_Union { do { x \<leftarrow> m; c x } | m. m \<in> M }"
    apply igr'
    subgoal for r w\<^sub>1 x m w\<^sub>2
      apply (rule exI[ where x="do { x \<leftarrow> m; c x }"])
      by igr
    subgoal by blast
    done
    
  lemma g_Union_Union_join: "do { x \<leftarrow> g_Union A; y \<leftarrow> g_Union B; f x y } 
     = g_Union {do { x \<leftarrow> a; y \<leftarrow> b; f x y } |a b. a \<in> A \<and> b \<in> B}"
     apply igr_simp
     
     apply (intro conjI allI iffI; clarsimp?)
     
     subgoal for r w\<^sub>1 x a w\<^sub>1' xa b w\<^sub>2'
       apply (rule exI[where x="do { x \<leftarrow> a; y \<leftarrow> b; f x y }"])
       by igr
     subgoal by blast
     done

     
  end   
subsection \<open>Partial Function Setup\<close>    
    
  definition "g_ord a b \<equiv> gM_rel a \<subseteq> gM_rel b"  

  lemma g_ord_alt: "g_ord a b \<longleftrightarrow> g_union a b = b"
    unfolding g_ord_def g_union_def 
    by (cases a; cases b; auto)
  
  lemma g_ord_igr[igr_inits]: "g_ord a b \<longleftrightarrow> (\<forall>w r. (w,r)\<in>gM_rel a \<longrightarrow> (w,r)\<in>gM_rel b)"  
    unfolding g_ord_def by auto
    
  lemma g_ord_refl[simp]: "g_ord a a" unfolding g_ord_def by simp
  lemma g_ord_antisym: "g_ord a b \<Longrightarrow> g_ord b a \<Longrightarrow> a=b" unfolding g_ord_def by (simp add: gM_rel_eq_iff)
  lemma g_ord_trans[trans]: "g_ord a b \<Longrightarrow> g_ord b c \<Longrightarrow> g_ord a c" unfolding g_ord_def by simp
      
  definition "g_lub M = (GR (\<Union>m\<in>M. gM_rel m))"
  
  lemma g_lub_igr[igr_simps]: "pw\<in>gM_rel (g_lub M) \<longleftrightarrow> (\<exists>m\<in>M. pw\<in>gM_rel m)"
    unfolding g_lub_def by auto
  
  abbreviation "mono_g \<equiv> monotone (fun_ord g_ord) g_ord"
  
  lemma g_pfd: "partial_function_definitions g_ord g_lub"
    apply unfold_locales by igr+

  lemma g_lub_empty: "g_lub {} = g_empty"
    by igr
    
  interpretation gM:
    partial_function_definitions g_ord g_lub
    rewrites "g_lub {} \<equiv> g_empty"
    apply (rule g_pfd)
    by (simp add: g_lub_empty)


  lemma gM_admissible: "gM.admissible (\<lambda>f. \<forall>x pw. pw\<in>gM_rel (f x) \<longrightarrow> P x pw)"  
    apply (rule ccpo.admissibleI)
    unfolding fun_lub_def
    by igr'
  

  lemma fixp_induct_gM:
    fixes F :: "'c \<Rightarrow> 'c" and
      U :: "'c \<Rightarrow> 'b \<Rightarrow> ('a,'r) gM" and
      C :: "('b \<Rightarrow> ('a,'r) gM) \<Rightarrow> 'c" and
      P :: "'b \<Rightarrow> ('a list \<times> 'r) \<Rightarrow> bool"
    assumes mono: "\<And>x. mono_g (\<lambda>f. U (F (C f)) x)"
    assumes eq: "f \<equiv> C (ccpo.fixp (fun_lub g_lub) (fun_ord g_ord) (\<lambda>f. U (F (C f))))"
    assumes inverse2: "\<And>f. U (C f) = f"
    assumes step: "\<And>f x y. (\<And>x y. y\<in>gM_rel (U f x) \<Longrightarrow> P x y) \<Longrightarrow> y\<in>gM_rel (U (F f) x) \<Longrightarrow> P x y"
    assumes defined: "y\<in> gM_rel (U f x)"
    shows "P x y"
    using step defined gM.fixp_induct_uc[of U F C, OF mono eq inverse2 gM_admissible, of P]
    
    unfolding g_empty_def
    apply (cases y)
    apply (simp (no_asm_use))
    by fast    
    
      
  declaration \<open>Partial_Function.init "gM" \<^term>\<open>gM.fixp_fun\<close>
    \<^term>\<open>gM.mono_body\<close> @{thm gM.fixp_rule_uc} @{thm gM.fixp_induct_uc}
    (SOME @{thm fixp_induct_gM})\<close>

  lemma bind_gM_mono[partial_function_mono]:
    assumes mf: "mono_g B" and mg: "\<And>y. mono_g (\<lambda>f. C y f)"
    shows "mono_g (\<lambda>f. g_bind (B f) (\<lambda>y. C y f))"
    using assms
    unfolding monotone_def fun_ord_def flat_ord_def
    by igr
    
  lemma union_gM_mono[partial_function_mono]:
    assumes ma: "mono_g A" and mb: "mono_g B"
    shows "mono_g (\<lambda>f. g_union (A f) (B f))"
    using assms
    unfolding monotone_def fun_ord_def flat_ord_def
    by igr
    
    
  lemma gM_rel_pointwise_mcont[cont_intro]: "mcont gM.lub_fun gM.le_fun \<Union> (\<subseteq>) (\<lambda>x. gM_rel (x args))"
    apply (intro mcontI cont_intro)      
    subgoal
      apply (rule monotoneI)
      by (simp add: fun_ord_def g_ord_def)    
    subgoal
      apply (rule)
      by (simp add: g_lub_def)
    done  
    
    
    
subsection \<open>More Combinators\<close>    
    
    
  subsubsection \<open>Apply\<close>  
    
  definition g_apply where "g_apply m f \<equiv> do { x\<leftarrow>m; g_return (f x) }"

  notation (in lang_syntax) g_apply (infixl "<&>" 90)
  
  context begin interpretation lang_syntax .
  
  lemma igr_apply[igr_simps]: "(w,r) \<in> gM_rel (m <&> f) \<longleftrightarrow> (\<exists>r'. (w,r')\<in> gM_rel m \<and> r=f r')"  
    unfolding g_apply_def
    by igr  
  
  lemma g_apply_simps[simp]: 
    "g_empty <&> f = g_empty"
    "g_return x <&> f = g_return (f x)"
  
    "m <&> id = m"
    "m <&> f <&> g = m <&> (g o f)"
    by igr+

  lemma g_apply_unit[simp]: "m <&> f = m" for f :: "unit \<Rightarrow> unit"
    by igr  

  lemma g_Union_apply: "g_Union M <&> f = g_Union ({m <&> f | m. m\<in>M })" 
    supply [intro] = exI[where x="_ <&> f"]
    by igr_fastforce
    

  subsubsection \<open>Lift2\<close>
  text \<open>Lift a binary operation\<close>
  definition "g_lift2 op a b \<equiv> do { x\<leftarrow>a; y\<leftarrow>b; g_return (op x y) }"
  
  lemma igr_lift2[igr_simps]: 
    "(w,r)\<in>gM_rel (g_lift2 op a b) \<longleftrightarrow> (\<exists>w\<^sub>1 x w\<^sub>2 y. (w\<^sub>1,x)\<in>gM_rel a \<and> (w\<^sub>2,y)\<in>gM_rel b \<and> w=w\<^sub>1@w\<^sub>2 \<and> r = op x y)"
    unfolding g_lift2_def
    by igr
  
  lemma g_lift2_mono[partial_function_mono]: 
    assumes ma: "mono_g A" and mb: "mono_g B"
    shows "mono_g (\<lambda>f. g_lift2 op (A f) (B f))"
    unfolding g_lift2_def
    using assms
    by (intro partial_function_mono)
  
  lemma g_lift2_simps[simp]:
    "g_lift2 op g_empty b = g_empty"
    "g_lift2 op a g_empty = g_empty"
    
    "g_lift2 op (g_return x) b = b <&> op x"
    "g_lift2 op a (g_return y) = a <&> (\<lambda>x. op x y)"
    unfolding g_lift2_def g_apply_def
    by auto

    
  lemma g_lift2_apply: 
    "g_lift2 op (m\<^sub>1 <&> f\<^sub>1) (m\<^sub>2 <&> f\<^sub>2) = g_lift2 (\<lambda>a b. op (f\<^sub>1 a) (f\<^sub>2 b)) m\<^sub>1 m\<^sub>2"
    unfolding g_lift2_def g_apply_def
    by auto

  lemma g_lift2_apply_left: 
    "g_lift2 op (m\<^sub>1 <&> f\<^sub>1) m\<^sub>2 = g_lift2 (\<lambda>a b. op (f\<^sub>1 a) b) m\<^sub>1 m\<^sub>2"
    using g_lift2_apply[where f\<^sub>2=id] by auto 
        
  lemma g_lift2_apply_right: 
    "g_lift2 op (m\<^sub>1) (m\<^sub>2 <&> f\<^sub>2) = g_lift2 (\<lambda>a b. op a (f\<^sub>2 b)) m\<^sub>1 m\<^sub>2"
    using g_lift2_apply[where f\<^sub>1=id] by auto 
    
  
  end
      
  subsubsection \<open>Power\<close>
  (*
    Analogously to fold, there is a left and right power
  *)
  context fixes m :: "('a,'b) gM" and fi :: "('c\<Rightarrow>'b\<Rightarrow>'c) \<times> 'c" begin  
    fun g_powl where
      "g_powl 0 = g_return (snd fi)"
    | "g_powl (Suc n) = g_lift2 (fst fi) (g_powl n) m"
    
  end

  (* Example for left-associativity: *)
  lemma "g_powl m (f,i) 3 = g_lift2 f (g_lift2 f (g_lift2 f (g_return i) m) m) m"
    by (simp add: eval_nat_numeral)
      
  context fixes m :: "('a,'b) gM" and fi :: "('b\<Rightarrow>'c\<Rightarrow>'c) \<times> 'c" begin  
    fun g_powr where
      "g_powr 0 = g_return (snd fi)"
    | "g_powr (Suc n) = g_lift2 (fst fi) m (g_powr n)"

        
  end  

  (* Example for right-associativity: *)
  lemma "g_powr m (f,i) 3 = g_lift2 f m (g_lift2 f m (g_lift2 f m (g_return i)))"
    by (simp add: eval_nat_numeral)

    
  context begin interpretation lang_syntax .
    
  (* Normalized AST form *)  
    
  lemma g_powr_Cons_foldr: "g_powr m ((#),[]) n <&> (\<lambda>xs. foldr f xs i) = g_powr m (f,i) n"
    apply (rule sym)
    apply (induction n)
    apply (simp)
    apply (simp)
    apply (simp add: g_apply_def g_lift2_def) (* Going back to basic monad definitions, and using monad laws *)
    done

  lemma g_powl_snoc_foldl: "g_powl m (\<lambda>xs x. xs@[x],[]) n <&> (foldl f i) = g_powl m (f,i) n"
    apply (rule sym)
    apply (induction n)
    apply (simp)
    apply (simp)
    apply (simp add: g_apply_def g_lift2_def) (* Going back to basic monad definitions, and using monad laws *)
    done

  end      
    
  subsubsection \<open>Star\<close>
  
  definition g_starr where "g_starr m ce = g_Union { g_powr m ce n | n. True }"
  definition g_starl where "g_starl m ce = g_Union { g_powl m ce n | n. True }"


  notation (in lang_syntax) g_starr (infixl "*&" 100) 
  notation (in lang_syntax) g_starl (infixl "&*" 100)  

  context begin interpretation lang_syntax .
  
          
  lemma igr_starr[igr_simps]: "(w,r) \<in> gM_rel (m *& fi) \<longleftrightarrow> (\<exists>n. (w,r) \<in> gM_rel (g_powr m fi n))"
    unfolding g_starr_def
    by igr' 

  lemma igr_starl[igr_simps]: "(w,r) \<in> gM_rel (m &* fi) \<longleftrightarrow> (\<exists>n. (w,r) \<in> gM_rel (g_powl m fi n))"
    unfolding g_starl_def
    by igr' 
    
        
  lemma g_starr_unfold: "g_starr m fi = g_return (snd fi) <|> g_lift2 (fst fi) m (g_starr m fi)"
    apply (simp add: igr_eq_iff igr_starr; safe)
    subgoal for w r n
      by (cases n; igr) 
    subgoal for w r
      apply (simp add: igr_simps; safe)
      subgoal
        apply (rule exI[where x=0])
        by igr
      subgoal for w\<^sub>1 x w\<^sub>2 y n
        apply (rule exI[where x="Suc n"])
        by igr
      done
    done

  lemma g_starl_unfold: "g_starl m fi = g_return (snd fi) <|> g_lift2 (fst fi) (g_starl m fi) m"
    apply (simp add: igr_eq_iff igr_starl; safe)
    subgoal for w r n
      by (cases n; igr) 
    subgoal for w r
      apply (simp add: igr_simps; safe)
      subgoal
        apply (rule exI[where x=0])
        by igr
      subgoal for w\<^sub>1 x n w\<^sub>2 y
        apply (rule exI[where x="Suc n"])
        by igr
      done
    done

  paragraph \<open>Star as fixed Point\<close>  
    
  partial_function (gM) g_starr' where 
    "g_starr' m fi = g_return (snd fi) <|> g_lift2 (fst fi) m (g_starr' m fi)" 

  partial_function (gM) g_starl' where 
    "g_starl' m fi = g_return (snd fi) <|> g_lift2 (fst fi) (g_starl' m fi) m" 
    
    
    
  lemma g_starr_as_fixp: "g_starr' m fi = g_starr m fi"
    apply (simp add: igr_eq_iff igr_starr; safe)
  proof -
    fix w r n 
    assume "(w, r) \<in> gM_rel (g_powr m fi n)"  
    thus "(w, r) \<in> gM_rel (g_starr' m fi)"  
      apply (induction n arbitrary: w r)
      apply (subst g_starr'.simps)
      apply (auto simp: igr_simps) []
      apply (subst g_starr'.simps)
      apply (auto simp: igr_simps; blast) []
      done
  next
    fix w r 
    assume "(w, r) \<in> gM_rel (g_starr' m fi)"  
    thus "\<exists>n. (w, r) \<in> gM_rel (g_powr m fi n)"        
      apply (induction arbitrary: w r rule: g_starr'.fixp_induct)
      apply simp
      apply (simp add: igr_simps)
      apply (clarsimp simp: igr_simps; safe)
      subgoal by (auto intro: exI[where x=0] simp: igr_simps)
      subgoal by (force intro: exI[where x=0] exI[where x="Suc _"] simp: igr_simps)
      done
  qed

  lemma g_starl_as_fixp: "g_starl' m fi = g_starl m fi"
    apply (simp add: igr_eq_iff igr_starl; safe)
  proof -
    fix w r n 
    assume "(w, r) \<in> gM_rel (g_powl m fi n)"  
    thus "(w, r) \<in> gM_rel (g_starl' m fi)"  
      apply (induction n arbitrary: w r)
      apply (subst g_starl'.simps)
      apply (auto simp: igr_simps) []
      apply (subst g_starl'.simps)
      apply (auto simp: igr_simps; blast) []
      done
  next
    fix w r 
    assume "(w, r) \<in> gM_rel (g_starl' m fi)"  
    thus "\<exists>n. (w, r) \<in> gM_rel (g_powl m fi n)"        
      apply (induction arbitrary: w r rule: g_starl'.fixp_induct)
      apply simp
      apply (simp add: igr_simps)
      apply (clarsimp simp: igr_simps; safe)
      subgoal by (auto intro: exI[where x=0] simp: igr_simps)
      subgoal by (force intro: exI[where x=0] exI[where x="Suc _"] simp: igr_simps)
      done
  qed

  end  
      
subsection \<open>Algebraic Structure of Cons,Append,Empty\<close>

  (*
    Structure with a cons, empty and append, such that empty is a left-id, and append is associative
  *)  
  
  locale assoc_cons_append_struct = 
    fixes cons :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
      and append :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
    assumes 
      cons_append_assoc: "append (cons x ys) zs = cons x (append ys zs)"
      
  begin   
  end
  
  (* The dual is a snoc-append structure *)  
  locale assoc_snoc_append_struct = 
    fixes snoc :: "'b \<Rightarrow> 'a \<Rightarrow> 'b"
      and append :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
    assumes 
      snoc_append_assoc: "append xs (snoc ys z) = snoc (append xs ys) z"
      
  begin   
    
  end

  (* Append and empty are a monoid *)
  locale append_empty_monoid =
    fixes empty :: 'b
      and append :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  
    assumes append_left_id: "append empty xs = xs" 
    assumes append_right_id: "append xs empty = xs" 
    assumes append_assoc: "append (append xs ys) zs = append xs (append ys zs)"
  begin
    lemmas append_ai = append_left_id append_right_id append_assoc
  
  end  

  term semigroup
    
  locale assoc_cons_append_monoid_struct = assoc_cons_append_struct + append_empty_monoid +
    constrains cons :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  begin
    abbreviation (input) snoc :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" where "snoc xs x \<equiv> append xs (cons x empty)"
    abbreviation (input) "ce \<equiv> (cons,empty)" 
  end
  
  locale assoc_snoc_append_monoid_struct = assoc_snoc_append_struct + append_empty_monoid +
    constrains snoc :: "'b \<Rightarrow> 'a \<Rightarrow> 'b"
  begin
    abbreviation (input) cons :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" where "cons x xs \<equiv> append (snoc empty x) xs"
    abbreviation (input) "ce \<equiv> (snoc,empty)" 
  end

  
  context assoc_cons_append_monoid_struct begin
    lemma dual: "assoc_snoc_append_monoid_struct snoc append empty"
      apply (unfold_locales)
      by (simp add: append_ai)
    
  end
  
  context assoc_snoc_append_monoid_struct begin
    lemma dual: "assoc_cons_append_monoid_struct cons append empty"
      apply (unfold_locales)
      by (simp add: append_ai)
    
  end
      
    
  context assoc_cons_append_monoid_struct begin 
    context
      notes [simp] = cons_append_assoc append_ai
    begin
  
      lemma g_powr_add: "g_powr m ce (n+n') = g_lift2 (append) (g_powr m ce n) (g_powr m ce n')"  
        apply (induction n)
        apply (simp add: g_apply_def)
        apply simp
        by (simp add: g_apply_def g_lift2_def) (* Going back to basic monad definitions, and using monad laws *)
    
      lemma g_powr_Suc_rev: "g_powr m ce (Suc n) = g_lift2 snoc (g_powr m ce n) m"  
        supply [simp del] = g_powr.simps(2)
        apply (simp add: g_powr_add[of _ n 1, simplified])
        apply (simp add: g_powr.simps(2))
        by (simp add: g_apply_def g_lift2_def) (* Going back to basic monad definitions, and using monad laws *)
      
      lemma g_powr_conv_l: "g_powr m ce n = g_powl m (snoc,empty) n"
        supply [simp del] = g_powr.simps(2)
        apply (induction n)
        apply simp    
        apply (simp add: g_powr_Suc_rev)    
        done
        
                
    end      

    interpretation lang_syntax .
        
    lemma g_starr_join: "g_lift2 append (a *& ce) (a *& ce) = a *& ce"
      unfolding g_starr_def g_lift2_def g_Union_Union_join
      apply simp
      apply (fo_rule arg_cong)
      apply (rule )
      subgoal
        by (clarsimp) (metis g_lift2_def g_powr_add)
        (* TODO: Phrase g_powr_add in g_powr \<bind> ctd = \<dots> form *)
      subgoal 
        apply auto
        by (metis add_0 g_lift2_def g_powr_add)
        (* TODO: Phrase g_powr_add in g_powr \<bind> ctd = \<dots> form *)
      done
                
    lemma g_starr_conv_l: "m *& ce = m &* (snoc,empty)"
      unfolding g_starr_def g_starl_def
      by (simp add: g_powr_conv_l)
    
    
  end      

  (* Technical lemma, to prevent safe/auto from running havoc on common \<Union>_ = \<Union>_ goals *)
  lemma cleanup_double_set_image: "{f m |m. m \<in> {g n |n. P n}} = {f (g n) | n. P n}" by blast

  context begin interpretation lang_syntax .
        
  lemma starl_bind_eqI:
    assumes "\<And>n. do { x \<leftarrow> g_powl a fi n; c x } = do { x' \<leftarrow> g_powl a fi' n; c' x' }"
    shows "do { x \<leftarrow> a &* fi; c x } = do { x' \<leftarrow> a &* fi'; c' x' }"
    unfolding g_starl_def g_Union_distrib_bind cleanup_double_set_image
    by (simp add: assms)

  lemma starr_bind_eqI:
    assumes "\<And>n. do { x \<leftarrow> g_powr a fi n; c x } = do { x' \<leftarrow> g_powr a fi' n; c' x' }"
    shows "do { x \<leftarrow> a *& fi; c x } = do { x' \<leftarrow> a *& fi'; c' x' }"
    unfolding g_starr_def g_Union_distrib_bind cleanup_double_set_image
    by (simp add: assms)

  end  
          
  context assoc_snoc_append_monoid_struct begin
    
    lemma g_powl_append_conv: "do { y \<leftarrow> g_powl a (snoc,i) n; c (append x y) } = do { y' \<leftarrow> g_powl a (snoc,append x i) n; c y'}"
    proof (induction n arbitrary: c)
      case 0 thus ?case by simp
    next
      case (Suc n)
      
      show ?case
        apply (simp add: g_lift2_def snoc_append_assoc)
        apply (subst Suc.IH) 
        ..
    qed    

    interpretation lang_syntax .      
    lemma g_starl_append_conv: "do { y \<leftarrow> a &* (snoc,i); c (append x y) } = do { y' \<leftarrow> a &* (snoc, append x i); c y' }"  
      apply (rule starl_bind_eqI)
      by (simp add: g_powl_append_conv)    
    
  
  end

subsubsection \<open>Standard Append Structures\<close>
  interpretation acam_list: assoc_cons_append_monoid_struct "(#)" "(@)" "[]"
    by unfold_locales auto
    
  interpretation asam_list: assoc_snoc_append_monoid_struct "\<lambda>xs x. xs@[x]" "(@)" "[]"
    by (rule acam_list.dual)
    
    
    
  (*interpretation acam_unit: assoc_cons_append_struct f "()" g
    apply unfold_locales
    by auto
  *)
  
  (* Unlike acam_unit, this version does not introduce extra variables. *)      
  interpretation acam_ignore: assoc_cons_append_monoid_struct "\<lambda>_ _. ()" "\<lambda>_ _. ()" "()"
    apply unfold_locales
    by auto  
    
  context monoid begin
    sublocale assoc_cons_append_monoid_struct "(\<^bold>*)" "(\<^bold>*)" "(\<^bold>1)"
      apply unfold_locales by (simp_all add: ac_simps)
      
  end        

  interpretation acam_insert: assoc_cons_append_monoid_struct insert "(\<union>)" "{}"
    by unfold_locales auto

  interpretation asam_insert: assoc_snoc_append_monoid_struct "\<lambda>s x. insert x s" "(\<union>)" "{}" 
    using acam_insert.dual by simp

      
  abbreviation "ceCons \<equiv> ((#), [])"
  abbreviation "ceIgnore \<equiv> (\<lambda>_ _. (), ())"
  abbreviation "ceInsert \<equiv> (insert, {})"
  abbreviation "ceRevInsert \<equiv> (\<lambda>s x. insert x s, {})"

subsubsection \<open>Folding and Star\<close>

  context begin interpretation lang_syntax .

  lemma g_powr_Cons_foldl:
    fixes f :: "'s \<Rightarrow> 'x \<Rightarrow> 's"
    shows "g_powr m acam_list.ce n <&> (foldl f i) = g_powl m (f,i) n"
    apply (rule sym)
    apply (subst acam_list.g_powr_conv_l)
    apply (simp add: g_powl_snoc_foldl)
    done
  
        
  lemma g_starr_foldl_conv_aux: "{ma <&> f |ma. \<exists>n. ma = X n} = { X n <&> f | n. True }" by auto
  
  lemma g_starr_foldl_conv: "m *& ceCons <&> foldl f s = m &* (f,s)"
    unfolding g_starr_def g_starl_def
    by (simp add: g_Union_apply g_starr_foldl_conv_aux g_powr_Cons_foldl)

  lemma g_starr_fold_conv: "m *& ceCons <&> (\<lambda>xs. fold f xs s) = m &* ((\<lambda>c s. f s c),s)"
    using g_starr_foldl_conv[unfolded List.foldl_conv_fold, of m "(\<lambda>c s. f s c)"]
    .
    
  end
      
subsubsection \<open>Insert and Star\<close>    

  context begin interpretation lang_syntax .
    
  lemma g_starr_insert_first_elem_conv: "do { s \<leftarrow> (a *& ceInsert); c (insert x s)} 
      = do { s' \<leftarrow> a &* (\<lambda>s x. insert x s,{x}); c s' }"  
    apply (simp add: acam_insert.g_starr_conv_l)
    apply (simp add: asam_insert.g_starl_append_conv[where x="{_}", simplified])
    done      
    
  end

experiment
begin


context
  fixes fi :: "('a\<Rightarrow>'b\<Rightarrow>'b) \<times> 'b" and m::"('c,'a) gM"
begin
  interpretation lang_syntax .

  partial_function (gM) starr' where "starr' (uu::unit) = g_return (snd fi) <|> g_lift2 (fst fi) m (starr' ())"   
    
  thm starr'.raw_induct[rotated]
  
  lemma "pw \<in> gM_rel (starr' ()) \<Longrightarrow> pw \<in> gM_rel (m *& fi)"
    apply (induction rule: starr'.raw_induct[rotated, consumes 1])
    apply (subst g_starr_unfold)
    apply igr_fastforce
    done
  
    

end
end



subsection \<open>More Combinators\<close>

context begin interpretation lang_syntax .

definition g_ignore_right where "g_ignore_right m n \<equiv> do { x\<leftarrow>m; n; g_return x }"
definition g_ignore_left :: "_ \<Rightarrow> _ \<Rightarrow> (_,_) gM" where "g_ignore_left m n \<equiv> do { m; n }"

definition g_char where "g_char C \<equiv> GR { ([c],c) | c. c\<in>C }"

definition "g_plus" where "g_plus m fi = g_lift2 (fst fi) m (m *& fi)"


definition g_option where "g_option m = m <&> Some <|> g_return None"

abbreviation g_Cons where "g_Cons \<equiv> g_lift2 (#)"
abbreviation g_append where "g_append \<equiv> g_lift2 (@)"

end

notation (in lang_syntax) g_ignore_right (infixl "\<lless>" 90)
notation (in lang_syntax) g_ignore_left (infixl "\<ggreater>" 90)
notation (in lang_syntax) g_char ("<_>" 1000)
notation (in lang_syntax) "g_plus" (infixl "+&" 100)
notation (in lang_syntax) g_option ("_?" [101] 100)

notation (in lang_syntax) g_Cons (infixl "<#>" 65)
notation (in lang_syntax) g_append (infixl "<@>" 65)


section \<open>Language of a Grammar\<close>

context begin interpretation lang_syntax .

  definition "g_lang g \<equiv> Domain (gM_rel g)"
  
  lemma igr_in_g_lang[igr_simps]: "w\<in>g_lang g \<longleftrightarrow> (\<exists>r. (w,r)\<in>gM_rel g)"
    unfolding g_lang_def
    by auto
  
  lemma igr_lang_eq_iff[igr_inits]: "g_lang g = L \<longleftrightarrow> (\<forall>w. w\<in>g_lang g \<longleftrightarrow> w\<in>L)"
    unfolding g_lang_def
    by auto
  
  
  (* igr-setup for regular languages *)  

  lemma igr_L_opt[igr_simps]: "w\<in>a\<^sup>? \<longleftrightarrow> w\<in>a \<or> w=[]"
    unfolding L_opt_def by auto
      
  lemma igr_L_concat[igr_simps]: "w \<in> a \<cdot> b \<longleftrightarrow> (\<exists>w\<^sub>1 w\<^sub>2. w\<^sub>1\<in>a \<and> w\<^sub>2\<in>b \<and> w=w\<^sub>1@w\<^sub>2)"
    unfolding L_concat_def by auto
      
  lemma igr_L_star[igr_simps]: "w \<in> a\<^sup>\<star> \<longleftrightarrow> (\<exists>n. w\<in>L_pow a n)"  
    unfolding L_star_def by blast
    
  definition "gl_indep f \<equiv> \<forall>x y. g_lang (f x) = g_lang (f y)"  
  
  lemma gl_indep_alt: "gl_indep f \<longleftrightarrow> (\<forall>x. g_lang (f x) = g_lang (f undefined))"
    unfolding gl_indep_def by blast
  
  named_theorems g_lang_simps  
    
  named_theorems gl_indep_intros
  
    
  lemma g_lang_return[g_lang_simps]: "g_lang (g_return x) = {[]}" 
    by igr   
    
  lemma g_lang_empty[g_lang_simps]: "g_lang g_empty = {}"  
    by igr   

  lemma g_lang_this[g_lang_simps]: "g_lang (g_this S) = S"      
    by igr   

  lemma g_lang_Union[g_lang_simps]: "g_lang (g_Union M) = (Union (g_lang`M))"  
    by igr   
    
    
  lemma g_lang_union[g_lang_simps]: "g_lang (a <|> b) = g_lang a \<union> g_lang b"  
    by igr 
    
  lemma g_lang_bind[g_lang_simps]: "gl_indep f \<Longrightarrow> g_lang (g_bind m f) = g_lang m \<cdot> g_lang (f undefined)" 
    unfolding gl_indep_alt L_concat_def
    by igr

  lemma gl_indep_const[gl_indep_intros]: "gl_indep (\<lambda>_. c)" 
    unfolding gl_indep_def by auto 
    
  lemma gl_indep_return[gl_indep_intros]: "gl_indep (\<lambda>x. g_return (f x))"  
    unfolding gl_indep_def 
    by igr

  lemma gl_indep_union[gl_indep_intros]: "gl_indep a \<Longrightarrow> gl_indep b \<Longrightarrow> gl_indep (\<lambda>x. a x <|> b x)"  
    unfolding gl_indep_def
    by igr
            
    
  lemma gl_indep_normD[gl_indep_intros]: "(w,r)\<in>gM_rel (m x) \<Longrightarrow> gl_indep m \<Longrightarrow> (\<exists>r'. (w,r')\<in>gM_rel (m undefined))"  
    unfolding gl_indep_def g_lang_def 
    by blast
    
  lemma ex3_aux_simp: "(\<exists>x y z. a y z \<and> b x y z) = (\<exists>y z. a y z \<and> (\<exists>x. b x y z))" by auto 
    
    
  lemma gl_indep_bind[gl_indep_intros]: 
    assumes "gl_indep m" "\<And>x. gl_indep (f x)" "\<And>y. gl_indep (\<lambda>x. f x y)" 
    shows "gl_indep (\<lambda>x. do {y\<leftarrow>m x; f x y})"
    apply (subst gl_indep_alt)
    apply igr_simp 
    apply safe
    apply (metis (full_types) assms gl_indep_def igr_in_g_lang)
    apply (metis (full_types) assms gl_indep_def igr_in_g_lang)
    done
    
  lemma g_lang_lift2[g_lang_simps]: "g_lang (g_lift2 f a b) = g_lang a \<cdot> g_lang b"
    unfolding g_lift2_def
    apply (subst g_lang_simps | intro gl_indep_intros)+
    by simp    
  

  lemma g_lang_powr[g_lang_simps]: "g_lang (g_powr a fi n) = L_pow (g_lang a) n"
    apply (induction n)
    apply igr
    apply igr
    done
    
    
    
  lemma g_lang_starr[g_lang_simps]: "g_lang (a*&fi) = (g_lang a)\<^sup>\<star>"
    unfolding g_starr_def L_star_def  
    by (auto simp add: g_lang_simps)
    
    
    
  lemma g_lang_powl[g_lang_simps]: "g_lang (g_powl a fi n) = L_pow (g_lang a) n"
    apply (induction n)
    apply igr
    
    supply [simp del] = L_pow_simps
    supply [simp add] = L_pow_unfold_left
    
    apply igr
    done




  lemma glang_char[g_lang_simps]: "g_lang (<C>) = \<lbrace>C\<rbrace>"  
    unfolding g_char_def char_class_def
    by igr

  lemma g_lang_apply[g_lang_simps]: "g_lang (a <&> f) = g_lang a"  
    by igr
        

  lemma g_lang_ignore_left[g_lang_simps]: "g_lang (a \<ggreater> b) = g_lang a \<cdot> g_lang b"
    unfolding g_ignore_left_def by igr  

  lemma g_lang_ignore_right[g_lang_simps]: "g_lang (a \<lless> b) = g_lang a \<cdot> g_lang b"
    unfolding g_ignore_right_def by igr  
   
  lemma g_lang_opt[g_lang_simps]: "g_lang (a?) = (g_lang a)\<^sup>?"
    unfolding g_option_def by igr  
     


end

  
  subsection \<open>Unsorted Lemmas\<close>
  context begin interpretation lang_syntax .
  
  lemma l_char_classI: "c\<in>C \<Longrightarrow> [c]\<in>\<lbrace>C\<rbrace>" 
    by (auto simp: in_char_class)
  
  lemma l_concatI: "a\<in>L\<^sub>1 \<Longrightarrow> b\<in>L\<^sub>2 \<Longrightarrow> a@b \<in> L\<^sub>1\<cdot>L\<^sub>2"
    unfolding L_concat_def by blast
    
  lemma l_concatConsI: "[x]\<in>L\<^sub>1 \<Longrightarrow> xs\<in>L\<^sub>2 \<Longrightarrow> x#xs \<in> L\<^sub>1\<cdot>L\<^sub>2"
    using l_concatI[of "[x]" _ xs] by simp

  lemma l_star_emptyI[simp]: "[] \<in> L\<^sup>\<star>"  
    apply (subst L_star_unfold)
    by auto
    
  lemma l_char_classE: assumes "s\<in>\<lbrace>C\<rbrace>" obtains c where "s=[c]" "c\<in>C"
    using assms by (auto simp: in_char_class)

  lemma l_concatE: assumes "s\<in>a\<cdot>b" obtains sa sb where "s=sa@sb" "sa\<in>a" "sb\<in>b"
    using assms unfolding L_concat_def by blast
    
    
        
  lemma L_star_unfold_right: "L\<^sup>\<star> = {[]} \<union> L\<^sup>\<star> \<cdot> L"
    (* TODO: Clean up this proof *)
    apply (rule)
    subgoal 
      unfolding L_star_def
      apply clarsimp
      subgoal for xs n
        apply (cases n)
        apply simp
        apply (simp only: L_pow_unfold_left)
        by igr
      done  
    subgoal 
      apply igr'
      using L_pow_simps(1) apply blast
      using L_pow_unfold_left l_concatI by blast
    done  
  
    
  (* TODO: Move *)
  lemma igr_g_char[igr_simps]: "(w,r)\<in>gM_rel <C> \<longleftrightarrow> w=[r] \<and> r\<in>C"
    unfolding g_char_def by simp
    
  (* TODO: Move *)  
  lemmas [igr_simps] = in_char_class
    

  (* TODO: Move *)
  lemma gM_rel_imp_lang: "(w,r)\<in>gM_rel g \<Longrightarrow> w\<in>g_lang g"
    by igr
    
  (* TODO: Move *)
  lemma g_ignore_left_assoc: "a\<ggreater>b\<ggreater>c = a\<ggreater>(b\<ggreater>c)" unfolding g_ignore_left_def by simp
  
  (* TODO: Move *)  
  lemma g_option_ignore_conv: "do {p?; c} = do { (g_return () <|> p \<ggreater> g_return ()); c }"
    unfolding g_option_def g_ignore_left_def 
    by igr  
  
  
  (* TODO: Move *)  
  lemma g_lift2I: 
    assumes "(w\<^sub>1,r\<^sub>1) \<in> gM_rel m\<^sub>1"
    assumes "(w\<^sub>2,r\<^sub>2) \<in> gM_rel m\<^sub>2"
    shows "(w\<^sub>1@w\<^sub>2,f r\<^sub>1 r\<^sub>2) \<in> gM_rel ( g_lift2 f m\<^sub>1 m\<^sub>2 )"  
    using assms unfolding g_ignore_right_def 
    by igr
    
    
section \<open>Proving Unambiguity\<close>

  (* TODO: Move *)
  subsection \<open>Elim-Rules for Grammar\<close>
  lemma gM_emptyE:
    "(s,r)\<in>gM_rel g_empty \<Longrightarrow> P" by igr

  lemma gM_returnE:
    assumes "(s,r)\<in>gM_rel (g_return x)"
    obtains "s=[]" "r=x"
    using assms by igr
    
        
  lemma gM_charE:
    assumes "(s,r)\<in>gM_rel<C>"
    obtains "s=[r]"
    using assms by igr
  
  lemma gM_bindE:
    assumes "(s,r)\<in>gM_rel (do { x\<leftarrow>a; b x})"
    obtains s\<^sub>1 s\<^sub>2 x where "s=s\<^sub>1@s\<^sub>2" "(s\<^sub>1,x)\<in>gM_rel a" "(s\<^sub>2,r)\<in>gM_rel (b x)"
    using assms by igr
      
  lemma gM_lift2E:  
    assumes "(s,r)\<in>gM_rel (g_lift2 f a b)"
    obtains s\<^sub>1 s\<^sub>2 x\<^sub>1 x\<^sub>2 where "s=s\<^sub>1@s\<^sub>2" "(s\<^sub>1,x\<^sub>1)\<in>gM_rel a" "(s\<^sub>2,x\<^sub>2)\<in>gM_rel b" "r = f x\<^sub>1 x\<^sub>2"
    using assms unfolding g_lift2_def
    apply (elim gM_bindE gM_returnE) by blast

  lemma gM_ignore_leftE:  
    assumes "(s,r)\<in>gM_rel (a \<ggreater> b)"
    obtains s\<^sub>1 s\<^sub>2 x where "s=s\<^sub>1@s\<^sub>2" "(s\<^sub>1,x)\<in>gM_rel a" "(s\<^sub>2,r)\<in>gM_rel b"
    using assms unfolding g_ignore_left_def
    apply (elim gM_bindE gM_returnE) by blast
    
  lemma gM_ignore_rightE:  
    assumes "(s,r)\<in>gM_rel (a \<lless> b)"
    obtains s\<^sub>1 s\<^sub>2 x where "s=s\<^sub>1@s\<^sub>2" "(s\<^sub>1,r)\<in>gM_rel a" "(s\<^sub>2,x)\<in>gM_rel b"
    using assms unfolding g_ignore_right_def
    apply (elim gM_bindE gM_returnE) by blast
    
  lemma gM_unionE:
    assumes "(s,r)\<in>gM_rel (a <|> b)"
    obtains "(s,r) \<in> gM_rel a" | "(s,r) \<in> gM_rel b"
    using assms by igr
      
  lemma gM_starE:
    assumes "(s,r)\<in>gM_rel (a *& fi)"
    obtains n where "(s,r)\<in>gM_rel (g_powr a fi n)"
    using assms by igr

  lemma gM_applyE:
    assumes "(s,r)\<in>gM_rel (a <&> f)"  
    obtains r' where "(s,r')\<in>gM_rel a" "r = f r'"
    using assms by igr
      
  
  
  subsection \<open>Unambiguity\<close>

  text \<open>A grammar is unambiguous if its relation is single-valued, i.e.,
    every word is mapped to at most one result\<close>  
  definition "unambiguous g \<longleftrightarrow> single_valued (gM_rel g)"

  
  
  
  subsection \<open>Uniqueness\<close>
  definition "L_uniq L R \<equiv> \<forall>s\<^sub>1 s\<^sub>2 s\<^sub>1' s\<^sub>2'. s\<^sub>1@s\<^sub>2 = s\<^sub>1'@s\<^sub>2' \<and> s\<^sub>1\<in>L \<and> s\<^sub>2\<in>R \<and> s\<^sub>1'\<in>L \<and> s\<^sub>2'\<in>R \<longrightarrow> s\<^sub>1=s\<^sub>1'"

  definition "g_uniq L C \<equiv> \<forall>s\<^sub>1 r\<^sub>1 s\<^sub>2 s\<^sub>1' r\<^sub>1' s\<^sub>2'. 
    s\<^sub>1@s\<^sub>2 = s\<^sub>1'@s\<^sub>2' \<and> (s\<^sub>1,r\<^sub>1)\<in>gM_rel L \<and> s\<^sub>2\<in>C \<and> (s\<^sub>1',r\<^sub>1')\<in>gM_rel L \<and> s\<^sub>2'\<in>C \<longrightarrow> s\<^sub>1=s\<^sub>1' \<and> r\<^sub>1=r\<^sub>1'"
    
  (*definition "g_uniq L C \<equiv> \<forall>s\<^sub>1 r\<^sub>1 s\<^sub>2 s\<^sub>1' r\<^sub>1' s\<^sub>2'. 
    s\<^sub>1@s\<^sub>2 = s\<^sub>1'@s\<^sub>2' \<and> (s\<^sub>1,r\<^sub>1)\<in>gM_rel L \<and> s\<^sub>2\<in>C \<and> (s\<^sub>1',r\<^sub>1')\<in>gM_rel L \<and> s\<^sub>2'\<in>C \<longrightarrow> s\<^sub>1=s\<^sub>1' \<and> r\<^sub>1=r\<^sub>1'"
  *)
          
  lemma g_uniqI[intro?]: 
    assumes "\<And>s\<^sub>1 r\<^sub>1 s\<^sub>2 s\<^sub>1' r\<^sub>1' s\<^sub>2'. \<lbrakk> s\<^sub>1@s\<^sub>2 = s\<^sub>1'@s\<^sub>2'; (s\<^sub>1,r\<^sub>1)\<in>gM_rel L; s\<^sub>2\<in>C; (s\<^sub>1',r\<^sub>1')\<in>gM_rel L; s\<^sub>2'\<in>C\<rbrakk> \<Longrightarrow> s\<^sub>1=s\<^sub>1' \<and> r\<^sub>1=r\<^sub>1'"
    shows "g_uniq L C"
    using assms unfolding g_uniq_def by blast

  lemma g_uniqD:
    assumes "g_uniq L C"
    assumes "s\<^sub>1@s\<^sub>2 = s\<^sub>1'@s\<^sub>2'" 
    assumes "(s\<^sub>1,r\<^sub>1)\<in>gM_rel L" "s\<^sub>2\<in>C" 
    assumes "(s\<^sub>1',r\<^sub>1')\<in>gM_rel L" "s\<^sub>2'\<in>C"  
    shows "s\<^sub>1=s\<^sub>1'" "s\<^sub>2=s\<^sub>2'" "r\<^sub>1=r\<^sub>1'"
    using assms unfolding g_uniq_def by blast+
    
  lemma g_uniqE:
    assumes "g_uniq L C"
    assumes "s\<^sub>1@s\<^sub>2 = s\<^sub>1'@s\<^sub>2'" 
    assumes "(s\<^sub>1,r\<^sub>1)\<in>gM_rel L" "s\<^sub>2\<in>C" 
    assumes "(s\<^sub>1',r\<^sub>1')\<in>gM_rel L" "s\<^sub>2'\<in>C"  
    obtains "s\<^sub>1=s\<^sub>1'" "s\<^sub>2=s\<^sub>2'" "r\<^sub>1=r\<^sub>1'"
    using assms unfolding g_uniq_def by blast+
        
  lemma unambiguous_eq_uniq: "unambiguous g \<longleftrightarrow> g_uniq g {[]}"  
    unfolding unambiguous_def g_uniq_def single_valued_def
    by igr
    
  named_theorems g_uniq_intros  
    
  lemma g_uniq_returnI[simp,g_uniq_intros]: "g_uniq (g_return x) C"  
    unfolding g_uniq_def by igr
    
  lemma g_uniq_bindI[g_uniq_intros]:
    fixes a :: "('c,'a) gM" and b :: "'a \<Rightarrow> ('c,'b) gM"
    assumes BL_INDEP: "\<And>x. g_lang (b x) = g_lang (b undefined)"
    assumes U1: "\<And>x. g_uniq a (g_lang (b x)\<cdot>C)"
    assumes U2: "\<And>x. g_uniq (b x) C"
    shows "g_uniq (do {x\<leftarrow>a; b x}) C"  
    apply (rule g_uniqI)
    apply (elim gM_bindE; clarsimp)
  proof goal_cases
    case (1 r\<^sub>1 s\<^sub>3 r\<^sub>1' s\<^sub>3' s\<^sub>1 s\<^sub>2 x s\<^sub>1' s\<^sub>2' x')
    
    from 1 have 
           C12: "s\<^sub>2 @ s\<^sub>3 \<in> g_lang (b x) \<cdot> C" 
      and C12': "s\<^sub>2' @ s\<^sub>3' \<in> g_lang (b x') \<cdot> C"
      by igr+
    
    from g_uniqD[OF U1 \<open>s\<^sub>1@_@_=_\<close> \<open>(s\<^sub>1,_)\<in>_\<close> C12 \<open>(s\<^sub>1',_)\<in>_\<close>] C12'
    have [simp]: "s\<^sub>1=s\<^sub>1'" "x=x'"
      by (simp_all add: BL_INDEP[of x] BL_INDEP[of x'])
    
    from \<open>s\<^sub>1 @ s\<^sub>2 @ s\<^sub>3 = s\<^sub>1' @ s\<^sub>2' @ s\<^sub>3'\<close> have "s\<^sub>2 @ s\<^sub>3 = s\<^sub>2' @ s\<^sub>3'" by simp
    
    from \<open>(s\<^sub>2, _) \<in> gM_rel (b _)\<close> have S2: "(s\<^sub>2, r\<^sub>1) \<in> gM_rel (b x')" by simp
    
    from g_uniqD[OF U2 \<open>s\<^sub>2@_ = _\<close> S2 \<open>s\<^sub>3\<in>C\<close> \<open>(s\<^sub>2', _) \<in> gM_rel (b x')\<close> \<open>s\<^sub>3'\<in>C\<close>] 
    have [simp]: "s\<^sub>2 = s\<^sub>2'" "r\<^sub>1 = r\<^sub>1'" by auto
    
    show ?case by simp
  qed  

  
  
  lemma g_uniq_lift2I[g_uniq_intros]:
    fixes a :: "('c,'a) gM" and b :: "('c,'b) gM"
    assumes U1: "g_uniq a (g_lang b\<cdot>C)"
    assumes U2: "g_uniq b C"
    shows "g_uniq (g_lift2 f a b) C"  
    unfolding g_lift2_def
    apply (intro g_uniq_bindI)
    apply (subst g_lang_simps | intro gl_indep_intros refl)+
    
    apply (simp add: U1)
    apply (simp add: g_lang_simps)
    apply (simp add: g_lang_simps U2)

    apply simp
    done
    
  
  lemma L_conc_combine_aux:
    assumes "a@b=a'@b'" "a\<in>A" "b\<in>B" "a'\<in>A'" "b'\<in>B'"
    obtains "a'@b'\<in>A\<cdot>B" "a'@b'\<in>A'\<cdot>B'"
    using assms by igr_fastforce
  
  
  lemma g_uniq_unionI[g_uniq_intros]:
    assumes UA: "g_uniq a C"
    assumes UB: "g_uniq b C"
    assumes DJ: "g_lang a \<cdot> C \<inter> g_lang b \<cdot> C = {}"
    shows "g_uniq (a <|> b) C"
    apply (rule g_uniqI)
    apply (elim gM_unionE)
    
    subgoal by (blast dest: g_uniqD[OF UA])
    subgoal
      using DJ 
    
     using disjointD[OF DJ]  by igr
    subgoal using disjointD[OF DJ] by igr
    subgoal by (blast dest: g_uniqD[OF UB])
    done
    
    
  (* TODO: Move *)  
  lemma g_uniq_antimono2: "g_uniq a C \<Longrightarrow> C'\<subseteq>C \<Longrightarrow> g_uniq a C'"
    unfolding g_uniq_def
    by blast

  (* TODO: Move *)  
  lemma L_starI: "w \<in> L_pow L n \<Longrightarrow> w\<in>L\<^sup>\<star>" by igr
    
  lemma g_uniq_starrI[g_uniq_intros]:
    assumes aC_dj: "g_lang a \<cdot> (g_lang a)\<^sup>\<star> \<cdot> C \<inter> C = {}"
    assumes UA: "g_uniq a ((g_lang a)\<^sup>\<star>\<cdot>C)"
    shows "g_uniq (a *& fi) C"
    apply (rule)
    apply (clarsimp simp: igr_starr)
  proof goal_cases
    case (1 s\<^sub>1 r\<^sub>1 s\<^sub>2 s\<^sub>1' r\<^sub>1' s\<^sub>2' n n')
    
    from disjointD[OF aC_dj] 
    have aC_dj_aux: "x\<in>C \<Longrightarrow> x\<in>g_lang a \<cdot> g_lang a\<^sup>\<star> \<cdot> C \<Longrightarrow> thesis" for x thesis 
    by blast
    
    from 1 show ?case
    proof (induction n n' arbitrary: s\<^sub>1 r\<^sub>1 s\<^sub>2 s\<^sub>1' r\<^sub>1' s\<^sub>2' rule : nat2ss_induct.induct)
      case 1
      then show ?case by (auto elim: gM_returnE gM_lift2E)
    next
      case (2 v)
      then show ?case
      apply (clarsimp elim!: gM_returnE gM_lift2E)
      apply ((drule gM_rel_imp_lang)+; simp add: g_lang_simps)
      apply (drule L_starI)
      apply (erule aC_dj_aux)
      by igr_force
    next
      case (3 v)
      then show ?case 
      apply (clarsimp elim!: gM_returnE gM_lift2E)
      apply ((drule gM_rel_imp_lang)+; simp add: g_lang_simps)
      apply (drule L_starI)
      apply (erule aC_dj_aux[of "_@_@_"])
      by igr_force
    next
      case (4 n\<^sub>1 n\<^sub>2)
      
      from "4.prems"
      show ?case 
        apply (clarsimp elim!: gM_returnE gM_lift2E)
        apply (erule g_uniqE[OF UA]; assumption?)
        apply ((drule gM_rel_imp_lang)+; simp add: g_lang_simps) apply igr
        apply ((drule gM_rel_imp_lang)+; simp add: g_lang_simps) apply igr
        
        apply clarsimp
        
        apply (drule (4) "4.IH")
        by simp
    qed
  qed            
    
  lemma g_uniq_applyI[g_uniq_intros]: "g_uniq g C \<Longrightarrow> g_uniq (g<&>f) C"
    apply rule
    apply igr_simp
    apply (blast dest: g_uniqD)
    done
    
  lemma g_uniq_charI[g_uniq_intros]: "g_uniq <cs> C"
    unfolding g_uniq_def
    by igr'
  
  subsection \<open>Empty, Has-Empty and Lookahead\<close>
  text \<open>Some simp-lemmas to semi-automatically decide if the language
    is empty, contains the empty word, and to compute the lookahead-1 set\<close>
  definition "is_el L \<equiv> L={}"  
  definition "has_eps L \<equiv> []\<in>L"  
  definition "lh1 l \<equiv> { x | x xs. x#xs\<in>l }"
  
  lemma eq_empty_elem_conv: "a={} \<longleftrightarrow> (\<forall>x. x\<notin>a)" by simp

  
  lemma lh1_disjI:
    assumes "\<lbrakk> \<not>is_el L\<^sub>1; \<not>is_el L\<^sub>2 \<rbrakk> \<Longrightarrow> \<not>(has_eps L\<^sub>1 \<and> has_eps L\<^sub>2)" 
    assumes "\<lbrakk> \<not>is_el L\<^sub>1; \<not>is_el L\<^sub>2 \<rbrakk> \<Longrightarrow> lh1 L\<^sub>1 \<inter> lh1 L\<^sub>2 = {}"
    shows "L\<^sub>1 \<inter> L\<^sub>2 = {}"
    apply (clarsimp simp: disjoint_iff)
    subgoal for xs
      using assms unfolding is_el_def has_eps_def lh1_def
      apply (cases xs)
      by auto
    done
  
  lemma g_uniq_empty[simp]: "g_uniq g {}" unfolding g_uniq_def by blast
  lemma g_uniq_empty'[simp]: "is_el C \<Longrightarrow> g_uniq g C" unfolding is_el_def by simp
  
  
  
  subsubsection "Empty Language"
  lemma is_el_empty[simp]: "is_el {}"  
    unfolding is_el_def by blast
  
  lemma has_eps_emp[simp]: "\<not>has_eps {}"
    unfolding has_eps_def by auto

  lemma lh1_el[simp]: "lh1 {} = {}"
    unfolding lh1_def by blast
    
    
    
  subsubsection \<open>Language with empty word\<close>      

  lemma is_el_insert[simp]: "\<not>is_el (insert x s)"
    unfolding is_el_def by blast
  
  lemma has_eps_eps[simp]: "has_eps {[]}"
    unfolding has_eps_def by auto
    
  (* lemma lh1_eps[simp]: "lh1 {[]} = {}" unfolding lh1_def by auto  *)

  lemma lh1_ins_Nil[simp]: "lh1 (insert [] L) = lh1 L"
    unfolding lh1_def by blast
  
  
  subsubsection \<open>Character\<close>  
  lemma is_el_char_class[simp]: "is_el \<lbrace>C\<rbrace> \<longleftrightarrow> C={}"
    unfolding is_el_def eq_empty_elem_conv by igr'
        
  lemma has_eps_char[simp]: "\<not>has_eps \<lbrace>C\<rbrace>"  
    unfolding has_eps_def by igr

  lemma lh1_char[simp]: "lh1 \<lbrace>C\<rbrace> = C"
    unfolding lh1_def by igr
    
        
  subsubsection \<open>Concat\<close>  
      
  lemma is_el_concat[simp]: "is_el (L\<^sub>1\<cdot>L\<^sub>2) \<longleftrightarrow> is_el L\<^sub>1 \<or> is_el L\<^sub>2"
    unfolding is_el_def eq_empty_elem_conv by igr'

  lemma has_eps_concat[simp]: "has_eps (L\<^sub>1\<cdot>L\<^sub>2) \<longleftrightarrow> has_eps L\<^sub>1 \<and> has_eps L\<^sub>2"
    unfolding has_eps_def by igr

  lemma lh1_concat_iff[simp]: "\<not>is_el L\<^sub>2 \<Longrightarrow> lh1 (L\<^sub>1\<cdot>L\<^sub>2) = lh1 L\<^sub>1 \<union> (if has_eps L\<^sub>1 then lh1 L\<^sub>2 else {})"
    unfolding lh1_def is_el_def has_eps_def
    supply [simp] = Cons_eq_append_conv
    by (igr'; blast)
    
        
  subsubsection \<open>Union\<close>  
      
  lemma is_el_union[simp]: "is_el (L\<^sub>1\<union>L\<^sub>2) \<longleftrightarrow> is_el L\<^sub>1 \<and> is_el L\<^sub>2"  
    unfolding is_el_def by blast
    
  lemma has_eps_union[simp]: 
    "has_eps (L\<^sub>1\<union>L\<^sub>2) \<longleftrightarrow> has_eps L\<^sub>1 \<or> has_eps L\<^sub>2"  
    "has_eps (insert x L) \<longleftrightarrow> x=[] \<or> has_eps L"
    unfolding has_eps_def by igr+

  lemma lh1_union[simp]: "lh1 (a\<union>b) = lh1 a \<union> lh1 b"  
    unfolding lh1_def by igr
    
  subsubsection \<open>Optional\<close>  
    
  lemma is_el_opt[simp]: "\<not>is_el (L\<^sup>?)" unfolding L_opt_def by simp
  
  lemma has_eps_opt[simp]: "has_eps (L\<^sup>?)" unfolding L_opt_def by simp 
    
  lemma lh1_opt[simp]: "lh1 (L\<^sup>?) = lh1 L" unfolding lh1_def by igr
    
  subsection \<open>Power\<close>
  lemma is_el_pow[simp]: "is_el (L_pow L n) = (n\<noteq>0 \<and> is_el L)"  
    apply (induction n)
    by auto

  lemma has_eps_pow[simp]: "has_eps (L_pow L n) = (n=0 \<or> has_eps L)"  
    apply (induction n)
    by auto

  lemma lh1_pow[simp]: "lh1 (L_pow L n) = (if n=0 then {} else lh1 L)"
    apply (cases "is_el L")
    subgoal
      unfolding is_el_def
      by (induction n) auto
    subgoal
      apply (induction n)
      apply simp
      apply (simp split: if_splits)
      done
    done
    
          
  subsubsection \<open>Star\<close>  
            
  lemma is_el_star[simp]: "\<not>is_el (a\<^sup>\<star>)" 
    unfolding is_el_def using l_star_emptyI by blast

  lemma has_eps_star[simp]: "has_eps (L\<^sup>\<star>)"
    apply (subst L_star_unfold) by simp
        
  lemma lh1_star[simp]: "lh1 (L\<^sup>\<star>) = lh1 L"  
    unfolding lh1_def
    apply igr_simp
    apply safe
    subgoal for x xs n
      apply (induction n) (* Induction required to handle possibility of has_eps L *)
      apply igr
      apply simp
      apply igr_simp
      by (auto simp add: Cons_eq_append_conv) 
    subgoal for x xs
      by (auto intro!: exI[where x=1])
    done
    

    
subsection "Set of Characters in Language"    
  abbreviation "l_charset l \<equiv> \<Union> (set ` l)"
  abbreviation "l_charset_must l \<equiv> \<Inter> (set ` l)"
  
    
  lemma L_disj_charset_must_mayI:
    assumes "\<not>(l_charset_must A \<subseteq> l_charset B)"
    shows "A \<inter> B = {}"
    using assms
    by blast

  
  
  
      
  lemma l_charset_concat[simp]: "\<lbrakk> \<not>is_el L\<^sub>1; \<not>is_el L\<^sub>2 \<rbrakk> \<Longrightarrow> l_charset (L\<^sub>1\<cdot>L\<^sub>2) = l_charset L\<^sub>1 \<union> l_charset L\<^sub>2"
    unfolding is_el_def
    supply [simp] = Bex_def
    by igr_force 

  lemma l_charset_must_concat[simp]: "l_charset_must (A\<cdot>B) = l_charset_must A \<union> l_charset_must B"
    unfolding L_concat_def
    by fastforce
        
         
  lemma l_charset_char[simp]: "l_charset \<lbrace>C\<rbrace> = C"  
    supply [simp] = Bex_def
    by igr_force
    
  lemma l_charset_must_multiple_char[simp]: "card C > 1 \<Longrightarrow> l_charset_must \<lbrace>C\<rbrace> = {}"  
    unfolding char_class_def
    apply auto
    by (metis Suc_lessD card_ge_0_finite card_le_Suc0_iff_eq linorder_not_less list.set(1) list.set(2) singletonD)
    
  lemma l_charset_must_sng_char[simp]: "l_charset_must \<lbrace>{c}\<rbrace> = {c}"  
    by igr'
    
  
  lemma l_charset_opt[simp]: "l_charset (L\<^sup>?) = l_charset L"  
    supply [simp] = Bex_def
    by igr_force

  lemma l_charset_must_opt[simp]: "l_charset_must (L\<^sup>?) = {}"  
    supply [simp] = Bex_def
    by igr_force

        
  lemma Union_nat_split: "\<Union>{ f n | n::nat. True} = f 0 \<union> (\<Union>{ f (Suc n) | n::nat. True})"  
    apply (auto)
    by (metis old.nat.exhaust)
    
    
    
  lemma l_charset_star[simp]:
    assumes [simp]: "\<not>is_el L"
    shows "l_charset (L\<^sup>\<star>) = l_charset L"      
  proof -
    have 1: "l_charset (L_pow L (Suc n)) = l_charset L" for n
      apply (induction n)
      apply simp
      apply simp
      done
      
    have 2: "(l_charset (L_pow L 0)) = {}" by simp
    
    have "l_charset (L\<^sup>\<star>) = \<Union> {l_charset (L_pow L n) | n. True }"
      supply [simp] = Bex_def
      by (igr'; blast)
    also have "\<dots> = (l_charset (L_pow L 0)) \<union> (\<Union> {l_charset (L_pow L (Suc n)) | n. True })"  
      by (rule Union_nat_split)
    also have "\<dots> = l_charset L" using 1 2 by simp
    finally show ?thesis  .
  qed
    
  lemma l_charset_must_star[simp]: "l_charset_must (A\<^sup>\<star>) = {}"
    using l_star_emptyI by fastforce
    
  
subsection \<open>Unit-Grammars\<close>    
  definition "mk_unit g \<equiv> g <&> (\<lambda>_. ())"
  
  lemma g_ignore_right_lift2: "a\<lless>b = g_lift2 (\<lambda>x _. x) a (mk_unit b)" unfolding g_ignore_right_def mk_unit_def by igr   
  lemma g_ignore_left_lift2: "a\<ggreater>b = g_lift2 (\<lambda>_ x. x) (mk_unit a) b" unfolding g_ignore_left_def mk_unit_def by igr   
    
  lemma g_lang_mk_unit[g_lang_simps]: "g_lang (mk_unit g) = g_lang g" unfolding mk_unit_def by (simp add: g_lang_simps)

  lemma g_uniq_mk_unitI: "g_uniq g C \<Longrightarrow> g_uniq (mk_unit g) C" (* Incomplete! *)
    unfolding mk_unit_def
    apply rule
    apply igr'
    by (blast dest: g_uniqD)
  
end  





(* Proving Kleene Algebra 
  (from Wikipedia):
    A Kleene algebra is a set A together with two binary operations + : A \<times> A \<rightarrow> A and \<sqdot> : A \<times> A \<rightarrow> A and one function * : A \<rightarrow> A, written as a + b, ab and a* respectively, so that the following axioms are satisfied.
    
    Associativity of + and \<sqdot>: a + (b + c) = (a + b) + c and a(bc) = (ab)c for all a, b, c in A.
    Commutativity of +: a + b = b + a for all a, b in A
    Distributivity: a(b + c) = (ab) + (ac) and (b + c)a = (ba) + (ca) for all a, b, c in A
    Identity elements for + and \<sqdot>: There exists an element 0 in A such that for all a in A: a + 0 = 0 + a = a. There exists an element 1 in A such that for all a in A: a1 = 1a = a.
    Annihilation by 0: a0 = 0a = 0 for all a in A.
    The above axioms define a semiring. We further require:
    
    + is idempotent: a + a = a for all a in A.
    It is now possible to define a partial order \<le> on A by setting a \<le> b if and only if a + b = b (or equivalently: a \<le> b if and only if there exists an x in A such that a + x = b; with any definition, a \<le> b \<le> a implies a = b). With this order we can formulate the last four axioms about the operation *:
    
    1 + a( a* ) \<le> a* for all a in A.
    1 + ( a* )a \<le> a* for all a in A.
    if a and x are in A such that ax \<le> x, then a*x \<le> x
    if a and x are in A such that xa \<le> x, then x( a* ) \<le> x [3]
*)

experiment begin
  context begin interpretation lang_syntax .
    lemma assoc: 
      "(a \<union> b) \<union> c = a \<union> (b \<union> c)"
      "(a \<cdot> b) \<cdot> c = a \<cdot> (b \<cdot> c)"
      by auto
    
    lemma comm: "a\<union>b = b \<union> a" by auto
    
    lemma dist: 
      "a\<cdot>(b\<union>c) = a\<cdot>b \<union> a\<cdot>c" 
      "(a\<union>b)\<cdot>c = a\<cdot> c \<union> b\<cdot>c"
      by igr_fastforce+
    
    lemma identity: 
      "{[]} \<cdot> a = a"    
      "a \<cdot> {[]} = a"    
      "a \<union> {} = a"
      by auto

    lemma annihilation: "{}\<cdot>L = {}" "L\<cdot>{}={}" by auto
    
    lemma idem: "a\<union>a = a" by auto
    
    lemma "a\<subseteq>b \<longleftrightarrow> a\<union>b = b" by blast
    
    lemma star_unfoldl: "{[]} \<union> a\<cdot>a\<^sup>\<star> \<subseteq> a\<^sup>\<star>"
      supply [intro] = exI[where x=0] exI[where x="Suc _"]
      by igr_fastforce
      
    lemma star_unfoldr: "{[]} \<union> a\<^sup>\<star>\<cdot>a \<subseteq> a\<^sup>\<star>"
      supply [intro] = exI[where x=0] exI[where x="Suc _"]
      supply [simp] = L_pow_unfold_left and [simp del] = L_pow_simps(2)
      by igr_fastforce
      
    lemma star_inductl: "a\<cdot>x \<subseteq> x \<Longrightarrow> a\<^sup>\<star>\<cdot>x \<subseteq> x"  
    proof -
      assume A: "a\<cdot>x \<subseteq> x"
      have "L_pow a n \<cdot> x \<subseteq> x" for n
        apply (induction n)
        apply simp
        apply simp
        by (metis A L_concat_mono L_concat_simps(5) equalityD1 subset_trans)
      thus ?thesis using A
        apply igr'
        using l_concatI by blast
    qed
    
    lemma star_inductr: "x\<cdot>a \<subseteq> x \<Longrightarrow> x\<cdot>a\<^sup>\<star> \<subseteq> x"  
    proof -
      assume A: "x\<cdot>a \<subseteq> x"
      have "x \<cdot> L_pow a n \<subseteq> x" for n
        apply (induction n)
        apply simp
        apply simp
        by (metis A L_concat_mono L_concat_simps(5) equalityD1 subset_trans)
      thus ?thesis using A
        apply igr'
        using l_concatI by blast
    qed
      
  end
end








end
