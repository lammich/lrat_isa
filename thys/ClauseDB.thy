section \<open>Clause Database\<close>
theory ClauseDB
imports Unsigned_Literal Nat_Array_Dfun Proto_Sepref_Ghostvar
begin


  method_setup sepref_dbg_trans_step1_normgoal 
    = \<open>Scan.succeed (SIMPLE_METHOD' o Sepref_Frame.norm_goal_pre_tac)\<close>

  method_setup sepref_dbg_trans_step2_aligngoal 
    = \<open>Scan.succeed (SIMPLE_METHOD' o Sepref_Frame.align_goal_tac)\<close>

  method_setup sepref_dbg_trans_step3_recover_pure_frame 
    = \<open>Scan.succeed (SIMPLE_METHOD' o (fn ctxt => resolve_tac ctxt @{thms trans_frame_rule}))\<close>
    
  method_setup sepref_dbg_trans_step4_recover_pure 
    = \<open>Scan.succeed (SIMPLE_METHOD' o Sepref_Frame.recover_pure_tac)\<close>
  
  (* TODO: Make this visible! It's currently locally hidden as fr_rl_tac    
  method_setup sepref_dbg_trans_step5_rule_tac 
    = \<open>Scan.succeed (SIMPLE_METHOD' o Sepref_Translate.fr_rl_tac)\<close>
  *)
    
      



  (* TODO: Move *)
  lemma takeWhile_eq_all_conv'[simp]:
    "(xs = takeWhile P xs) = (\<forall>x \<in> set xs. P x)"
    by(induct xs, auto)


    
  subsection "Terminated List Segment" 

  context
    fixes trm :: "'a"
  begin
  
    definition "zseg_at xs i \<equiv> (takeWhile ((\<noteq>)trm) (drop i xs))"
    
    definition "zseg_is_term xs i \<equiv> \<exists>j<length xs. i\<le>j \<and> xs!j=trm"
  
    lemma zseg_at_overflow[simp]: "length xs \<le> i \<Longrightarrow> zseg_at xs i = []"
      unfolding zseg_at_def by auto
  
      
    lemma zseg_is_term_append: "zseg_is_term xs i \<Longrightarrow> zseg_is_term (xs@xs') i"
      unfolding zseg_at_def zseg_is_term_def
      by (auto simp: nth_append)
      
    lemma id_take_nth_dropD: "xs!i=x \<Longrightarrow> i<length xs \<Longrightarrow> \<exists>xs\<^sub>1 xs\<^sub>2. length xs\<^sub>1 = i \<and> xs=xs\<^sub>1@x#xs\<^sub>2"
      using id_take_nth_drop by force
      
    lemma zseg_append_t: 
      assumes "zseg_is_term xs i"  
      shows "zseg_at (xs@xs') i = zseg_at xs i"
    proof -
      from assms obtain xs\<^sub>1 xs\<^sub>2 where 1: "drop i xs = xs\<^sub>1@trm#xs\<^sub>2"
        unfolding zseg_is_term_def
        apply clarsimp 
        by (metis Cons_nth_drop_Suc drop_take_drop_unsplit)
      
      show ?thesis
        unfolding zseg_at_def
        by (simp add: 1 takeWhile_tail)
        
    qed  
  
    lemma zseg_is_term_alt: "zseg_is_term xs i \<longleftrightarrow> trm \<in> set (drop i xs)"
      unfolding zseg_is_term_def 
      apply (clarsimp simp: in_set_conv_nth) 
      apply (rule; clarsimp)
      apply (metis le_add_diff_inverse le_add_diff_inverse2 less_diff_conv)
      by (metis add.commute le_add1 less_diff_conv)
    
    lemma zseg_append_nt:
      "\<not>zseg_is_term xs i \<Longrightarrow> zseg_at (xs@xs') i = zseg_at xs i @ zseg_at xs' (i-length xs)"
      unfolding zseg_at_def
      by (auto simp: zseg_is_term_alt takeWhile_append)
    
    lemma zseg_append: "zseg_at (xs@xs') i = (if zseg_is_term xs i then zseg_at xs i else zseg_at xs i @ zseg_at xs' (i-length xs))"
      using zseg_append_t zseg_append_nt by auto          
    
    lemma zseg_is_term_drop[simp]: "zseg_is_term (drop i db) i' = zseg_is_term db (i+i')"
      unfolding zseg_is_term_def 
      apply auto
      subgoal by (metis add.commute less_diff_conv nat_add_left_cancel_le) 
      subgoal by (metis add.commute add_leD1 add_le_imp_le_diff diff_less_mono ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
      done
  
    lemma zseg_at_drop[simp]: "zseg_at (drop i db) i' = zseg_at db (i+i')"
      unfolding zseg_at_def 
      by (auto simp: algebra_simps)
          
    lemma zseg_eq_Nil_conv: "zseg_at xs i = [] \<longleftrightarrow> (i<length xs \<longrightarrow> xs!i=trm)"
      unfolding zseg_at_def
      by (auto simp: takeWhile_eq_Nil_iff hd_drop_conv_nth intro: leI)
    
  
    lemma zseg_subset: "set (zseg_at xs i) \<subseteq> set xs"
      unfolding zseg_at_def apply clarsimp
      by (meson in_set_dropD set_takeWhileD)  
  
    lemma zseg_nZ[simp]: "trm\<notin>set (zseg_at xs i)"  
      unfolding zseg_at_def apply clarsimp
      by (auto dest: set_takeWhileD)
      
          
    
    definition "zdom f \<equiv> {x. f x \<noteq> trm}"
    definition "zran f \<equiv> f`UNIV - {trm}"
  
    lemma zdom_empty[simp]: "zdom (\<lambda>_. trm) = {}" unfolding zdom_def by auto
    lemma zran_empty[simp]: "zran (\<lambda>_. trm) = {}" unfolding zran_def by auto
      
              
    subsubsection \<open>Iterating over Zseg\<close>
    
    definition "zseg_fold xs i c f s \<equiv> do {
      (_,_,s)\<leftarrow>WHILET 
        (\<lambda>(brk,i,s). \<not>brk \<and> c s) 
        (\<lambda>(brk,i,s). do {
          x\<leftarrow>mop_list_get xs i;
          if x=trm then RETURN (True,i,s)
          else do {
            s\<leftarrow>f x s;
            ASSERT(i<length xs);
            RETURN (False,i+1,s)
          }
        })
        (False,i,s);
        RETURN s
      }"
    
      
    lemma zseg_fold_unfold: "zseg_fold xs i c f s = do {
      if c s then do {
        x\<leftarrow>mop_list_get xs i;
        if x=trm then RETURN s
        else do {
          s\<leftarrow>f x s;
          ASSERT(i<length xs);
          zseg_fold xs (i+1) c f s
        }
      } else RETURN s
    }"
      apply (rewrite in "\<hole> = _" zseg_fold_def)
      apply (subst WHILET_unfold) 
      apply (cases "i<length xs"; simp)
      apply (intro conjI impI)
      subgoal
        apply (subst WHILET_unfold) 
        by simp
      subgoal
        unfolding zseg_fold_def
        by simp
      done
      
      
    lemma zseg_is_term_imp_len_lt: "zseg_is_term xs i \<Longrightarrow> i<length xs"
      unfolding zseg_is_term_def by auto  
    
    lemma zseg_is_term_step: "zseg_is_term xs i \<Longrightarrow> xs!i\<noteq>trm \<Longrightarrow> zseg_is_term xs (Suc i)"
      unfolding zseg_is_term_def
      by (metis le_less_Suc_eq linorder_not_le)  
      
    lemma zseg_at_unfold: "zseg_is_term xs i \<Longrightarrow> zseg_at xs i = (if xs!i=trm then [] else (xs!i) # zseg_at xs (Suc i))"  
      unfolding zseg_at_def zseg_is_term_def
      by (auto simp: drop_Suc_nth)
      
    lemma zseg_fold_refine:
      assumes T: "zseg_is_term xs i"
      shows "zseg_fold xs i c f s \<le> nfoldli (zseg_at xs i) c f s "
    proof -
      from T have "i\<le>length xs" by (auto dest: zseg_is_term_imp_len_lt)
      then show ?thesis using T proof (induction i arbitrary: s rule: inc_induct)
        case base
        then show ?case by (auto dest: zseg_is_term_imp_len_lt)
      next
        case (step ii)
        
        from step.prems show ?case
          apply (subst zseg_at_unfold, simp)
          apply (subst zseg_fold_unfold, simp)
          apply (clarsimp simp: zseg_is_term_imp_len_lt)
          apply (rule bind_mono(1)[OF order_refl step.IH])              
          apply (simp add: zseg_is_term_step)
          done        
        
      qed
    qed
  end    

          
  subsection \<open>Clause DB Definitions\<close>  
    
  subsubsection \<open>Invariant and Abstraction Function\<close>  
  text \<open>maxlit \<times> db \<times> cid_map \<times> bound\<close>  
  type_synonym clause_db_list = "dimacs_var literal option list"
  type_synonym clause_db = "nat \<times> clause_db_list \<times> (nat \<Rightarrow> nat) \<times> nat"
  
  definition cdb_invar :: "clause_db \<Rightarrow> bool" where "cdb_invar \<equiv> \<lambda>(ml,db,cm,bnd). 
    (\<forall>i\<in>zran 0 cm. zseg_is_term None db i)
  \<and> (0<length db \<and> length db\<le>bnd \<and> db!0 = None)
  \<and> (\<forall>l. Some l\<in>set db \<longrightarrow> ulit_of l\<le>ml)
  "
  
  text \<open>The clause database represents a CNF formula composed of all clauses that are assigned an ID.
    Also, there is a last clause that is currently being built.
    
    Moreover, it has a set of literals that corresponds to both, the last clause and the CNF.
    
    Finally, there is a capacity bound, which is used to bound the capacity and do overflow 
    reasoning in later refinement steps.
  \<close>
  

  text \<open>Internal: clause at index\<close>  
  definition cdb_internal_clause_at :: "clause_db_list \<Rightarrow> nat \<Rightarrow> dimacs_var clause" where 
    "cdb_internal_clause_at \<equiv> \<lambda>db i. (set (map the (zseg_at None db i)))"

  text \<open>CNF made up of all registered clauses\<close>    
  definition cdb_\<alpha> :: "clause_db \<Rightarrow> dimacs_var cnf" where 
    "cdb_\<alpha> \<equiv> \<lambda>(ml,db,cm,bnd). cdb_internal_clause_at db ` zran 0 cm"

  text \<open>All literals, in registered and built clause\<close>  
  definition cdb_lits :: "clause_db \<Rightarrow> dimacs_var literal set" where 
    "cdb_lits \<equiv> \<lambda>(_,db,_,_). { l | l. Some l \<in> set db}"

  text \<open>Capacity\<close>  
  definition cdb_cap :: "clause_db \<Rightarrow> nat" where
    "cdb_cap \<equiv> \<lambda>(_,db,_,bnd). bnd-length db"  
  
  text \<open>Current clause being built at given index\<close>  
  definition cdb_last :: "clause_db \<Rightarrow> nat \<Rightarrow> clause_db_list" where "cdb_last \<equiv> \<lambda>(_,db,_,_) i. drop i db"
  
  text \<open>Valid clause index\<close>
  definition cdb_idx_valid :: "clause_db \<Rightarrow> nat \<Rightarrow> bool" where "cdb_idx_valid \<equiv> \<lambda>(_,db,_,_) i. 0<i \<and> i\<le>length db"

  text \<open>DB length\<close>
  definition cdb_db_len :: "clause_db \<Rightarrow> nat" where "cdb_db_len \<equiv> \<lambda>(_,db,_,_). length db"
  
  
  lemma cdb_clause_at_finite[simp,intro!]: "finite (cdb_internal_clause_at cdb cid)"
    unfolding cdb_internal_clause_at_def by (auto split: prod.split)

    
  lemma zseg_nZ_ulito:
    assumes "l\<in>set (zseg_at None db i)"  
    shows "\<not>is_None l"  
    using assms zseg_nZ
    by fastforce
    
  lemma cdb_\<alpha>_lits: "cdb_invar cdb \<Longrightarrow> l\<in>C \<Longrightarrow> C\<in>cdb_\<alpha> cdb \<Longrightarrow> l\<in>cdb_lits cdb"  
    unfolding cdb_invar_def cdb_\<alpha>_def cdb_lits_def cdb_internal_clause_at_def
    apply clarsimp
    using zseg_subset zseg_nZ_ulito ulito_the_def by fastforce
    
    
        
  subsection \<open>Operations\<close>  

  definition cdb_make :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> clause_db" where [simp]: "cdb_make ml db cm bnd \<equiv> (ml,db,cm,bnd)"
  definition cdb_dest :: "clause_db \<Rightarrow> _" where [simp]: "cdb_dest cdb \<equiv> cdb"
  
  definition with_cdb_read' :: "(clause_db \<Rightarrow> 'a) \<Rightarrow> clause_db \<Rightarrow> 'a" where "with_cdb_read' f cdb\<^sub>0 \<equiv> do {
    let cdb = cdb_dest cdb\<^sub>0;
    let r = f cdb;
    let _ = unborrow' cdb cdb\<^sub>0;
    r
  }"
  

  lemma with_cdb_read_alt[simp]: "with_cdb_read' f cdb = f cdb"
    unfolding with_cdb_read'_def
    by simp
              
    
  subsubsection \<open>Empty\<close>  
  definition cdb_empty :: "nat \<Rightarrow> clause_db" where "cdb_empty cap \<equiv> cdb_make 0 [None] (op_dfun_empty 0) (cap+1)"

  lemma cdb_empty_refine[simp]:
    "cdb_invar (cdb_empty cap)"
    "cdb_\<alpha> (cdb_empty cap) = {}"
    "cdb_lits (cdb_empty cap) = {}"
    "cdb_cap (cdb_empty cap) = cap"
    unfolding cdb_empty_def cdb_invar_def cdb_\<alpha>_def cdb_lits_def cdb_cap_def
    by (auto simp: )


  subsubsection \<open>Access to Internal Details\<close>
  (* Will be unfolded for higher levels, but simplify sepref refinement for code that breaks up internal details *)
  definition "cdb_lookup_cid \<equiv> with_cdb_read' (\<lambda>(_,db,cm,_) i. doN {
    ASSERT(i \<in> zdom 0 cm);
    RETURN (op_dfun_lookup cm (dest_cid i))
  })"      
  
  (* TODO: Implement op_dfun_lookup_unguarded, as we know that index is in range. *)
    
  definition "cdb_get_db \<equiv> with_cdb_read' (\<lambda>(_,db,cm,_) i. doN {
    mop_list_get db i
  })"      
    
  subsubsection \<open>Valid IDs and Lookup\<close>  
  
  definition cdb_id_valid :: "clause_db \<Rightarrow> nat \<Rightarrow> bool" where 
    "cdb_id_valid \<equiv> with_cdb_read' (\<lambda>(_,db,cm,_) i. dest_cid i \<in> zdom 0 cm)"

  definition cdb_lookup :: "clause_db \<Rightarrow> nat \<Rightarrow> dimacs_var clause" where 
    "cdb_lookup \<equiv> with_cdb_read' (\<lambda>(ml,db,cm,bnd) i. cdb_internal_clause_at db (cm i))"

  lemma cdb_lookup_correct: "cdb_id_valid cdb i \<Longrightarrow> cdb_lookup cdb i \<in> cdb_\<alpha> cdb"
    unfolding cdb_id_valid_def cdb_lookup_def cdb_\<alpha>_def
    by (auto simp: zdom_def zran_def)

  lemma cdb_lookup_finite[simp,intro!]: "finite (cdb_lookup cdb cid)"
    unfolding cdb_lookup_def by (auto split: prod.split) 
    
  lemma cdb_id_valid_empty[simp]: "\<not>cdb_id_valid (cdb_empty cap) cid"  
    unfolding cdb_id_valid_def cdb_empty_def
    by auto
    
  subsubsection \<open>Iteration over Clause\<close>
  
  definition cdb_iterate :: "clause_db \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> (dimacs_var literal \<Rightarrow> 'a \<Rightarrow> 'a nres) \<Rightarrow> 'a \<Rightarrow> 'a nres" 
    where "cdb_iterate \<equiv> \<lambda>(ml,db,cm,bnd) cid c f s. do {
    ASSERT(cid\<in>zdom 0 cm);
    zseg_fold None db (cm cid) c (f o the) s
  }"

  lemma cdb_iterate_foreach_refine1:
    assumes "cdb_invar cdb"
    assumes "cdb_id_valid cdb cid"
    assumes RS: "(s,s')\<in>Rs"
    assumes CR: "\<And>s s'. (s,s')\<in>Rs \<Longrightarrow> (c s, c' s')\<in>bool_rel"
    assumes F'_refine: "\<And>l l' s s'. \<lbrakk> (l,l')\<in>Id; l'\<in>cdb_lits cdb; (s,s')\<in>Rs  \<rbrakk> \<Longrightarrow> f l s \<le> \<Down>Rs (f' l' s')"
    shows "cdb_iterate cdb cid c f s \<le> \<Down>Rs (FOREACHcd (cdb_lookup cdb cid) c' f' s')"
    using assms(1,2)
    unfolding FOREACHcd_def cdb_id_valid_def cdb_iterate_def cdb_lookup_def cdb_internal_clause_at_def
    unfolding zdom_def
    apply clarsimp
    subgoal for ml db cm
      apply (rule rhs_step_bind_SPEC[where x'="map the (zseg_at None db (cm cid))"], simp)
      apply (rule order_trans[OF zseg_fold_refine nfoldli_invar_refine[where I=top]])
      supply [refine_dref_RELATES] = RELATESI[of "br the (Not o is_None)"]
      apply refine_dref_type
      subgoal unfolding cdb_invar_def by (auto simp: zran_def) 
      subgoal
        unfolding cdb_invar_def
        apply (simp add: map_in_list_rel_conv)
        using zseg_nZ_ulito
        by auto
      subgoal using RS .
      subgoal by simp
      subgoal using CR by blast
      subgoal by (simp add: pw_leof_iff)
      subgoal for l1i xi l2i l1 x l2 si s
        apply (clarsimp simp: in_br_conv)
        using zseg_subset[of None db "cm cid"]
        using F'_refine[of x x si s]
        apply (clarsimp simp: pw_le_iff refine_pw_simps)
        apply (auto simp: in_br_conv cdb_lits_def)
        done
      done
    done
  
       
  lemma cdb_iterate_refine[refine]:
    assumes CDBR: "(cdb,cdb')\<in>Id"
    assumes CIDR: "(cid,cid')\<in>Id"
    assumes CR: "\<And>s s'. (s,s')\<in>Rs \<Longrightarrow> (c s, c' s')\<in>bool_rel"
    assumes FR: "\<And>l l' s s'. \<lbrakk> (l,l')\<in>Id; (s,s')\<in>Rs \<rbrakk> \<Longrightarrow> f l s \<le>\<Down>Rs (f' l' s')"
    assumes SR: "(s,s')\<in>Rs"
    shows "cdb_iterate cdb cid c f s \<le> \<Down>Rs (cdb_iterate cdb' cid' c' f' s')"  
    unfolding cdb_iterate_def zseg_fold_def comp_def
    using CDBR CIDR SR CR
    supply [refine_dref_RELATES] = RELATESI[of Rs]
    apply (refine_rcg FR)
    apply (refine_dref_type)
    by simp_all
    
    

  lemma cdb_iterate_foreach_refine:
    assumes CDBI: "cdb_invar cdb'"
    assumes CIDV: "cdb_id_valid cdb' cid'"
    assumes CDBR: "(cdb,cdb')\<in>Id"
    assumes CIDR: "(cid,cid')\<in>Id"
    assumes CR: "\<And>s s'. (s,s')\<in>Rs \<Longrightarrow> (c s, c' s')\<in>bool_rel"
    assumes FR: "\<And>l l' s s'. \<lbrakk> (l,l')\<in>Id; l'\<in>cdb_lits cdb; (s,s')\<in>Rs \<rbrakk> \<Longrightarrow> f l s \<le>\<Down>Rs (f' l' s')"
    assumes SR: "(s,s')\<in>Rs"
    shows "cdb_iterate cdb cid c f s \<le> \<Down>Rs (FOREACHcd (cdb_lookup cdb' cid') c' f' s')"
    using cdb_iterate_foreach_refine1[where Rs=Rs] assms by simp 
    
        
  subsubsection \<open>Last Index and Building up Clause\<close>  
    
  definition cdb_last_idx :: "clause_db \<Rightarrow> nat" where "cdb_last_idx \<equiv> with_cdb_read' (\<lambda>(_,db,_,_). length db)"  
  
  definition cdb_append :: "clause_db \<Rightarrow> dimacs_var literal option \<Rightarrow> clause_db nres" where 
    "cdb_append cdb l \<equiv> do {
      let (ml,db,cm,bnd) = cdb_dest cdb; 
      ASSERT (length db < bnd);
      RETURN (cdb_make (max (ulito_of l) ml) (db@[l]) cm bnd)
    }"
        
  lemma cdb_last_idx_valid[simp]: "cdb_invar cdb \<Longrightarrow> cdb_idx_valid cdb (cdb_last_idx cdb)"
    unfolding cdb_invar_def cdb_last_idx_def cdb_idx_valid_def by auto
  
  lemma cdb_clause_at_last[simp]: "cdb_internal_clause_at db (cdb_last_idx (ml,db,cm,bnd)) = {}"
    unfolding cdb_last_idx_def cdb_internal_clause_at_def
    by (auto split: prod.splits)
    
    
  lemma cdb_last_last_idx[simp]: "cdb_last cdb (cdb_last_idx cdb) = []"
    unfolding cdb_last_def cdb_last_idx_def cdb_internal_clause_at_def
    by (auto split: prod.splits)
    

  fun the_lit_set where
    "the_lit_set None = {}"
  | "the_lit_set (Some l) = {l}"    
    
  lemma in_the_lit_set_conv[simp]: "x\<in>the_lit_set l \<longleftrightarrow> (l=Some x)"
    by (cases l) auto
  
  lemma the_lit_set_empty_conv[simp]: "the_lit_set l = {} \<longleftrightarrow> l=None"  
    by (cases l) auto
    
  
  lemma cdb_append_correct[refine_vcg]:
    assumes "cdb_invar cdb"    
    assumes "cdb_cap cdb > 0"
    shows "cdb_append cdb l \<le> SPEC (\<lambda>cdb'. 
        cdb_invar cdb'
      \<and> cdb_\<alpha> cdb' = cdb_\<alpha> cdb
      \<and> cdb_cap cdb' = cdb_cap cdb - 1
      \<and> cdb_lits cdb' = cdb_lits cdb \<union> the_lit_set l
      \<and> (\<forall>i. cdb_idx_valid cdb i \<longrightarrow> cdb_last cdb' i = cdb_last cdb i @ [l] \<and> cdb_idx_valid cdb' i)
      \<and> (cdb_id_valid cdb' = cdb_id_valid cdb)
    )"
    unfolding cdb_append_def
    apply refine_vcg
    using assms
    apply clarsimp_all
    unfolding cdb_invar_def cdb_cap_def cdb_last_def cdb_\<alpha>_def cdb_internal_clause_at_def cdb_idx_valid_def cdb_lits_def cdb_id_valid_def
    apply (clarsimp_all simp: zseg_is_term_append zseg_append)
    apply (all \<open>(intro conjI equalityI subsetI)?\<close>)
    by (auto simp: ulito_of.simps)
    

  subsubsection \<open>Maximum Literal\<close>  
  definition cdb_maxlit :: "clause_db \<Rightarrow> nat" where "cdb_maxlit \<equiv> with_cdb_read' (\<lambda>(ml,_,_,_). ml)"  

  lemma cdb_maxlit_bound: "cdb_invar cdb \<Longrightarrow> vars_of_cnf (cdb_\<alpha> cdb) \<subseteq> maxlit_vdom (cdb_maxlit cdb)"
    unfolding cdb_invar_def cdb_\<alpha>_def cdb_maxlit_def cdb_internal_clause_at_def 
      vars_of_cnf_def vars_of_clause_def
    apply (clarsimp simp:)
    subgoal for ml db cm cidx l l'
      apply (subst in_maxlit_vdom_iff)
      using zseg_subset[of None db l]
      using ulit_maxlit_adjust_bounds
      by (metis le_trans option.collapse subsetD zseg_nZ)
    done      

    
          
  subsubsection \<open>State of last Clause\<close>

  definition is_open_clause :: "clause_db_list \<Rightarrow> bool" where "is_open_clause xs \<equiv> None \<notin> set xs"
  definition is_terminated_clause :: "clause_db_list \<Rightarrow> bool" where "is_terminated_clause xs \<equiv> xs\<noteq>[] \<and> last xs = None \<and> None \<notin> set (butlast xs)"  
  definition the_clause :: "clause_db_list \<Rightarrow> dimacs_var clause" where "the_clause xs \<equiv> set (map the (zseg_at None xs 0))"
          
  lemma open_clause_empty[simp]:
    "is_open_clause []"
    "the_clause [] = {}"
    unfolding is_open_clause_def the_clause_def
    by auto

  lemma open_clause_append[simp]:
    assumes "is_open_clause xs"
    assumes "\<not>is_None l"  
    shows "is_open_clause (xs@[l])" "the_clause (xs@[l]) = insert (the l)(the_clause xs)"
    using assms
    unfolding is_open_clause_def the_clause_def
    apply (auto simp: zseg_append)
    by (auto simp: ulito_invar_def ulito_\<alpha>_def zseg_is_term_alt zseg_at_def split: if_splits)
    
  lemma open_clause_terminate[simp]: 
    assumes "is_open_clause xs"
    shows "is_terminated_clause (xs@[None])" "the_clause(xs@[None]) = the_clause xs"
    using assms
    unfolding is_open_clause_def is_terminated_clause_def the_clause_def ulito_zero_def
    apply (auto simp: zseg_append)
    apply (auto simp: zseg_at_def)
    done
    
  lemma is_terminated_imp_zseg_term:
    "is_terminated_clause xs \<Longrightarrow> zseg_is_term None xs 0"
    unfolding is_terminated_clause_def zseg_is_term_alt
    by (auto simp: neq_Nil_rev_conv)  
    
    
      
  subsubsection \<open>Register Clause\<close>    
    
  definition cdb_register_clause :: "nat \<Rightarrow> nat \<Rightarrow> clause_db \<Rightarrow> clause_db nres"
  where "cdb_register_clause \<equiv> \<lambda>cid idx cdb. do {
    let (ml,db,cm,bnd) = cdb_dest cdb;
    ASSERT(cdb_idx_valid (ml,db,cm,bnd) idx);
    ASSERT(is_terminated_clause (cdb_last (ml,db,cm,bnd) idx));
    let cm = op_dfun_upd cm (dest_cid cid) idx;
    RETURN (cdb_make ml db cm bnd)  
  }"
  
  lemma cdb_register_clause_correct:
    assumes "cdb_invar cdb"
    assumes "cdb_idx_valid cdb idx"
    assumes "\<not>cdb_id_valid cdb cid"
    assumes "is_terminated_clause (cdb_last cdb idx)"
    shows "cdb_register_clause cid idx cdb \<le> SPEC (\<lambda>cdb'.
        cdb_invar cdb' 
      \<and> cdb_\<alpha> cdb' = insert (the_clause (cdb_last cdb idx)) (cdb_\<alpha> cdb) 
      \<and> (cdb_cap cdb' = cdb_cap cdb)
      \<and> (\<forall>cid'. cdb_id_valid cdb' cid' \<longleftrightarrow> cid' = cid \<or> cdb_id_valid cdb cid')
      \<and> (cdb_lits cdb' = cdb_lits cdb)
    )"
    using assms
    unfolding cdb_register_clause_def
    apply refine_vcg
    apply simp_all
    subgoal for db cm
      unfolding cdb_invar_def zran_def
      by (auto dest!: is_terminated_imp_zseg_term simp: cdb_last_def cdb_idx_valid_def)
    subgoal for db cm
      unfolding cdb_\<alpha>_def cdb_internal_clause_at_def cdb_last_def cdb_id_valid_def cdb_idx_valid_def
      unfolding the_clause_def zran_def zdom_def
      by (auto simp: )
    subgoal unfolding cdb_cap_def by auto   
    subgoal for db cm
      unfolding cdb_id_valid_def zran_def zdom_def cdb_idx_valid_def
      by (auto)
    subgoal for db cm
      unfolding cdb_lits_def by auto  
    done     

  
      
  lemma cdb_register_clause_correct_weak:
    assumes "cdb_invar cdb"
    assumes "cdb_idx_valid cdb idx"
    assumes "is_terminated_clause (cdb_last cdb idx)"
    shows "cdb_register_clause cid idx cdb \<le> SPEC (\<lambda>cdb'.
        cdb_invar cdb' 
      \<and> cdb_\<alpha> cdb' \<subseteq> insert (the_clause (cdb_last cdb idx)) (cdb_\<alpha> cdb)
      \<and> (cdb_cap cdb' = cdb_cap cdb)
      \<and> (cdb_lits cdb' = cdb_lits cdb)
    )"
    using assms
    unfolding cdb_register_clause_def
    apply refine_vcg
    apply simp_all
    subgoal for db cm
      unfolding cdb_invar_def zran_def
      by (auto dest!: is_terminated_imp_zseg_term simp: cdb_last_def)
    subgoal for db cm
      unfolding cdb_\<alpha>_def cdb_internal_clause_at_def cdb_last_def zran_def
      by (auto simp: the_clause_def)
    subgoal unfolding cdb_cap_def by auto   
    subgoal for db cm
      unfolding cdb_lits_def by auto  
    done     


  subsubsection \<open>Check for Empty Clause\<close>  
        
  definition cdb_is_empty_clause :: "clause_db \<Rightarrow> nat \<Rightarrow> bool nres" 
    where "cdb_is_empty_clause \<equiv> \<lambda>cdb idx. do {
    let (ml,db,cm,bnd) = cdb_dest cdb;
    ASSERT(cdb_idx_valid (ml,db,cm,bnd) idx \<and> is_terminated_clause (cdb_last (ml,db,cm,bnd) idx));
    l\<leftarrow>mop_list_get db idx;
    let cdb' = cdb_make ml db cm bnd;
    unborrow cdb' cdb;
    RETURN (is_None l)
  }"      

  
  lemma terminated_clause_check_empty:
    assumes "is_terminated_clause xs" 
    shows "xs\<noteq>[]" "is_None (xs!0) \<longleftrightarrow> the_clause xs = {}"
    using assms unfolding is_terminated_clause_def the_clause_def
    by (auto simp: zseg_eq_Nil_conv)
    
  
  lemma cdb_is_empty_clause_correct[refine_vcg]:
    assumes "cdb_idx_valid cdb idx" "is_terminated_clause (cdb_last cdb idx)"
    shows "cdb_is_empty_clause cdb idx \<le> SPEC (\<lambda>r. r \<longleftrightarrow> the_clause (cdb_last cdb idx) = {})"
    using assms unfolding cdb_is_empty_clause_def
    apply refine_vcg
    apply simp_all
    unfolding cdb_idx_valid_def cdb_last_def
    by (auto dest: terminated_clause_check_empty)



subsection \<open>Implementation\<close>


term cdb_make

sepref_register 
  cdb_make :: "nat \<Rightarrow> clause_db_list \<Rightarrow> (nat,nat) i_dfun \<Rightarrow> nat \<Rightarrow> nat \<times> clause_db_list \<times> (nat \<Rightarrow> nat) \<times> nat"
  cdb_dest :: "nat \<times> clause_db_list \<times> (nat \<Rightarrow> nat) \<times> nat \<Rightarrow> nat \<times> clause_db_list \<times> (nat, nat) i_dfun \<times> nat"

sepref_register 
  cdb_empty
  
  cdb_lookup_cid cdb_get_db
   
  cdb_id_valid cdb_last_idx cdb_append cdb_maxlit cdb_register_clause cdb_is_empty_clause

(* cdb_lookup is only refined when iterating over clause *)


typ clause_db

type_synonym clause_dbi = "lit_size_t word \<times> (lit_size_t word,size_t) array_list \<times> (size_t word,size_t) nadf"

definition cdb_assn :: "clause_db \<Rightarrow> clause_dbi \<Rightarrow> assn" where "cdb_assn \<equiv> \<lambda>(ml,db,cm,bnd) (mli,dbi,cmi). 
    lit_assn ml mli 
  ** al_assn' size_T ulito_assn db dbi 
  ** nadf_assn' size_T (snat_const size_T 0) size_assn cm cmi 
  ** dropi_assn (rdomp size_assn) bnd ghost_var"


(* For paper *)  
lemma "cdb_assn (ml,db,cm,bnd) (mli,dbi,cmi) = (
    lit_assn ml mli 
  ** al_assn ulito_assn db dbi 
  ** nadf_assn 0 size_assn cm cmi 
  ** \<up>(bnd < 2^(size_t_len-1))
  )"
proof -
  have A: "dropi_assn (rdomp size_assn) bnd ghost_var = \<up>(bnd < 2^(size_t_len-1))" for bnd
    unfolding b_assn_def pure_def any_rel_def rdomp_def 
    apply (auto simp: sep_algebra_simps in_br_conv)
    subgoal by (auto simp: sep_algebra_simps in_br_conv snat_rel_def snat.rel_def snat_eq_unat snat_invar_alt)
    subgoal
      apply (rule exI[where x="word_of_nat bnd"])
      unfolding snat_rel_def snat.rel_def in_br_conv
      by (simp add: snat_def int_eq_sint snat_invar_alt unat_of_nat_eq)
    done

  show ?thesis
    unfolding cdb_assn_def A
    by simp
qed  
    
lemma cdb_assn_rdomp_aux: "rdomp cdb_assn (ml,db,cm,bnd) \<Longrightarrow> 
  rdomp lit_assn ml
\<and> rdomp (al_assn' size_T ulito_assn) db
\<and> rdomp (nadf_assn' size_T (snat_const size_T 0) size_assn) cm
\<and> rdomp size_assn bnd
  "  
  unfolding cdb_assn_def rdomp_conv_pure_part
  by (auto dest!: pure_part_split_conj)


    
lemma cdb_assn_len_boundD[sepref_bounds_dest]: "rdomp cdb_assn cdb \<Longrightarrow> cdb_db_len cdb < max_size"
  apply (cases cdb; auto dest!: cdb_assn_rdomp_aux)
  by (auto dest!: sepref_bounds_dest simp: cdb_db_len_def)
  
definition cdb_make_impl :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> 'a word \<Rightarrow> clause_dbi llM" 
  where [llvm_inline]: "cdb_make_impl mli dbi cmi _ \<equiv> Mreturn (mli,dbi,cmi)"


lemma cdb_make_impl_refine[sepref_fr_rules]: 
  "(uncurry3 cdb_make_impl,uncurry3 (RETURN oooo cdb_make)) 
  \<in> [\<lambda>_. True]\<^sub>c lit_assn\<^sup>k *\<^sub>a (al_assn' size_T ulito_assn)\<^sup>d *\<^sub>a (nadf_assn' size_T (snat_const size_T 0) size_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> cdb_assn [\<lambda>(((ml,db),cm),_) r. r = (ml,db,cm) ]\<^sub>c"
  unfolding cdb_make_def cdb_make_impl_def cdb_assn_def any_rel_def
  apply sepref_to_hoare
  apply vcg_normalize
  
  apply (simp named_ss HOL_basic_ss_nomatch: move_resolve_ex_eq)
  
  supply [simp] = rdomp_pure_rel_eq
  apply vcg
  done    

lemma cdb_make_impl_refine2[sepref_fr_rules]: 
  "(uncurry3 cdb_make_impl,uncurry3 (RETURN oooo cdb_make)) 
  \<in> [\<lambda>_. True]\<^sub>c lit_assn\<^sup>k *\<^sub>a (al_assn' size_T ulito_assn)\<^sup>d *\<^sub>a (nadf_assn' size_T (snat_const size_T 0) size_assn)\<^sup>d *\<^sub>a (dropi_assn (rdomp size_assn))\<^sup>k \<rightarrow> cdb_assn [\<lambda>(((ml,db),cm),_) r. r = (ml,db,cm) ]\<^sub>c"
  unfolding cdb_make_def cdb_make_impl_def cdb_assn_def any_rel_def
  unfolding cdb_make_def cdb_make_impl_def cdb_assn_def any_rel_def
  apply sepref_to_hoare
  apply vcg_normalize
  
  apply (simp named_ss HOL_basic_ss_nomatch: move_resolve_ex_eq)
  
  supply [simp] = rdomp_pure_rel_eq
  apply vcg
  done    
  
  
  
lemma cdb_dest_impl_refine[sepref_fr_rules]: 
  "(\<lambda>(a,b,c). Mreturn (a,b,c,ghost_var::1 word), RETURN o cdb_dest) 
  \<in> [\<lambda>_. True]\<^sub>c cdb_assn\<^sup>d \<rightarrow> lit_assn \<times>\<^sub>a al_assn' size_T ulito_assn \<times>\<^sub>a nadf_assn' size_T (snat_const size_T 0) size_assn \<times>\<^sub>a dropi_assn (rdomp size_assn) [\<lambda>(ml,db,cm) (ml',db',cm',_). ml'=ml \<and> db'=db \<and> cm'=cm]\<^sub>c"  
  unfolding cdb_dest_def cdb_assn_def any_rel_def
  apply sepref_to_hoare
  apply vcg_normalize
  apply (simp named_ss HOL_basic_ss_nomatch: move_resolve_ex_eq)
  by vcg
  
  

term op_nadf_empty  
  
term cdb_empty
  
lemma singleton_list_by_append_conv: "[a] = op_list_append [] a"  by auto

find_theorems is_init


sepref_def cdb_empty_impl is "RETURN o cdb_empty" :: "[\<lambda>cap. cap+1 < max_size]\<^sub>a size_assn\<^sup>k \<rightarrow> cdb_assn"  
  unfolding cdb_empty_def
  
  apply (subst singleton_list_by_append_conv)
  apply (subst al_fold_custom_empty[where 'l=size_t])
  apply (subst nadf_fold_custom_empty[where 'l=size_t and A=size_assn])
  apply (subst fold_ulito_None)
  apply (rewrite at "cdb_make \<hole>" unat_const_fold[where 'a=lit_size_t])
  apply (annot_snat_const size_T)
  by sepref
  
  
term cdb_id_valid

lemma in_zdom_impl_conv: "i\<in>zdom 0 f \<longleftrightarrow> op_dfun_lookup f i \<noteq> 0"
  unfolding zdom_def by auto


lemma with_cdb_read'_lamdba: "with_cdb_read' (\<lambda>(a,b,c,d) i. f a b c d i) = (\<lambda>cdb i. with_cdb_read' (\<lambda>(a,b,c,d). f a b c d i) cdb)" by auto
    
  
lemma with_cdb_read'_unf: "with_cdb_read' (\<lambda>(a,b,c,d). f a b c d) cdb\<^sub>0 \<equiv> 
  case cdb_dest cdb\<^sub>0 of (a,b,c,d) \<Rightarrow> do {
    let r = f a b c d;
    let cdb = cdb_make a b c d;
    let _ = unborrow' cdb cdb\<^sub>0;
    r
  }"
  by simp

lemma with_cdb_read'_unf_monadic: "with_cdb_read' (\<lambda>(a,b,c,d). f a b c d) cdb\<^sub>0 \<equiv> 
  case cdb_dest cdb\<^sub>0 of (a,b,c,d) \<Rightarrow> do {
    r \<leftarrow> f a b c d;
    let cdb = cdb_make a b c d;
    let _ = unborrow' cdb cdb\<^sub>0;
    RETURN r
  }"
  by simp

sepref_def cdb_lookup_cid_impl [llvm_inline] is "uncurry cdb_lookup_cid" :: "cdb_assn\<^sup>k *\<^sub>a cid_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"  
  unfolding cdb_lookup_cid_def with_cdb_read'_lamdba
  unfolding with_cdb_read'_unf_monadic
  by sepref  

sepref_def cdb_get_db_impl [llvm_inline] is "uncurry cdb_get_db" :: "cdb_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a ulito_assn"
  unfolding cdb_get_db_def with_cdb_read'_lamdba 
  unfolding with_cdb_read'_unf_monadic
  by sepref  
    
  
sepref_def cdb_id_valid_impl [llvm_inline] is "uncurry (RETURN oo cdb_id_valid)" :: "cdb_assn\<^sup>k *\<^sub>a cid_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding cdb_id_valid_def in_zdom_impl_conv with_cdb_read'_lamdba
  unfolding with_cdb_read'_unf
  apply (annot_snat_const size_T)
  by sepref
  
term cdb_last_idx

sepref_def cdb_last_idx_impl [llvm_inline] is "(RETURN o cdb_last_idx)" :: "cdb_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding cdb_last_idx_def
  unfolding with_cdb_read'_unf
  by sepref    
  
term cdb_append
  
sepref_def cdb_append_impl [llvm_inline] is "uncurry cdb_append" :: "cdb_assn\<^sup>d *\<^sub>a ulito_assn\<^sup>k \<rightarrow>\<^sub>a cdb_assn"
  unfolding cdb_append_def Let_def max_def
  by sepref
    
  
term cdb_maxlit  
sepref_def cdb_maxlit_impl [llvm_inline] is "RETURN o cdb_maxlit" :: "cdb_assn\<^sup>k \<rightarrow>\<^sub>a lit_assn"
  unfolding cdb_maxlit_def
  unfolding with_cdb_read'_unf
  by sepref    
  
term cdb_register_clause

sepref_def cdb_register_clause_impl [llvm_inline] is "uncurry2 cdb_register_clause" 
  :: "cid_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a cdb_assn\<^sup>d \<rightarrow>\<^sub>a cdb_assn"
  unfolding cdb_register_clause_def Let_def
  by sepref

term cdb_is_empty_clause
  
sepref_def cdb_is_empty_clause_impl [llvm_inline] is "uncurry (cdb_is_empty_clause)" :: "cdb_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"  
  unfolding cdb_is_empty_clause_def
  by sepref  
    

sepref_definition cdb_free [llvm_code] is "\<lambda>cdb. doN {let _ = cdb_dest cdb; RETURN ()}" :: "cdb_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn"  
  by sepref

lemma cdb_free[sepref_frame_free_rules]: "MK_FREE cdb_assn cdb_free"
  apply (rule MK_FREE_hfrefI[OF cdb_free.refine])
  by auto
  
  
  
end
