theory Snippets
imports VTcomp
begin

  section \<open>Find Element in Array (Arrays)\<close>

  definition "find_elem (x::int) xs \<equiv> do {
    WHILEIT (\<lambda>i. i\<le>length xs \<and> x\<notin>set (take i xs)) (\<lambda>i. i<length xs \<and> xs!i\<noteq>x) (\<lambda>i. RETURN (i+1)) 0
  }"
  
  lemma "find_elem x xs \<le> SPEC (\<lambda>i. i\<le>length xs \<and> (i<length xs \<longrightarrow> xs!i = x))"
    unfolding find_elem_def
    apply refine_vcg
    apply (rule wf_measure[of "\<lambda>i. length xs - i"])
    apply (auto simp: in_set_conv_nth)
    (*sledgehammer*)
    using less_Suc_eq by blast
    
  sepref_definition find_elem_impl is "uncurry find_elem" :: "int_assn\<^sup>k *\<^sub>a (array_assn int_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn"
    unfolding find_elem_def short_circuit_conv
    by sepref
  
  export_code find_elem_impl in Haskell module_name test


  section \<open>Check Prefix (Arrays, Exceptions: Check)\<close>
    
  definition "check_prefix xs ys \<equiv> doE {
    CHECK (length xs \<le> length ys) ();
    EWHILEIT (\<lambda>i. i\<le>length xs \<and> take i xs = take i ys) (\<lambda>i. i<length xs) (\<lambda>i. doE { 
      EASSERT (i<length xs \<and> i<length ys); 
      CHECK (xs!i = ys!i) (); 
      ERETURN (i+1) 
    } ) 0;
    ERETURN ()
  }"
  
  (* ESPEC Exc Normal ! *)
  lemma "check_prefix xs ys \<le> ESPEC (\<lambda>_. xs \<noteq> take (length xs) ys) (\<lambda>_. xs = take (length xs) ys)"
    unfolding check_prefix_def
    apply (refine_vcg EWHILEIT_rule[where R="measure (\<lambda>i. length xs - i)"])
    apply auto []
    apply auto []
    apply auto []
    apply auto []
    apply auto []
    apply auto []
    subgoal
      by (simp add: take_Suc_conv_app_nth)
    apply auto []
    apply auto []
    subgoal 
      by (metis nth_take)
    subgoal 
      by force
    apply auto []
    done
  
  synth_definition check_prefix_bd is [enres_unfolds]: "check_prefix xs ys = \<hole>"
    apply (rule CNV_eqD)
    unfolding check_prefix_def
    apply opt_enres_unfold
    apply (rule CNV_I)
    done
    
  sepref_definition check_prefix_impl is "uncurry check_prefix_bd" 
    :: "(array_assn int_assn)\<^sup>k *\<^sub>a (array_assn int_assn)\<^sup>k \<rightarrow>\<^sub>a (unit_assn +\<^sub>a unit_assn)"
    unfolding check_prefix_bd_def
    by sepref
  
  export_code check_prefix_impl checking SML_imp
  

  section \<open>Is Prefix (Arrays, Exceptions: Catch)\<close>
  
  definition "is_prefix xs ys \<equiv> CATCH (doE {
    CHECK (length xs \<le> length ys) ();
    EWHILEIT (\<lambda>i. i\<le>length xs \<and> take i xs = take i ys) (\<lambda>i. i<length xs) (\<lambda>i. doE { 
      EASSERT (i<length xs \<and> i<length ys); 
      CHECK (xs!i = ys!i) (); 
      ERETURN (i+1) 
    } ) 0;
    ERETURN True
  }) (\<lambda>_. ERETURN False)"
  
  (* ESPEC Exc Normal ! *)
  lemma "is_prefix xs ys \<le> ESPEC (\<lambda>_. False) (\<lambda>r. r \<longleftrightarrow> xs = take (length xs) ys)"
    unfolding is_prefix_def
    apply (refine_vcg EWHILEIT_rule[where R="measure (\<lambda>i. length xs - i)"])
    apply auto []
    apply auto []
    apply auto []
    apply auto []
    apply auto []
    apply auto []
    subgoal
      by (simp add: take_Suc_conv_app_nth)
    apply auto []
    apply auto []
    subgoal 
      by (metis nth_take)
    subgoal 
      by force
    apply auto []
    done
  
  synth_definition is_prefix_bd is [enres_unfolds]: "is_prefix xs ys = \<hole>"
    apply (rule CNV_eqD)
    unfolding is_prefix_def
    apply opt_enres_unfold
    apply (rule CNV_I)
    done
    
  sepref_definition is_prefix_impl is "uncurry is_prefix_bd" 
    :: "(array_assn int_assn)\<^sup>k *\<^sub>a (array_assn int_assn)\<^sup>k \<rightarrow>\<^sub>a (unit_assn +\<^sub>a bool_assn)"
    unfolding is_prefix_bd_def
    by sepref
  
  export_code is_prefix_impl checking SML_imp
  
  
  
  
  
  
  
  
  
  section \<open>Copy Array (Arrays, For i=l..u)\<close>  
  
  definition "cp_array xs \<equiv> do {
    let ys = op_array_replicate (length xs) 0;   (* Use proper constructors *)
    
    ys \<leftarrow> nfoldli [0..<length xs] (\<lambda>_. True) (\<lambda>i ys. do {  (* Ensure linearity! ys\<leftarrow>\<dots> *)
      ASSERT (i<length xs \<and> i<length ys); 
      RETURN (ys[i:=xs!i]) 
    }) ys;
    
    RETURN ys
  }"
  
  sepref_definition cp_array_impl is cp_array :: "(array_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a array_assn nat_assn"
    unfolding cp_array_def
    by sepref
  
  
  
end
