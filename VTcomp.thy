theory VTcomp
imports 
  Array_Map_Default
  Dynamic_Array
  (*Impl_List_Set_Ndj*)
  Synth_Definition
  Exc_Nres_Monad
begin

no_notation Ref.lookup ("!_" 61)
no_notation Ref.update ("_ := _" 62)

section \<open>Added Stuff\<close>

lemma nfoldli_upt_rule:
  assumes INTV: "lb\<le>ub"
  assumes I0: "I lb \<sigma>0"
  assumes IS: "\<And>i \<sigma>. \<lbrakk> lb\<le>i; i<ub; I i \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f i \<sigma> \<le> SPEC (I (i+1))"
  assumes FNC: "\<And>i \<sigma>. \<lbrakk> lb\<le>i; i\<le>ub; I i \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes FC: "\<And>\<sigma>. \<lbrakk> I ub \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "nfoldli [lb..<ub] c f \<sigma>0 \<le> SPEC P"
  apply (rule nfoldli_rule[where I="\<lambda>l _ \<sigma>. I (lb+length l) \<sigma>"])
  apply simp_all
  apply (simp add: I0)
  subgoal using IS
    by (metis Suc_eq_plus1 add_diff_cancel_left' eq_diff_iff le_add1 length_upt upt_eq_lel_conv)
  subgoal for l1 l2 \<sigma> 
    apply (rule FNC[where i="lb + length l1"])
    apply (auto simp: INTV)
    using INTV upt_eq_append_conv by auto
  apply (rule FC) using INTV 
  by auto  

term Refine_Basic.bind
  
abbreviation (do_notation) bind_doN where "bind_doN \<equiv> Refine_Basic.bind"

notation (output) bind_doN (infixr "\<bind>" 54)
notation (ASCII output) bind_doN (infixr ">>=" 54)


nonterminal doN_binds and doN_bind
syntax
  "_doN_block" :: "doN_binds \<Rightarrow> 'a" ("doN {//(2  _)//}" [12] 62)
  "_doN_bind"  :: "[pttrn, 'a] \<Rightarrow> doN_bind" ("(2_ \<leftarrow>/ _)" 13)
  "_doN_let" :: "[pttrn, 'a] \<Rightarrow> doN_bind" ("(2let _ =/ _)" [1000, 13] 13)
  "_doN_then" :: "'a \<Rightarrow> doN_bind" ("_" [14] 13)
  "_doN_final" :: "'a \<Rightarrow> doN_binds" ("_")
  "_doN_cons" :: "[doN_bind, doN_binds] \<Rightarrow> doN_binds" ("_;//_" [13, 12] 12)
  "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixr "\<then>" 54)

syntax (ASCII)
  "_doN_bind" :: "[pttrn, 'a] \<Rightarrow> doN_bind" ("(2_ <-/ _)" 13)
  "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixr ">>" 54)

translations
  "_doN_block (_doN_cons (_doN_then t) (_doN_final e))"
    \<rightleftharpoons> "CONST bind_doN t (\<lambda>_. e)"
  "_doN_block (_doN_cons (_doN_bind p t) (_doN_final e))"
    \<rightleftharpoons> "CONST bind_doN t (\<lambda>p. e)"
  "_doN_block (_doN_cons (_doN_let p t) bs)"
    \<rightleftharpoons> "let p = t in _doN_block bs"
  "_doN_block (_doN_cons b (_doN_cons c cs))"
    \<rightleftharpoons> "_doN_block (_doN_cons b (_doN_final (_doN_block (_doN_cons c cs))))"
  "_doN_cons (_doN_let p t) (_doN_final s)"
    \<rightleftharpoons> "_doN_final (let p = t in s)"
  "_doN_block (_doN_final e)" \<rightharpoonup> "e"
  "(m \<then> n)" \<rightharpoonup> "(m \<bind> (\<lambda>_. n))"
  
  
definition [enres_unfolds]: "efor (lb::int) ub f \<sigma> \<equiv> doE {
  EASSERT (lb\<le>ub);
  (_,\<sigma>) \<leftarrow> EWHILET (\<lambda>(i,\<sigma>). i<ub) (\<lambda>(i,\<sigma>). doE { \<sigma> \<leftarrow> f i \<sigma>; ERETURN (i+1,\<sigma>) }) (lb,\<sigma>);
  ERETURN \<sigma>
}"  
  
thm EWHILEIT_rule

  
lemma efor_rule:
  assumes INTV: "lb\<le>ub"
  assumes I0: "I lb \<sigma>0"
  assumes IS: "\<And>i \<sigma>. \<lbrakk> lb\<le>i; i<ub; I i \<sigma> \<rbrakk> \<Longrightarrow> f i \<sigma> \<le> ESPEC E (I (i+1))"
  assumes FC: "\<And>\<sigma>. \<lbrakk> I ub \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "efor lb ub f \<sigma>0 \<le> ESPEC E P"
  unfolding efor_def
  supply EWHILET_rule[where R="measure (\<lambda>(i,_). nat (ub-i))" and I="\<lambda>(i,\<sigma>). lb\<le>i \<and> i\<le>ub \<and> I i \<sigma>", refine_vcg]
  apply refine_vcg
  apply auto
  using assms apply auto
  done
  


end
