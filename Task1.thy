theory Task1
imports VTcomp
begin

  type_synonym 'a gap_buffer = "nat \<times> nat \<times> 'a list"

  definition "gap_\<alpha> \<equiv> \<lambda>(l,r,buf). (l,take l buf @ drop r buf)"
  definition "gap_invar \<equiv> \<lambda>(l,r,buf). l\<le>r \<and> r\<le>length buf"
  
  abbreviation "gap_rel \<equiv> br gap_\<alpha> gap_invar"
  

  definition "aleft \<equiv> \<lambda>(l,buf). (if l>0 then (l-1,buf) else (l,buf))"
  definition "ainsert x \<equiv> \<lambda>(l,buf). (l+1,take l buf@x#drop l buf)"
  
  definition "cleft \<equiv> \<lambda>(l,r,buf). (if l\<noteq>0 then (l-1,r-1,buf[r:=buf!l]) else (l,r,buf))"
  
  lemma "(cleft, aleft) \<in> gap_rel \<rightarrow> gap_rel"
    apply (auto simp: in_br_conv gap_\<alpha>_def gap_invar_def aleft_def cleft_def split: prod.splits)
  subgoal for l r buf
    apply (rule nth_equalityI)
    apply (auto simp: nth_append min_def)
    apply (fo_rule fun_cong arg_cong)
    apply auto
    apply (fo_rule fun_cong arg_cong)
    sorry    
  subgoal 
    by simp 
  subgoal 
    by linarith 
    done
    
  definition "cinsert x \<equiv> \<lambda>(l,r,buf). (l+1,r,buf[l:=x])" 
  
  lemma "(cinsert,ainsert) \<in> Id \<rightarrow> gap_rel \<rightarrow> gap_rel"
    unfolding cinsert_def ainsert_def gap_\<alpha>_def gap_invar_def
    apply (auto simp: in_br_conv)
    subgoal sledgehammer sorry
    subgoal sledgehammer sorry
    done 
    
    
end
