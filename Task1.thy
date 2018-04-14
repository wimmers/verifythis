theory Task1
imports VTcomp
begin

  type_synonym 'a gap_buffer = "nat \<times> nat \<times> 'a list"

  definition "gap_\<alpha> \<equiv> \<lambda>(l,r,buf). (l,take l buf @ drop r buf)"
  definition "gap_invar \<equiv> \<lambda>(l,r,buf). l\<le>r \<and> r\<le>length buf"
  
  abbreviation "gap_rel \<equiv> br gap_\<alpha> gap_invar"
  

  definition "aleft \<equiv> \<lambda>(l,buf). (if l>0 then (l-1,buf) else (l,buf))"
  definition "ainsert x \<equiv> \<lambda>(l,buf). (l+1,take l buf@x#drop l buf)"
 
  definition "cleft \<equiv> \<lambda>(l,r,buf). (if l\<noteq>0 then (l-1,r-1,buf[r-1:=buf!(l-1)]) else (l,r,buf))"

  lemma drop_split_first:
    "drop (i - 1) xs = xs ! (i - 1) # drop i xs" if "i > 0" "i \<le> length xs"
    using that by (cases i) (auto simp: Cons_nth_drop_Suc)

  definition "aright \<equiv> \<lambda>(l,buf). if l<length buf then (l+1,buf) else (l,buf)"
  definition "adelete \<equiv> \<lambda>(l,buf). (if l\<noteq>0 then (l-1,take (l-1) buf @ drop l buf) else (l,buf))"
  
  lemma "(cleft, aleft) \<in> gap_rel \<rightarrow> gap_rel"
    apply (auto simp: in_br_conv gap_\<alpha>_def gap_invar_def aleft_def cleft_def split: prod.splits)
    subgoal for l r buf
      using take_Suc_conv_app_nth[of "l - 1" buf]
      apply (auto simp: drop_split_first[simplified])
      done
     apply linarith
    apply linarith
    done
 
  definition "cinsert x \<equiv> \<lambda>(l,r,buf). (l+1,r,buf[l:=x])" 


  lemma "(cinsert,ainsert) \<in> Id \<rightarrow> gap_rel \<rightarrow> gap_rel"
    unfolding cinsert_def ainsert_def gap_\<alpha>_def gap_invar_def
    oops
    apply (auto simp: in_br_conv)
    subgoal  sorry
    subgoal  sorry
    done 
    

  definition "cright \<equiv> \<lambda>(l,r,buf). (if l<length buf then (l+1,r+1,buf[l:=buf!r]) else (l,r,buf))"
    
  lemma "(cright,aright) \<in> gap_rel \<rightarrow> gap_rel"
    unfolding cinsert_def ainsert_def gap_\<alpha>_def gap_invar_def
    apply (auto simp: in_br_conv split: prod.split)
    subgoal   sorry
    subgoal   sorry
    subgoal   sorry
    
    oops
    

  definition "cdelete \<equiv> \<lambda>(l,r,buf). (if l\<noteq>0 then (l-1,r,buf) else (l,r,buf))"
  lemma "(cdelete,adelete) \<in> gap_rel \<rightarrow> gap_rel"
    unfolding cdelete_def adelete_def gap_\<alpha>_def gap_invar_def
    by (auto simp: in_br_conv split: prod.split)
        
    
    
end
