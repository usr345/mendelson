theory Sequent
imports Sequents.LK
begin
lemma imply_self: "\<turnstile> A \<longrightarrow> A"
  apply (rule impR)
  apply (rule basic)
  done

lemma conj_elim1 : "A \<and> B \<turnstile> A"
  apply (rule conjL)
  apply (rule basic)
  done

lemma disj_intro1 : "A \<turnstile> A \<or> B"
  apply (rule disjR)
  apply (rule basic)
  done

lemma double_neg : "A \<turnstile> \<not>\<not> A"
  apply (rule notR)
  apply (rule exchL)
  apply (rule notL)
  apply (rule basic)
  done

lemma ExcludedMiddle: "\<turnstile> A \<or> \<not>A"
  apply (rule disjR)
  apply (rule notR)
  apply (rule basic)
  done

lemma MP: "A \<longrightarrow> B, A \<turnstile> B"
  apply (rule impL)
  subgoal
    apply (rule thinR)
    apply (rule basic)
    done
  subgoal
    apply (rule exchL)
    apply (rule thinL)
    apply (rule basic)
    done
  done

lemma Syllogism: "A \<longrightarrow> B, B \<longrightarrow> C \<turnstile> A \<longrightarrow> C"
  apply (rule impR)
  apply (rule impL)
  subgoal
    apply (rule thinL)
    apply (rule thinR)
    apply (rule basic)
    done
  subgoal
    apply (rule exchL)
    apply (rule impL)
    subgoal
      apply (rule thinR)
      apply (rule exchL)
      apply (rule thinL)
      apply (rule basic)
      done
    subgoal
      apply (rule exchL)
      apply (rule thinL)
      apply (rule exchL)
      apply (rule thinL)
      apply (rule basic)
      done
    done
  done

lemma DeMorganDisj: "\<not>(A \<or> B) \<turnstile> \<not>A \<and> \<not>B"
  apply (rule conjR)
  subgoal
    apply (rule notR)
    apply (rule notL)
    apply (rule disjR)
    apply (rule exchR)
    apply (rule thinR)
    apply (rule basic)
    done
  subgoal
    apply (rule notR)
    apply (rule notL)
    apply (rule disjR)
    apply (rule thinR)
    apply (rule basic)
    done
  done

lemma DeMorganConj: "\<not>(A \<and> B) \<turnstile> \<not>A \<or> \<not>B"
  apply (rule disjR)
  apply (rule notR)
  apply (rule notR)
  apply (rule notL)
  apply (rule conjR)
  subgoal
    apply (rule exchL)
    apply (rule thinL)
    apply (rule basic)
    done
  subgoal
    apply (rule thinL)
    apply (rule basic)
    done
  done

lemma DeMorganConjBack: "\<not>(\<not>A \<and> \<not>B) \<turnstile> A \<or> B"
  apply (rule disjR)
  apply (rule notL)
  apply (rule conjR)
  subgoal
    apply (rule notR)
    apply (rule basic)
    done
  subgoal
    apply (rule notR)
    apply (rule basic)
    done
  done

lemma Distributivity : "A \<and> (B \<or> C) \<turnstile> (A \<and> B) \<or> (A \<and> C)"
  apply (rule conjL)
  apply (rule disjR)
  apply (rule conjR)
  subgoal
    apply (rule exchL)
    apply (rule thinL)
    apply (rule exchR)
    apply (rule thinR)
    apply (rule basic)
    done
  subgoal
    apply (rule exchL)
    apply (rule disjL)
    subgoal
      apply (rule exchL)
      apply (rule thinL)
      apply (rule exchR)
      apply (rule thinR)
      apply (rule basic)
      done
    subgoal
      apply (rule thinR)
      apply (rule conjR)
       apply (rule thinL)
       apply (rule basic)
       apply (rule basic)
      done
    done
  done

lemma Pierce: "\<turnstile> ((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P"
  apply (rule impR)
  apply (rule impL)
  subgoal
    apply (rule impR)
    apply (rule basic)
    done
  subgoal
    apply (rule basic)
    done
  done

lemma Pierce_cut: "\<turnstile> ((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P"
  apply (rule impR)
  apply (rule_tac P="P" in cut)
  subgoal
    (* P is False *)
    apply (rule impL)
    subgoal
      apply (rule impR)
      apply (rule basic)
      done
    subgoal
      apply (rule basic)
      done
    done
  subgoal
    (* P is True *)
    apply (rule basic)
    done
  done

lemma A1: "\<turnstile> A \<longrightarrow> B \<longrightarrow> A"
  apply (rule impR)
  apply (rule impR)
  apply (rule basic)
  done  

lemma A2: "\<turnstile> (A \<longrightarrow> (B \<longrightarrow> C)) \<longrightarrow> ((A \<longrightarrow> B) \<longrightarrow> (A \<longrightarrow> C))"
  apply (rule impR)
  apply (rule impR)
  apply (rule impR)
  apply (rule impL)
  subgoal
    apply (rule basic)
    done
  subgoal
    apply (rule impL)
    subgoal
      apply (rule impL)
        apply (rule basic)
      apply (rule basic)
      done
    subgoal
      apply (rule basic)
      done
    done
done

lemma ExcludedMiddle_cut: "\<turnstile> A \<or> \<not> A"
  apply (rule_tac P="A" in cut)
  subgoal
    apply (rule disjR)
    apply (rule notR)
    apply (rule basic)
    done
  subgoal
    apply (rule disjR)
    apply (rule basic)
    done
  done

(* 1.0.2 *)
lemma B2_1 : "\<not> a \<longrightarrow> \<not> b \<turnstile> b \<longrightarrow> a"
  apply (rule impR)
  apply (rule impL)
  subgoal
    apply (rule exchR)
    apply (rule notR)
    apply (rule thinL)
    apply (rule basic)
    done
  subgoal
    apply (rule notL)
    apply (rule thinR)
    apply (rule basic)
    done
  done

lemma B2_2 : "b \<longrightarrow> a \<turnstile> \<not> a \<longrightarrow> \<not> b"
  apply (rule impR)
  apply (rule impL)
  subgoal
    apply (rule notR)
    apply (rule thinL)
    apply (rule basic)
    done
  subgoal
    apply (rule exchL)
    apply (rule notL)
    apply (rule thinR)
    apply (rule basic)
    done
  done

lemma B20_1 : "a \<and> b \<longrightarrow> c \<turnstile> a \<longrightarrow> b \<longrightarrow> c"
  apply (rule impR)
  apply (rule impR)
  apply (rule impL)
  subgoal
    apply (rule thinR)
    apply (rule conjR)
     apply (rule basic)
    apply (rule basic)
    done
  subgoal
    apply (rule basic)
    done
  done

lemma B20_2 : "a \<longrightarrow> b \<longrightarrow> c \<turnstile> a \<and> b \<longrightarrow> c"
  apply (rule impR)
  apply (rule exchL)
  apply (rule conjL)
  apply (rule impL)
    apply (rule basic)
  apply (rule impL)
    apply (rule basic)
  apply (rule basic)
  done

lemma QB1 : "P(a) \<turnstile> \<exists> x . P(x)"
  apply (rule_tac x="a" in exR)
  apply (rule basic)
  done

lemma QB2 : "\<forall> x . P(x) \<turnstile> \<forall> y . P(y)"
  apply (rule allR)
  apply (rule_tac x="x" in allL)
  apply (rule basic)
  done

lemma QB7 : "\<exists> x . P(x) \<turnstile> \<exists> x . (P(x) \<or> Q(x))"
  apply (rule exL)
  apply (rule_tac x="x" in exR)
  apply (rule disjR)
  apply (rule basic)
  done

lemma QB13 : "\<exists> x . \<forall> y . R(x, y) \<turnstile> \<forall> y . \<exists> x . R(x, y)"
  apply (rule exL)
  apply (rule allR)
  apply (rule_tac x="x" in exR)
  apply (rule_tac x="xa" in allL)
  apply (rule basic)
  done

lemma QB14 : "\<forall> x . P(x) \<longrightarrow> Q(x), \<exists> x . \<not> Q(x) \<turnstile> \<exists> x . \<not> P(x)"
  apply (rule exL)
  apply (rule_tac x="x" in exR)
  apply (rule_tac x="x" in allL)
  apply (rule notR)
  apply (rule notL)
  apply (rule impL)
   apply (rule basic)
  apply (rule basic)
  done

lemma QB28 : "(\<exists> x . P(x)) \<and> (\<forall> y . P(y) \<longrightarrow> Q(y)) \<turnstile> \<exists> z . Q(z)"
  apply (rule conjL)
  apply (rule exL)
  apply (rename_tac a)
  apply (rule_tac x="a" in exR)
  apply (rule_tac x="a" in allL)
  apply (rule impL)
   apply (rule basic)
  apply (rule basic)
  done

lemma QB29 : "\<forall> x . P(a) \<longrightarrow> Q(x), P(a) \<turnstile> \<forall> x . Q(x)"
  apply (rule allR)
  apply (rule_tac x="x" in allL)
  apply (rule impL)
   apply (rule basic)
  apply (rule basic)
  done

lemma QB30 : "P(a) \<longrightarrow> (\<forall> x .  Q(x)) \<turnstile> \<forall> x . P(a) \<longrightarrow> Q(x)"
  apply (rule allR)
  apply (rule impR)
  apply (rule impL)
   apply (rule basic)
  apply (rule_tac x="x" in allL)
  apply (rule basic)
  done

lemma QB31 : "\<not> (\<exists> x . S(x)) \<turnstile> \<not> (\<exists> x . S(x) \<and> P(x))"
  apply (rule notL)
  apply (rule notR)
  apply (rule exL)
  apply (rule conjL)
  apply (rule_tac x="x" in exR)
  apply (rule basic)
  done

lemma QB32 : "\<exists> x . S(x) \<turnstile> (\<forall> x . S(x) \<longrightarrow> P(x)) \<longrightarrow> (\<exists> x . S(x) \<and> P(x))"
  apply (rule exL)
  apply (rule impR)
  apply (rule_tac x="x" in allL)
  apply (rule_tac x="x" in exR)
  apply (rule conjR)
   apply (rule basic)
  apply (rule impL)
   apply (rule basic)
  apply (rule basic)
  done
    
end