(*  Title:      schutz_spacetime/Util.thy
    Authors:    Richard Schmoetten, Jake Palmer and Jacques D. Fleuriot
                University of Edinburgh, 2021          
*)
theory Util
imports Main

(* Some "utility" proofs -- little proofs that come in handy every now and then. *)

begin

text \<open>For multiple uses of \<open>conjI\<close> (goal splitting).\<close>

lemma conjI3: "P1 \<Longrightarrow> P2 \<Longrightarrow> P3 \<Longrightarrow> P1\<and>P2\<and>P3"
  by auto
lemma conjI4: "P1 \<Longrightarrow> P2 \<Longrightarrow> P3 \<Longrightarrow> P4 \<Longrightarrow> P1\<and>P2\<and>P3\<and>P4"
  by auto
lemma conjI5: "P1 \<Longrightarrow> P2 \<Longrightarrow> P3 \<Longrightarrow> P4 \<Longrightarrow> P5 \<Longrightarrow> P1\<and>P2\<and>P3\<and>P4\<and>P5"
  by auto
lemma conjI6: "P1 \<Longrightarrow> P2 \<Longrightarrow> P3 \<Longrightarrow> P4 \<Longrightarrow> P5 \<Longrightarrow> P6 \<Longrightarrow> P1\<and>P2\<and>P3\<and>P4\<and>P5\<and>P6"
  by auto
lemma conjI7: "P1 \<Longrightarrow> P2 \<Longrightarrow> P3 \<Longrightarrow> P4 \<Longrightarrow> P5 \<Longrightarrow> P6 \<Longrightarrow> P7 \<Longrightarrow> P1\<and>P2\<and>P3\<and>P4\<and>P5\<and>P6\<and>P7"
  by auto

text \<open>
  We need this in order to obtain a natural number which can be passed to the ordering function,
  distinct from two others, in the case of a finite set of events with cardinality a least 3.
\<close>

lemma is_free_nat:
  assumes "(m::nat) < n"
      and "n < c"
      and "c \<ge> 3"
  shows "\<exists>k::nat. k < m \<or> (m < k \<and> k < n) \<or> (n < k \<and> k < c)"
using assms by presburger

text \<open>Helpful proofs on sets.\<close>

lemma set_le_two [simp]: "card {a, b} \<le> 2"
by (simp add: card_insert_if)

lemma set_le_three [simp]: "card {a, b, c} \<le> 3"
by (simp add: card_insert_if)

lemma card_subset: "\<lbrakk>card Y = n; Y \<subseteq> X\<rbrakk> \<Longrightarrow> card X \<ge> n \<or> infinite X"
using card_mono by blast

lemma card_subset_finite: "\<lbrakk>finite X; card Y = n; Y \<subseteq> X\<rbrakk> \<Longrightarrow> card X \<ge> n"
using card_subset by auto

lemma three_subset: "\<lbrakk>x \<noteq> y; x \<noteq> z; y \<noteq> z; {x,y,z} \<subseteq> X\<rbrakk> \<Longrightarrow> card X \<ge> 3 \<or> infinite X"
apply (case_tac "finite X")
apply (auto simp : card_mono)
apply (erule_tac Y = "{x,y,z}" in card_subset_finite)
  by auto

lemma card_Collect_nat:
  assumes "(j::nat)>i"
  shows "card {i..j} = j-i+1"
  using card_atLeastAtMost
  using Suc_diff_le assms le_eq_less_or_eq by presburger

lemma card_4_eq:
  "card X = 4 \<longleftrightarrow> (\<exists>S\<^sub>1. \<exists>S\<^sub>2. \<exists>S\<^sub>3. \<exists>S\<^sub>4. X = {S\<^sub>1, S\<^sub>2, S\<^sub>3, S\<^sub>4} \<and>
    S\<^sub>1 \<noteq> S\<^sub>2 \<and> S\<^sub>1 \<noteq> S\<^sub>3 \<and> S\<^sub>1 \<noteq> S\<^sub>4 \<and> S\<^sub>2 \<noteq> S\<^sub>3 \<and> S\<^sub>2 \<noteq> S\<^sub>4 \<and> S\<^sub>3 \<noteq> S\<^sub>4)"
  (is "card X = 4 \<longleftrightarrow> ?card4 X")
proof
  assume "card X = 4"
  hence "card X \<ge> 4" by auto
  then obtain S\<^sub>1 S\<^sub>2 S\<^sub>3 S\<^sub>4 where
    0: "S\<^sub>1\<in>X \<and> S\<^sub>2\<in>X \<and> S\<^sub>3\<in>X \<and> S\<^sub>4\<in>X" and
    1: "S\<^sub>1 \<noteq> S\<^sub>2 \<and> S\<^sub>1 \<noteq> S\<^sub>3 \<and> S\<^sub>1 \<noteq> S\<^sub>4 \<and> S\<^sub>2 \<noteq> S\<^sub>3 \<and> S\<^sub>2 \<noteq> S\<^sub>4 \<and> S\<^sub>3 \<noteq> S\<^sub>4"
    apply (simp add: eval_nat_numeral)
    by (auto simp add: card_le_Suc_iff)
  then have 2: "{S\<^sub>1, S\<^sub>2, S\<^sub>3, S\<^sub>4} \<subseteq> X" "card {S\<^sub>1, S\<^sub>2, S\<^sub>3, S\<^sub>4} = 4" by auto
  have "X = {S\<^sub>1, S\<^sub>2, S\<^sub>3, S\<^sub>4}"
    using Finite_Set.card_subset_eq \<open>card X = 4\<close>
    apply (simp add: eval_nat_numeral)
    by (smt (z3) \<open>card X = 4\<close> 2 card.infinite card_subset_eq nat.distinct(1))
  thus "?card4 X" using 1 by blast
next
  show "?card4 X \<Longrightarrow> card X = 4"
    by (smt (z3) card.empty card.insert eval_nat_numeral(2) finite.intros(1) finite_insert insertE
      insert_absorb insert_not_empty numeral_3_eq_3 semiring_norm(26,27))
qed


text \<open>These lemmas make life easier with some of the ordering proofs.\<close>

lemma less_3_cases: "n < 3 \<Longrightarrow> n = 0 \<or> n = Suc 0 \<or> n = Suc (Suc 0)"
by auto

end