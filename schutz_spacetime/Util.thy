theory Util
imports Main

(* Some "utility" proofs -- little proofs that come in handy every now and then. *)

begin

text\<open>For multiple uses of conjI\<close>
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

(* Nice for use in "lemmas" statements. *)
(* lemma def_mp:
  "\<lbrakk>P \<equiv> Q; P\<rbrakk> \<Longrightarrow> Q"
by simp
lemma def_mp2:
  "\<lbrakk>P \<equiv> Q; Q\<rbrakk> \<Longrightarrow> P"
by simp

lemma ex_distrib_and:
  "\<exists>x. P x \<and> Q x \<Longrightarrow> (\<exists>x. P x) \<and> (\<exists>x. Q x)"
by auto

lemma ex_distrib_and':
  "\<exists>x\<in>S. P x \<and> Q x \<Longrightarrow> (\<exists>x\<in>S. P x) \<and> (\<exists>x\<in>S. Q x)"
by auto

lemma conj_elim:
  "\<lbrakk>R; R \<Longrightarrow> P; R \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> P \<and> Q"
by simp *)

(* I need this in order to obtain a natural number which can be passed to the ordering function,
   distinct from two others, in the case of a finite set of events with cardinality a least 3. *)
lemma is_free_nat:
  assumes "(m::nat) < n"
      and "n < c"
      and "c \<ge> 3"
  shows "\<exists>k::nat. k < m \<or> (m < k \<and> k < n) \<or> (n < k \<and> k < c)"
using assms by presburger

(* lemma minus_ex_nat: "(\<exists>n::nat. f n = x) \<Longrightarrow> (\<forall>m. \<exists>n::nat. f (n - m) = x)"
proof (rule allI)
  fix m
  assume "\<exists>n. f n = x"
  then obtain k where "f k = x" by blast
  then have "f ((k + m) - m) = x" by simp
  then show "\<exists>n. f (n - m) = x" by blast
qed *)

(* Helpful proofs on sets. *)

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


(* Some of the following lemmas could easily go both ways, but go one way only so that the automatic
   stuff can be used without too much worry about it getting wild. *)
(* These are the kinds of lemmas that make my life a lot easier with some of the ordering proofs. *)

lemma less_3_cases: "n < 3 \<Longrightarrow> n = 0 \<or> n = Suc 0 \<or> n = Suc (Suc 0)"
by auto
(* 
lemma less_2_cases_ex: "\<exists>n::nat < 2. P n \<Longrightarrow> P 0 \<or> P 1"
using less_2_cases by fastforce

lemma less_2_cases_all: "\<forall>n::nat < 2. P n \<Longrightarrow> P 0 \<and> P 1"
by simp

lemma less_3_cases_ex: "\<exists>n::nat < 3. P n \<Longrightarrow> P 0 \<or> P 1 \<or> P 2"
by (metis One_nat_def less_3_cases numerals(2))

lemma less_3_cases_all: "\<forall>n::nat < 3. P n \<Longrightarrow> P 0 \<and> P 1 \<and> P 2"
  by simp *)

end