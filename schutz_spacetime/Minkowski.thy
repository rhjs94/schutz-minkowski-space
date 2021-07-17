theory Minkowski
imports Main TernaryOrdering
begin

(* It is best to avoid `distinct` because it makes proof more difficult. *)
(* If it has to be used, the lemma: distinct_length_2_or_more is essential. *)
(* For proofs involving the cardinality of concrete, finite sets see `card_insert_if`. *)

(* I've tried to do little to no proofs in this file, and keep that in other files. *)
(* So, this is mostly locale and other definitions, except where it is nice to prove something
   about definitional equivalence and the like (plus the intermediate lemmas that are necessary for
   doing so). *)

(* Minkowski spacetime = <\<E>, \<P>, [...]>
   except in the notation here I've used [[...]] for [...] as Isabelle uses [...] for lists.

   Except where stated otherwise all axioms are exactly as they appear in Schutz97.
   It is the independent axiomatic system provided in the main body of the book.
   The axioms O1-O6 are the axioms of order, and largely concern properties of the betweenness
   relation.
   I1-I7 are the axioms of incidence.
   I1-I3 are similar to axioms found in systems for Euclidean geometry. As compared to Hilbert's
   Foundations (HIn), our incidence axioms (In) are loosely identifiable as
    I1 \<rightarrow> HI3, HI8;
    I2 \<rightarrow> HI1;
    I3 \<rightarrow> HI2.
   I4 fixes the dimension of the space.
   I5-I7 are what makes our system non-Galilean, and lead (I think) to Lorentz transforms and
   the ultimate speed limit.
   Axioms S and C and the axioms of symmetry and continuity, where the latter is what makes the
   system second order. Symmetry replaces all of Hilbert's axioms of congruence, when considered
   in the context of I5-I7.
*)

(* Events \<E>, paths \<P>, and {spray,SPRAY}s. Sprays only need to refer to \<E> and \<P>. *)
(* in_path_event is something that is covered in English by saying "a path is a set of events",
   but is necessary to have explicitly as an axiom as the types do not force it to be the case. *)

(* I1 has been removed as it is trivially provable by I4. Presumably Schutz had something in mind
   to do with making no assumptions about different subsets of the axioms being together, but I'm
   not sure what use it would have for us. It is easily reinstated if necessary. *)
(* I have now reinstated axiom I1. I think part of why Schutz has I1, together with the trickery
   `\<lbrakk> \<E>\<noteq>{} \<rbrakk> \<Longrightarrow>` in I4, is that then I4 talks *only* about dimension, and results such
   as no_empty_paths can be proved using only existence of elements and unreachable sets.
   In our case, it's also a question of ordering the sequence of axiom introductions:
   dimension should really go at the end, since it is not needed for quite a while;
   but many earlier proofs rely on the set of events being non-empty. *)

section "MinkowskiPrimitive: I1-I3"

locale MinkowskiPrimitive =
  fixes \<E> :: "'a set"
    and \<P> :: "('a set) set"
  assumes in_path_event [simp]: "\<lbrakk>Q \<in> \<P>; a \<in> Q\<rbrakk> \<Longrightarrow> a \<in> \<E>"
      (* I1 *)
      and nonempty_events [simp]: "\<E> \<noteq> {}"
      (* I2 *)
      (* It's still possible to have 1 event and 0 paths. *)
      and events_paths: "\<lbrakk>a \<in> \<E>; b \<in> \<E>; a \<noteq> b\<rbrakk> \<Longrightarrow> \<exists>R\<in>\<P>. \<exists>S\<in>\<P>. a \<in> R \<and> b \<in> S \<and> R \<inter> S \<noteq> {}"
      (* I3 *)
      and eq_paths [intro]: "\<lbrakk>P \<in> \<P>; Q \<in> \<P>; a \<in> P; b \<in> P; a \<in> Q; b \<in> Q; a \<noteq> b\<rbrakk> \<Longrightarrow> P = Q"
begin

(* This should be ensured by the additional axiom. *)
lemma path_sub_events:
  "Q \<in> \<P> \<Longrightarrow> Q \<subseteq> \<E>"
by (simp add: subsetI)

lemma paths_sub_power:
  "\<P> \<subseteq> Pow \<E>"
by (simp add: path_sub_events subsetI)

(* For more terse statements. *)
(* a \<noteq> b because a and b are being used to identify the path, and a = b would not do that. *)
abbreviation path :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "path ab a b \<equiv> ab \<in> \<P> \<and> a \<in> ab \<and> b \<in> ab \<and> a \<noteq> b"

abbreviation path_ex :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "path_ex a b \<equiv> \<exists>Q. path Q a b"

lemma path_permute:
  "path ab a b = path ab b a"
  by auto

abbreviation path_of :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "path_of a b \<equiv> THE ab. path ab a b"

lemma path_of_ex: "path (path_of a b) a b \<longleftrightarrow> path_ex a b"
  using theI' [where P="\<lambda>x. path x a b"] eq_paths by blast

(* Not sure if there's any point in this for abbreviations. *)
lemma path_unique:
  assumes "path ab a b" and "path ab' a b"
    shows "ab = ab'"
  using eq_paths assms by blast


section "Primitives: Unreachable Subset (from an Event)"

(* The Q \<in> \<P> \<and> b \<in> \<E> constraints are necessary as the types as not expressive enough to do it on
    their own. *)
(* Is this better or worse than Schutz's notation? His is: Q(b,\<emptyset>) *)
definition unreachable_subset :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set" ("\<emptyset> _ _" [100, 100] 100) where
  "unreachable_subset Q b \<equiv> {x\<in>Q. Q \<in> \<P> \<and> b \<in> \<E> \<and> b \<notin> Q \<and> \<not>(\<exists>R\<in>\<P>. b \<in> R \<and> x \<in> R)}"
  (* "unreachable_subset Q b \<equiv> {x\<in>Q. Q \<in> \<P> \<and> b \<in> \<E> \<and> b \<notin> Q \<and> \<not>(path_ex b x)}" *)


section "Primitives: Kinematic Triangle"

(* If we don't have a \<notin> S then a, b, and s*)
definition kinematic_triangle :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("\<triangle> _ _ _" [100, 100, 100] 100) where
    "kinematic_triangle a b c \<equiv>
       a \<in> \<E> \<and> b \<in> \<E> \<and> c \<in> \<E> \<and> a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c
       \<and> (\<exists>Q\<in>\<P>. \<exists>R\<in>\<P>. Q \<noteq> R \<and> (\<exists>S\<in>\<P>. Q \<noteq> S \<and> R \<noteq> S
                                       \<and> a \<in> Q \<and> b \<in> Q
                                       \<and> a \<in> R \<and> c \<in> R
                                       \<and> b \<in> S \<and> c \<in> S))"

(* A fuller, more explicit equivalent of \<triangle>, to show that the above definition is sufficient. *)
lemma tri_full:
  "\<triangle> a b c = (a \<in> \<E> \<and> b \<in> \<E> \<and> c \<in> \<E> \<and> a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c
              \<and> (\<exists>Q\<in>\<P>. \<exists>R\<in>\<P>. Q \<noteq> R \<and> (\<exists>S\<in>\<P>. Q \<noteq> S \<and> R \<noteq> S
                                              \<and> a \<in> Q \<and> b \<in> Q \<and> c \<notin> Q
                                              \<and> a \<in> R \<and> c \<in> R \<and> b \<notin> R
                                              \<and> b \<in> S \<and> c \<in> S \<and> a \<notin> S)))"
unfolding kinematic_triangle_def by (meson path_unique)


section "Primitives: SPRAY"

(* It's okay to not require x \<in> \<E> because if x \<notin> \<E> the SPRAY will be empty anyway, and if it's
   nonempty then x \<in> \<E> is derivable. *)
definition SPRAY :: "'a \<Rightarrow> ('a set) set" where
  "SPRAY x \<equiv> {R\<in>\<P>. x \<in> R}"

definition spray :: "'a \<Rightarrow> 'a set" where
  "spray x \<equiv> {y. \<exists>R\<in>SPRAY x. y \<in> R}"

(* Just for convenience. *)
definition is_SPRAY :: "('a set) set \<Rightarrow> bool" where
  "is_SPRAY S \<equiv> \<exists>x\<in>\<E>. S = SPRAY x"

definition is_spray :: "'a set \<Rightarrow> bool" where
  "is_spray S \<equiv> \<exists>x\<in>\<E>. S = spray x"

(* Some very simple SPRAY and spray lemmas. *)

lemma SPRAY_event:
  "SPRAY x \<noteq> {} \<Longrightarrow> x \<in> \<E>"
  (* using SPRAY_def by fastforce *)
proof (unfold SPRAY_def)
  assume nonempty_SPRAY: "{R \<in> \<P>. x \<in> R} \<noteq> {}"
  then have x_in_path_R: "\<exists>R \<in> \<P>. x \<in> R" by blast
  thus "x \<in> \<E>" using in_path_event by blast
qed

lemma SPRAY_nonevent:
  "x \<notin> \<E> \<Longrightarrow> SPRAY x = {}"
using SPRAY_event by auto

lemma SPRAY_path:
  "P \<in> SPRAY x \<Longrightarrow> P \<in> \<P>"
by (simp add: SPRAY_def)

lemma in_SPRAY_path:
  "P \<in> SPRAY x \<Longrightarrow> x \<in> P"
by (simp add: SPRAY_def)

lemma source_in_SPRAY:
  "SPRAY x \<noteq> {} \<Longrightarrow> \<exists>P \<in> SPRAY x. x \<in> P"
using in_SPRAY_path by auto

lemma spray_event:
  "spray x \<noteq> {} \<Longrightarrow> x \<in> \<E>"
proof (unfold spray_def)
  assume "{y. \<exists>R \<in> SPRAY x. y \<in> R} \<noteq> {}"
  then have "\<exists>y. \<exists>R \<in> SPRAY x. y \<in> R" by simp
  then have "SPRAY x \<noteq> {}" by blast
  thus "x \<in> \<E>" using SPRAY_event by simp
qed

lemma spray_nonevent:
  "x \<notin> \<E> \<Longrightarrow> spray x = {}"
using spray_event by auto

lemma in_spray_event:
  "y \<in> spray x \<Longrightarrow> y \<in> \<E>"
proof (unfold spray_def)
  assume "y \<in> {y. \<exists>R\<in>SPRAY x. y \<in> R}"
  then have "\<exists>R\<in>SPRAY x. y \<in> R" by (rule CollectD)
  then obtain R where path_R: "R \<in> \<P>"
                  and y_inR: "y \<in> R" using SPRAY_path by auto
  thus "y \<in> \<E>" using in_path_event by simp
qed

lemma source_in_spray:
  "spray x \<noteq> {} \<Longrightarrow> x \<in> spray x"
proof -
  assume nonempty_spray: "spray x \<noteq> {}"
  have spray_eq: "spray x = {y. \<exists>R\<in>SPRAY x. y \<in> R}" using spray_def by simp
  then have ex_in_SPRAY_path: "\<exists>y. \<exists>R\<in>SPRAY x. y \<in> R" using nonempty_spray by simp
  show "x \<in> spray x" using ex_in_SPRAY_path spray_eq source_in_SPRAY by auto
qed


section "Primitives: Path (In)dependence"

(* "A subset of three paths of a SPRAY is dependent if there is a path which does not belong
   to the SPRAY and which contains one event from each of the three paths: we also say any
   one of the three paths is dependent on the other two.
   Otherwise the subset is independent."[Schutz97] *)
(* The definition of SPRAY constrains x, Q, R, S to be in \<E> and \<P>. *)
definition dep3_event :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "dep3_event Q R S x \<equiv> Q \<noteq> R \<and> Q \<noteq> S \<and> R \<noteq> S \<and> Q \<in> SPRAY x \<and> R \<in> SPRAY x \<and> S \<in> SPRAY x
                         \<and> (\<exists>T\<in>\<P>. T \<notin> SPRAY x \<and> (\<exists>y\<in>Q. y \<in> T) \<and> (\<exists>y\<in>R. y \<in> T) \<and> (\<exists>y\<in>S. y \<in> T))"

definition dep3_spray :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> ('a set) set \<Rightarrow> bool" where
  "dep3_spray Q R S SPR \<equiv> \<exists>x. SPRAY x = SPR \<and> dep3_event Q R S x"

definition dep3 :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "dep3 Q R S \<equiv> \<exists>x. dep3_event Q R S x"

(* Some very simple lemmas related to dep3_event. *)

(* Nice to have this on its own. *)
lemma dep3_nonspray:
  assumes "dep3_event Q R S x"
    shows "\<exists>P\<in>\<P>. P \<notin> SPRAY x"
  by (metis assms dep3_event_def)

lemma dep3_path:
  assumes dep3_QRSx: "dep3_event Q R S x"
  shows "Q \<in> \<P>" "R \<in> \<P>" "S \<in> \<P>"
proof -
  have "{Q,R,S} \<subseteq> SPRAY x" using dep3_event_def using dep3_QRSx by simp
  thus "Q \<in> \<P>" "R \<in> \<P>" "S \<in> \<P>" using SPRAY_path by auto
qed

lemma dep3_is_event:
  "dep3_event Q R S x \<Longrightarrow> x \<in> \<E>"
using SPRAY_event dep3_event_def by auto

lemma dep3_event_permute [no_atp]:
  assumes "dep3_event Q R S x"
    shows "dep3_event Q S R x" "dep3_event R Q S x" "dep3_event R S Q x"
     "dep3_event S Q R x" "dep3_event S R Q x"
using dep3_event_def assms by auto
(* lemmas dep3_event_permute1 = dep3_event_permute [THEN conjunct1]
lemmas dep3_event_permute2 = dep3_event_permute [THEN conjunct2, THEN conjunct1]
lemmas dep3_event_permute3 = dep3_event_permute [THEN conjunct2, THEN conjunct2,
                                                 THEN conjunct1]
lemmas dep3_event_permute4 = dep3_event_permute [THEN conjunct2, THEN conjunct2,
                                                 THEN conjunct2, THEN conjunct1]
lemmas dep3_event_permute5 = dep3_event_permute [THEN conjunct2, THEN conjunct2,
                                                 THEN conjunct2, THEN conjunct2] *)

(* "We next give recursive definitions of dependence and independence which will be used to
    characterize the concept of dimension. A path T is dependent on the set of n paths (where
    n \<ge> 3)

    S = {Qi : i = 1, 2, ..., n; Qi \<in> SPRAY x}

    if it is dependent on two paths S1 and S2, where each of these two paths is dependent
    on some subset of n - 1 paths from the set S." [Schutz97] *)
inductive dep_path :: "'a set \<Rightarrow> ('a set) set \<Rightarrow> 'a \<Rightarrow> bool" where
  dep_two: "dep3_event T A B x \<Longrightarrow> dep_path T {A, B} x"
(* Not necessary, but may be helpful? dep3_event_permute covers these cases.
| dep_two2: "dep3_event A T B x \<Longrightarrow> dep_path T {A, B} x"
| dep_two3: "dep3_event A B T x \<Longrightarrow> dep_path T {A, B} x"*)
| dep_n:   "\<lbrakk>S \<subseteq> SPRAY x; card S \<ge> 3; dep_path T {S1, S2} x;
             S' \<subseteq> S; S'' \<subseteq> S; card S' = card S - 1; card S'' = card S - 1;
             dep_path S1 S' x; dep_path S2 S'' x\<rbrakk> \<Longrightarrow> dep_path T S x"

(* NOT actually true! *)
(* We could have e.g. a basis x y z with one added vector v that lies in span(x,y).
   Then the extra vector is dependent on {x y z} but z is independent of {x y v}. *)
(* lemma dep_path_permute:
  assumes "S \<subseteq> SPRAY x" and "P1\<in>S" and "P2\<in>S"
  and "dep_path P1 (S-{P1}) x"
shows "dep_path P2 (S-{P2}) x" *)



(* "We also say that the set of n + 1 paths S\<union>{T} is a dependent set." [Schutz97]
   Starting from this constructive definition, the below gives an analytical one. *)
definition dep_set :: "('a set) set \<Rightarrow> bool" where
  (* "dep_set S \<equiv> \<exists>x. S\<subseteq>SPRAY x \<and> (\<exists>S'\<subseteq>S. \<exists>P\<in>(S-S'). dep_path P S' x)" *)
  "dep_set S \<equiv> \<exists>x. \<exists>S'\<subseteq>S. \<exists>P\<in>(S-S'). dep_path P S' x"
  (* "dep_set S \<equiv> \<exists>P\<in>S. \<exists>x::'a. S \<subseteq> SPRAY x \<and> dep_path P (S-{P}) x" *)
(* TODO: do we want an explicit S \<subseteq> SRPRAY x here? I think dep_path implies it.*)

lemma dependent_superset:
  assumes "dep_set A" and "A\<subseteq>B" (* and "B\<subseteq>SPRAY x" *)
  shows "dep_set B"
  using assms(1) assms(2) dep_set_def
  by (meson Diff_mono dual_order.trans in_mono order_refl)

lemma path_in_dep_set:
  assumes "dep3_event P Q R x"
  shows "dep_set {P,Q,R}" (* and "{P,Q,R}\<subseteq>SPRAY x" *)
  using dep_two assms dep3_event_def dep_set_def
  by (metis DiffI insertE insertI1 singletonD subset_insertI)

lemma path_in_dep_set2:
  assumes "dep3_event P Q R x"
  shows "dep_path P {P,Q,R} x"
proof
  let ?S1 = "Q"
  let ?S2 = "R"
  let ?S' = "{P,R}"
  let ?S'' = "{P,Q}"
  show "{P, Q, R} \<subseteq> SPRAY x" using assms dep3_event_def by blast
  show "3 \<le> card {P, Q, R}" using assms dep3_event_def by auto
  show "dep_path P {?S1, ?S2} x" using assms dep3_event_def by (simp add: dep_two)
  show "?S' \<subseteq> {P, Q, R}" by simp
  show "?S'' \<subseteq> {P, Q, R}" by simp
  show "card ?S' = card {P, Q, R} - 1" using assms dep3_event_def by auto
  show "card ?S'' = card {P, Q, R} - 1" using assms dep3_event_def by auto
  show "dep_path ?S1 ?S' x" by (simp add: assms dep3_event_permute(2) dep_two)
  show "dep_path ?S2 ?S'' x" using assms dep3_event_permute(2,4) dep_two by blast
qed


definition indep_set :: "('a set) set \<Rightarrow> bool" where
  "indep_set S \<equiv> \<not>(\<exists>T \<subseteq> S. dep_set T)"


section "Primitives: 3-SPRAY"

(* "We now make the following definition which enables us to specify the dimensions of Minkowski
   space-time. A SPRAY is a 3-SPRAY if:
     i) it contains four independent paths, and
    ii) all paths of the SPRAY are dependent on these four paths."
*)
(* I'm not sure "\<not> dep_path S (SPRAY x) x" is the correct way to characterise an independent
   path of a SPRAY. *)
(* three_SPRAY says "the SPRAY on x exists and is a 3-SPRAY. *)
definition three_SPRAY :: "'a \<Rightarrow> bool" where
  "three_SPRAY x \<equiv> \<exists>S1\<in>\<P>. \<exists>S2\<in>\<P>. \<exists>S3\<in>\<P>. \<exists>S4\<in>\<P>.
    S1 \<noteq> S2 \<and> S1 \<noteq> S3 \<and> S1 \<noteq> S4 \<and> S2 \<noteq> S3 \<and> S2 \<noteq> S4 \<and> S3 \<noteq> S4
    \<and> S1 \<in> SPRAY x \<and> S2 \<in> SPRAY x \<and> S3 \<in> SPRAY x \<and> S4 \<in> SPRAY x
    \<and> (indep_set {S1, S2, S3, S4})
    \<and> (\<forall>S\<in>SPRAY x. dep_path S {S1,S2,S3,S4} x)"
(* definition three_SPRAY :: "'a \<Rightarrow> bool" where
  "three_SPRAY x \<equiv> \<exists>S1\<in>\<P>. \<exists>S2\<in>\<P>. \<exists>S3\<in>\<P>. \<exists>S4\<in>\<P>.
                      S1 \<noteq> S2 \<and> S1 \<noteq> S3 \<and> S1 \<noteq> S4 \<and> S2 \<noteq> S3 \<and> S2 \<noteq> S4 \<and> S3 \<noteq> S4
                      \<and> S1 \<in> SPRAY x \<and> S2 \<in> SPRAY x \<and> S3 \<in> SPRAY x \<and> S4 \<in> SPRAY x
                      \<and> (\<forall>S\<in>{S1,S2,S3,S4}. \<not> dep_path S (SPRAY x) x)
                      \<and> (\<forall>S\<in>SPRAY x. dep_path S {S1,S2,S3,S4} x)" *)

(* is_three_SPRAY says "this set of sets of elements is a set of paths which is a 3-SPRAY. *)
definition is_three_SPRAY :: "('a set) set \<Rightarrow> bool" where
  "is_three_SPRAY SPR \<equiv> \<exists> x. SPR = SPRAY x \<and> three_SPRAY x"

(* Just extracting a bit of the definition basically. *)
lemma three_SPRAY_ge4:
  assumes "three_SPRAY x"
  shows "\<exists>Q1\<in>\<P>. \<exists>Q2\<in>\<P>. \<exists>Q3\<in>\<P>. \<exists>Q4\<in>\<P>. Q1 \<noteq> Q2 \<and> Q1 \<noteq> Q3 \<and> Q1 \<noteq> Q4 \<and> Q2 \<noteq> Q3 \<and> Q2 \<noteq> Q4 \<and> Q3 \<noteq> Q4"
using assms three_SPRAY_def by meson

end (* MinkowskiPrimitive *)

section "MinkowskiBetweenness: O1-O5"

locale MinkowskiBetweenness = MinkowskiPrimitive +
  fixes betw :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("[[_ _ _]]")
      (* O1 *) (*notice this is not only for events, but all things with same data type*)
  assumes abc_ex_path: "[[a b c]] \<Longrightarrow> \<exists>Q\<in>\<P>. a \<in> Q \<and> b \<in> Q \<and> c \<in> Q"
      (* O2 *)
      and abc_sym: "[[a b c]] \<Longrightarrow> [[c b a]]"
      (* O3, relaxed, as O3 can be proven from this. *)
      and abc_ac_neq: "[[a b c]] \<Longrightarrow> a \<noteq> c"
      (* O4 *)
      (* I have removed the requirement that a \<noteq> d in order to prove negative
         betweenness statements as Schutz does. For example, if we have [abc]
         and [bca] we want to conclude [aba] and claim "contradiction!", but
         we can't as long as we mandate that a \<noteq> d. *)
      and abc_bcd_abd [intro]: "\<lbrakk>[[a b c]]; [[b c d]]\<rbrakk> \<Longrightarrow> [[a b d]]"
      (* O5, relaxed; exhausting all six options is not necessary thanks to abc_sym. *)
      and some_betw: "\<lbrakk>Q \<in> \<P>; a \<in> Q; b \<in> Q; c \<in> Q; a \<noteq> b; a \<noteq> c; b \<noteq> c\<rbrakk>
               \<Longrightarrow> [[a b c]] \<or> [[b c a]] \<or> [[c a b]]"
begin

(* The next few lemmas either provide the full axiom from the text derived from a new simpler
   statement, or provide some very simple fundamental additions which make sense to prove
   immediately before starting, usually related to set-level things that should be true which
   fix the type-level ambiguity of 'a. *)

lemma betw_events:
  assumes abc: "[[a b c]]"
  shows "a \<in> \<E> \<and> b \<in> \<E> \<and> c \<in> \<E>"
proof -
  have "\<exists>Q\<in>\<P>. a \<in> Q \<and> b \<in> Q \<and> c \<in> Q" using abc_ex_path abc by simp
  thus ?thesis using in_path_event by auto
qed

(* This shows the shorter version of O5 is equivalent. *)
lemma O5_still_O5 [no_atp]:
  "((Q \<in> \<P> \<and> {a,b,c} \<subseteq> Q \<and> a \<in> \<E> \<and> b \<in> \<E> \<and> c \<in> \<E> \<and> a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c)
     \<longrightarrow> [[a b c]] \<or> [[b c a]] \<or> [[c a b]])
   =
   ((Q \<in> \<P> \<and> {a,b,c} \<subseteq> Q \<and> a \<in> \<E> \<and> b \<in> \<E> \<and> c \<in> \<E> \<and> a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c)
     \<longrightarrow> [[a b c]] \<or> [[b c a]] \<or> [[c a b]] \<or> [[c b a]] \<or> [[a c b]] \<or> [[b a c]])"
by (auto simp add: abc_sym)

lemma some_betw_xor:
   "\<lbrakk>Q \<in> \<P>; a \<in> Q; b \<in> Q; c \<in> Q; a \<noteq> b; a \<noteq> c; b \<noteq> c\<rbrakk>
               \<Longrightarrow> ([[a b c]] \<and> \<not> [[b c a]] \<and> \<not> [[c a b]])
                 \<or> ([[b c a]] \<and> \<not> [[a b c]] \<and> \<not> [[c a b]])
                 \<or> ([[c a b]] \<and> \<not> [[a b c]] \<and> \<not> [[b c a]])"
by (meson abc_ac_neq abc_bcd_abd some_betw)

(* O3 *)
(* TODO give a structured proof for this. *)
lemma abc_abc_neq:
  assumes abc: "[[a b c]]"
  shows "a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c"
using abc_sym abc_ac_neq assms abc_bcd_abd by blast


lemma abc_bcd_acd:
  assumes abc: "[[a b c]]"
      and bcd: "[[b c d]]"
  shows "[[a c d]]"
proof -
  have cba: "[[c b a]]" using abc_sym abc by simp
  have dcb: "[[d c b]]" using abc_sym bcd by simp
  have "[[d c a]]" using abc_bcd_abd dcb cba by blast
  thus ?thesis using abc_sym by simp
qed

lemma abc_only_cba:
  assumes "[[a b c]]"
    shows "\<not> [[b a c]]" "\<not> [[a c b]]" "\<not> [[b c a]]" "\<not> [[c a b]]"
using abc_sym abc_abc_neq abc_bcd_abd assms by blast+

(* lemmas abc_only_cba1 = abc_only_cba [THEN conjunct1]
lemmas abc_only_cba2 = abc_only_cba [THEN conjunct2, THEN conjunct1]
lemmas abc_only_cba3 = abc_only_cba [THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas abc_only_cba4 = abc_only_cba [THEN conjunct2, THEN conjunct2, THEN conjunct2] *)


section "Betweenness: Unreachable Subset Via a Path"

definition unreachable_subset_via :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set"
                                     ("\<emptyset> _ from _ via _ at _" [100, 100, 100, 100] 100) where
  "unreachable_subset_via Q Qa R x \<equiv> {Qy. [[x Qy Qa]] \<and> (\<exists>Rw\<in>R. Qa \<in> \<emptyset> Q Rw \<and> Qy \<in> \<emptyset> Q Rw)}"



section "Betweenness: Chains"

subsection "Totally ordered chains with indexing"

definition short_ch :: "'a set \<Rightarrow> bool" where
  "short_ch X \<equiv>
    \<^cancel>\<open>EITHER two distinct events connected by a path\<close>
    \<exists>x\<in>X. \<exists>y\<in>X. path_ex x y \<and> \<not>(\<exists>z\<in>X. z\<noteq>x \<and> z\<noteq>y)" (*path_ex implies x\<noteq>y*)
    (* card X = 2 \<and> (\<forall>x\<in>X. \<forall>y\<in>X. x\<noteq>y \<longrightarrow> path_ex x y) *)

(* Infinite sets are weird with card, because card gives a natural number always. *)
definition long_ch_by_ord :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "long_ch_by_ord f X \<equiv>
    \<^cancel>\<open>OR at least three events such that any three events are ordered\<close>
    \<exists>x\<in>X. \<exists>y\<in>X. \<exists>z\<in>X. x\<noteq>y \<and> y\<noteq>z \<and> x\<noteq>z \<and> ordering f betw X"
    (* (card X \<ge> 3 \<or> infinite X) \<and> ordering f betw X" (* \<and> \<exists>P\<in>\<P>. X \<subseteq> P *) *)

(* Does this restrict chains to lie on paths? Proven in Ch3's Interlude! *)
definition ch_by_ord :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "ch_by_ord f X \<equiv> short_ch X \<or> long_ch_by_ord f X"

definition ch :: "'a set \<Rightarrow> bool" where
  "ch X \<equiv> \<exists>f. ch_by_ord f X"

(* Since f 0 is always in the chain, and plays a special role particularly for infinite chains
   (as the 'endpoint', the non-finite edge) let us fix it straight in the definition.
   Notice we require both infinite X AND long_ch_by_ord, thus circumventing infinite
   Isabelle sets having cardinality 0. *)
definition semifin_chain:: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" ("[_[_ ..]_]") where
  (* "semifin_chain f x Q \<equiv> infinite Q \<and> ordering f betw Q \<and> f 0 = x" *)
  "semifin_chain f x Q \<equiv>
    infinite Q \<and> long_ch_by_ord f Q
    \<and> f 0 = x"

definition fin_long_chain:: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool"
  ("[_[_ .. _ ..  _]_]") where
  (* "fin_long_chain f x y z Q \<equiv> ([f[x..z]Q] \<and> y\<in>Q)" (* card Q \<ge> 2 ? *) *)
  (* "fin_long_chain f x y z Q \<equiv> (card Q \<ge> 3 \<and> ordering f betw Q)" *)
  "fin_long_chain f x y z Q \<equiv>
    x\<noteq>y \<and> x\<noteq>z \<and> y\<noteq>z
    \<and> finite Q \<and> long_ch_by_ord f Q
    \<and> f 0 = x \<and> y\<in>Q \<and> f (card Q - 1) = z"

lemma index_middle_element:
  assumes "[f[a..b..c]X]"
  shows "\<exists>n. 0<n \<and> n<(card X - 1) \<and> f n = b"
proof -
  obtain n where n_def: "n < card X" "f n = b"
    by (metis TernaryOrdering.ordering_def assms fin_long_chain_def long_ch_by_ord_def)
  have "0<n \<and> n<(card X - 1) \<and> f n = b"
    using assms fin_long_chain_def n_def
    by (metis Suc_pred' gr_implies_not0 less_SucE not_gr_zero)
  thus ?thesis by blast
qed

lemma fin_ch_betw:
  assumes "[f[a..b..c]X]"
  shows "[[a b c]]"
proof -
  obtain nb where n_def: "nb\<noteq>0" "nb<card X - 1" "f nb = b"
    using assms index_middle_element by blast
  have "[[(f 0) (f nb) (f (card X - 1))]]"
    using fin_long_chain_def long_ch_by_ord_def assms n_def ordering_ord_ijk zero_less_iff_neq_zero
    by fastforce
  thus ?thesis using assms fin_long_chain_def n_def(3) by auto
qed

lemma chain_sym_obtain:
  assumes "[f[a..b..c]X]"
  obtains g where "[g[c..b..a]X]" and "g=(\<lambda>n. f (card X - 1 - n))"
using ordering_sym assms(1) unfolding fin_long_chain_def long_ch_by_ord_def
by (metis (mono_tags, lifting) abc_sym diff_self_eq_0 diff_zero)

lemma chain_sym:
  assumes "[f[a..b..c]X]"
    shows "[\<lambda>n. f (card X - 1 - n)[c..b..a]X]"
  using chain_sym_obtain [where f=f and a=a and b=b and c=c and X=X]
  using assms(1) by blast

(* This one is rarely used, if at all. But it gives a base for proving equivalence with the
   definition below, made and used extensively by Jake (I'm too lazy to redo all his proofs). *)
definition fin_long_chain_2:: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "fin_long_chain_2 x y z Q \<equiv> \<exists>f. [f[x..y..z]Q]"

definition fin_chain:: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" ("[_[_ .. _]_]") where
  "fin_chain f x y Q \<equiv>
    (short_ch Q \<and> x\<in>Q \<and> y\<in>Q \<and> x\<noteq>y)
    \<or> (\<exists>z\<in>Q. [f[x..z..y]Q])"
  (* "fin_chain f x y Q \<equiv> ch_by_ord f Q \<and> finite Q \<and> f 0 = x \<and> f (card Q - 1) = y" *)
  (* "fin_chain f x y Q \<equiv>
    (short_ch Q \<and> x\<in>Q \<and> y\<in>Q \<and> x\<noteq>y)
    \<or> (finite Q \<and> long_ch_by_ord f Q
      \<and> f 0 = x \<and> f (card Q - 1) = y)" *)

lemma points_in_chain:
  assumes "[f[x..y..z]Q]"
  shows "x\<in>Q \<and> y\<in>Q \<and> z\<in>Q"
proof -
  have "x\<in>Q"
    using ordering_def assms card_gt_0_iff emptyE fin_long_chain_def long_ch_by_ord_def
    by metis
  moreover have "y\<in>Q"
    using assms fin_long_chain_def
    by auto
  moreover have "z\<in>Q"
    using ordering_def assms card_gt_0_iff emptyE fin_long_chain_def long_ch_by_ord_def
    by (metis (no_types, hide_lams) Suc_diff_1 lessI)
  ultimately show ?thesis
    by blast
qed

lemma ch_long_if_card_ge3:
  assumes "ch X"
      and "card X \<ge> 3"
    shows "\<exists>f. long_ch_by_ord f X"
proof (rule ccontr)
  assume "\<nexists>f. long_ch_by_ord f X"
  hence "short_ch X"
    using assms(1) ch_by_ord_def ch_def
    by auto
  obtain x y z where "x\<in>X \<and> y\<in>X \<and> z\<in>X" and "x\<noteq>y \<and> y\<noteq>z \<and> x\<noteq>z"
    using assms(2)
    by (auto simp add: card_le_Suc_iff numeral_3_eq_3)
  thus False
    using \<open>short_ch X\<close> short_ch_def
    by metis
qed

subsection "Locally ordered chains with indexing"

(* Definition for Schutz-like chains, with local order only. *)
definition long_ch_by_ord2 :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "long_ch_by_ord2 f X \<equiv>
    \<exists>x\<in>X. \<exists>y\<in>X. \<exists>z\<in>X. x\<noteq>y \<and> y\<noteq>z \<and> x\<noteq>z \<and> ordering2 f betw X"

subsection "Chains using betweenness"

(* Old def of finite_chain_with3. Shown equivalent to fin_long_chain_2 in `Ch3.thy`. *)
definition chain_with :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" ("[[.. _ .. _ .. _ ..]_]") where
  "chain_with x y z X \<equiv> [[x y z]] \<and> x \<in> X \<and> y \<in> X \<and> z \<in> X \<and> (\<exists>f. ordering f betw X)"
definition finite_chain_with3 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" ("[[_ .. _ .. _]_]") where
  "finite_chain_with3 x y z X \<equiv> [[..x..y..z..]X] \<and> \<not>(\<exists>w\<in>X. [[w x y]] \<or> [[y z w]])"

lemma long_chain_betw: "[[..a..b..c..]X] \<Longrightarrow> [[a b c]]"
by (simp add: chain_with_def)

lemma finite_chain3_betw: "[[a..b..c]X] \<Longrightarrow> [[a b c]]"
by (simp add: chain_with_def finite_chain_with3_def)

(* old def - excludes 2-element chains *)
(* TODO Should it be "\<exists>y\<in>X. [[x y z]] \<or> [[y x z]] \<or> [[x z y]]"?
   Similarly for the other definitions. *)
definition finite_chain_with2 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" ("[[_ .. _]_]") where
  (* "finite_chain_with2 x z X \<equiv> x \<in> X \<and> z \<in> X \<and> (\<exists>f. ordering f betw X)
                                \<and> (\<exists>y\<in>X. [[x y z]]) \<and> \<not>(\<exists>w\<in>X. \<exists>w'\<in>X. [[w x w']] \<or> [[w z w']])" *)
  (* "finite_chain_with2 x z X \<equiv> x \<in> X \<and> z \<in> X \<and> (\<exists>f. ordering f betw X)
                                \<and> (\<exists>y\<in>X. [[x y z]] \<and> \<not>(\<exists>w\<in>X. [[w x y]] \<or> [[y z w]]))" *)
  "finite_chain_with2 x z X \<equiv> \<exists>y\<in>X. [[x..y..z]X]"

lemma finite_chain2_betw: "[[a..c]X] \<Longrightarrow> \<exists>b. [[a b c]]"
  using finite_chain_with2_def finite_chain3_betw by meson


section "Betweenness: Rays and Intervals"

(* "Given any two distinct events a,b of a path we define the segment
   (ab) := {x : [axb], x\<in>ab} [...]" [Schutz97] *)
(* Our version is a little different, because it is defined for any a b of type 'a.
   Thus we can have empty set segments, which Schutz cannot. *)
definition segment :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "segment a b \<equiv> {x::'a. \<exists>ab. [[a x b]] \<and> x\<in>ab \<and> path ab a b}"

abbreviation is_segment :: "'a set \<Rightarrow> bool"
  where "is_segment ab \<equiv> (\<exists>a b. ab = segment a b)" (*ab \<noteq> {} \<and> (\<exists>a b. ab = segment a b)*)

definition interval :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "interval a b \<equiv> insert b (insert a (segment a b))"

abbreviation is_interval :: "'a set \<Rightarrow> bool"
  where "is_interval ab \<equiv> (\<exists>a b. ab = interval a b)"

definition prolongation :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "prolongation a b \<equiv> {x::'a. \<exists>ab. [[a b x]] \<and> x\<in>ab \<and> path ab a b}"

abbreviation is_prolongation :: "'a set \<Rightarrow> bool"
  where "is_prolongation ab \<equiv> \<exists>a b. ab = prolongation a b"

(* I think this is what Schutz actually meant, maybe there is a typo in the text? *)
(* Notice that b \<in> ray a b for any a, always. Cf the comment on segment_def.
   Thus `\<exists>ray a b \<noteq> {}` is no guarantee that a path ab exists. *)
definition ray :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "ray a b \<equiv> insert b (segment a b \<union> prolongation a b)"

abbreviation is_ray :: "'a set \<Rightarrow> bool"
  where "is_ray R \<equiv> \<exists>a b. R = ray a b"

definition is_ray_on :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "is_ray_on R P \<equiv> P\<in>\<P> \<and> R\<subseteq>P \<and> is_ray R"

(* This is as in Schutz. Notice b is not in it? *)
definition ray_Schutz :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "ray_Schutz a b \<equiv> insert a (segment a b \<union> prolongation a b)"

lemma ends_notin_segment: "a \<notin> segment a b \<and> b \<notin> segment a b"
  using abc_abc_neq segment_def by fastforce

lemma ends_in_int: "a \<in> interval a b \<and> b \<in> interval a b"
  using interval_def by auto

lemma seg_betw: "x \<in> segment a b \<longleftrightarrow> [[a x b]]"
  using segment_def abc_abc_neq abc_ex_path by fastforce

lemma pro_betw: "x \<in> prolongation a b \<longleftrightarrow> [[a b x]]"
  using prolongation_def abc_abc_neq abc_ex_path by fastforce

lemma seg_sym: "segment a b = segment b a"
  using abc_sym segment_def by auto

lemma empty_segment: "segment a a = {}"
  by (simp add: segment_def)

lemma int_sym: "interval a b = interval b a"
  by (simp add: insert_commute interval_def seg_sym)

lemma seg_path:
  assumes "x \<in> segment a b" (* thus segment \<noteq> {} *)
  obtains ab where "path ab a b" "segment a b \<subseteq> ab"
proof -
  obtain ab where "path ab a b"
    using abc_abc_neq abc_ex_path assms seg_betw
    by meson
  have "segment a b \<subseteq> ab"
    using \<open>path ab a b\<close> abc_ex_path path_unique seg_betw
    by fastforce
  thus ?thesis
    using \<open>path ab a b\<close> that by blast
qed

lemma seg_path2:
  assumes "segment a b \<noteq> {}"
  obtains ab where "path ab a b" "segment a b \<subseteq> ab"
  using assms seg_path by force

(* Path density (theorem 17) will extend this to an assumption of `segment a b \<noteq> {}` *)
lemma seg_endpoints_on_path:
  assumes "card (segment a b) \<ge> 2" "segment a b \<subseteq> P" "P\<in>\<P>"
  shows "path P a b"
proof -
  have non_empty: "segment a b \<noteq> {}" using assms(1) numeral_2_eq_2 by auto
  then obtain ab where "path ab a b" "segment a b \<subseteq> ab"
    using seg_path2 by force
  have "a\<noteq>b" by (simp add: \<open>path ab a b\<close>)
  obtain x y where "x\<in>segment a b" "y\<in>segment a b" "x\<noteq>y"
    using assms(1) numeral_2_eq_2
    by (metis card.infinite card_le_Suc0_iff_eq not_less_eq_eq not_numeral_le_zero)
  have "[[a x b]]"
    using \<open>x \<in> segment a b\<close> seg_betw by auto
  have "[[a y b]]"
    using \<open>y \<in> segment a b\<close> seg_betw by auto
  have "x\<in>P \<and> y\<in>P"
    using \<open>x \<in> segment a b\<close> \<open>y \<in> segment a b\<close> assms(2) by blast
  have "x\<in>ab \<and> y\<in>ab"
    using \<open>segment a b \<subseteq> ab\<close> \<open>x \<in> segment a b\<close> \<open>y \<in> segment a b\<close> by blast
  have "ab=P"
    using \<open>path ab a b\<close> \<open>x \<in> P \<and> y \<in> P\<close> \<open>x \<in> ab \<and> y \<in> ab\<close> \<open>x \<noteq> y\<close> assms(3) path_unique by auto
  thus ?thesis
    using \<open>path ab a b\<close> by auto
qed

lemma pro_path:
  assumes "x \<in> prolongation a b" (* thus prolongation \<noteq> {} *)
  obtains ab where "path ab a b" "prolongation a b \<subseteq> ab"
proof -
  obtain ab where "path ab a b"
    using abc_abc_neq abc_ex_path assms pro_betw
    by meson
  have "prolongation a b \<subseteq> ab"
    using \<open>path ab a b\<close> abc_ex_path path_unique pro_betw
    by fastforce
  thus ?thesis
    using \<open>path ab a b\<close> that by blast
qed

lemma ray_cases:
  assumes "x \<in> ray a b"
  shows "[[a x b]] \<or> [[a b x]] \<or> x = b"
proof -
  have "x\<in>segment a b \<or> x\<in> prolongation a b \<or> x=b"
    using assms ray_def by auto
  thus "[[a x b]] \<or> [[a b x]] \<or> x = b"
    using pro_betw seg_betw by auto
qed

lemma ray_path:
  assumes "x \<in> ray a b" "x\<noteq>b"
  obtains ab where "path ab a b \<and> ray a b \<subseteq> ab"
proof -
  let ?r = "ray a b"
  have "?r \<noteq> {b}"
    using assms by blast
  have "\<exists>ab. path ab a b \<and> ray a b \<subseteq> ab"
  proof -
    have betw_cases: "[[a x b]] \<or> [[a b x]]" using ray_cases assms
      by blast
    then obtain ab where "path ab a b"
      using abc_abc_neq abc_ex_path by blast
    have "?r \<subseteq> ab" using betw_cases
    proof (rule disjE)
      assume "[[a x b]]"
      show "?r \<subseteq> ab"
      proof
        fix x assume "x\<in>?r"
        show "x\<in>ab"
          by (metis \<open>path ab a b\<close> \<open>x \<in> ray a b\<close> abc_ex_path eq_paths ray_cases)
      qed
    next assume "[[a b x]]"
      show "?r \<subseteq> ab"
      proof
        fix x assume "x\<in>?r"
        show "x\<in>ab"
          by (metis \<open>path ab a b\<close> \<open>x \<in> ray a b\<close> abc_ex_path eq_paths ray_cases)
      qed
    qed
    thus ?thesis
      using \<open>path ab a b\<close> by blast
  qed
  thus ?thesis
    using that by blast
qed

end (* MinkowskiBetweenness *)

section "MinkowskiChain: O6"

locale MinkowskiChain = MinkowskiBetweenness +
  (* O6 supposedly serves the same purpose as Pasch's axiom. *)
  assumes O6: "\<lbrakk>Q \<in> \<P>; R \<in> \<P>; S \<in> \<P>; T \<in> \<P>; Q \<noteq> R; Q \<noteq> S; R \<noteq> S; a \<in> Q\<inter>R \<and> b \<in> Q\<inter>S \<and> c \<in> R\<inter>S;
                \<exists>d\<in>S. [[b c d]] \<and> (\<exists>e\<in>R. d \<in> T \<and> e \<in> T \<and> [[c e a]])\<rbrakk>
               \<Longrightarrow> \<exists>f\<in>T\<inter>Q. \<exists>X. [[a..f..b]X]"
  (* assumes O6: "\<lbrakk>Q \<in> \<P>; R \<in> \<P>; S \<in> \<P>; T \<in> \<P>; Q \<noteq> R; Q \<noteq> S; R \<noteq> S; a \<in> Q\<inter>R \<and> b \<in> Q\<inter>S \<and> c \<in> R\<inter>S;
                \<exists>d\<in>S. [[b c d]] \<and> (\<exists>e\<in>R. d \<in> T \<and> e \<in> T \<and> [[c e a]])\<rbrakk>
               \<Longrightarrow> \<exists>f\<in>T\<inter>Q. \<exists>X. \<exists>g. [g[a..f..b]X]" *)
begin


section "Chains: (Closest) Bounds"

definition is_bound_f :: "'a \<Rightarrow> 'a set \<Rightarrow> (nat\<Rightarrow>'a) \<Rightarrow> bool" where
  "is_bound_f Q\<^sub>b Q f \<equiv>
    \<forall>i j ::nat. [f[(f 0)..]Q] \<and> (i<j \<longrightarrow> [[(f i) (f j) Q\<^sub>b]])"


definition is_bound :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_bound Q\<^sub>b Q \<equiv>
    \<exists>f::(nat\<Rightarrow>'a). is_bound_f Q\<^sub>b Q f"

(* Q\<^sub>b has to be on the same path as the chain Q.
   This is left implicit in the betweenness condition (as is Q\<^sub>b\<in>\<E>).
   So this is equivalent to Schutz only if we also assume his axioms,
   i.e. the statement of the continuity axiom is no longer independent of other axioms. *)

(*ALTERNATIVE: "is_bound Q\<^sub>b Q \<equiv>
  \<forall>i::nat. \<forall>j::nat. \<exists>f::(nat\<Rightarrow>'a). \<exists>Q\<^sub>0\<in>Q.
  [f[Q\<^sub>0..]Q] \<and> (i<j \<longrightarrow> [[(f i) (f j) Q\<^sub>b]])" *)


definition all_bounds :: "'a set \<Rightarrow> 'a set" where
  "all_bounds Q = {Q\<^sub>b. is_bound Q\<^sub>b Q}"


definition bounded :: "'a set \<Rightarrow> bool" where
  "bounded Q \<equiv> \<exists> Q\<^sub>b. is_bound Q\<^sub>b Q"
  (* "bounded Q \<equiv> \<exists> Q\<^sub>b\<in>\<E>. is_bound Q\<^sub>b Q" *)


(* Just to make sure Continuity is not too strong. *)
lemma bounded_imp_inf:
  assumes "bounded Q"
  shows "infinite Q"
  using assms bounded_def is_bound_def is_bound_f_def semifin_chain_def by blast


definition closest_bound_f :: "'a \<Rightarrow> 'a set \<Rightarrow> (nat\<Rightarrow>'a) \<Rightarrow> bool" where
  "closest_bound_f Q\<^sub>b Q f \<equiv>
\<^cancel>\<open>Q is an infinite chain indexed by f bound by Q\<^sub>b\<close>
    is_bound_f Q\<^sub>b Q f \<and>
\<^cancel>\<open>Any other bound must be further from the start of the chain than the closest bound\<close>
    (\<forall> Q\<^sub>b'. (is_bound Q\<^sub>b' Q \<and> Q\<^sub>b' \<noteq> Q\<^sub>b) \<longrightarrow> [[(f 0) Q\<^sub>b Q\<^sub>b']])"


definition closest_bound :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "closest_bound Q\<^sub>b Q \<equiv>
\<^cancel>\<open>Q is an infinite chain indexed by f bound by Q\<^sub>b\<close>
    \<exists>f. is_bound_f Q\<^sub>b Q f \<and>
\<^cancel>\<open>Any other bound must be further from the start of the chain than the closest bound\<close>
    (\<forall> Q\<^sub>b'. (is_bound Q\<^sub>b' Q \<and> Q\<^sub>b' \<noteq> Q\<^sub>b) \<longrightarrow> [[(f 0) Q\<^sub>b Q\<^sub>b']])"

end (*MinkowskiChain*)

section "MinkowskiUnreachable: I5-I7"

locale MinkowskiUnreachable = MinkowskiChain +
  (* I5 *)
  assumes two_in_unreach: "\<lbrakk>Q \<in> \<P>; b \<in> \<E>; b \<notin> Q\<rbrakk> \<Longrightarrow> \<exists>x\<in>\<emptyset> Q b. \<exists>y\<in>\<emptyset> Q b. x \<noteq> y"

  (* Look in the book for the definition of I6 there. It's much nicer, because I felt here I
     had to capture the ordering f in order to talk about such things as "event at position i",
     which can't be got at without some serious fudgery otherwise. I'm sure there's a better way. *)

(* TODO replace chain_by_ord with long_ch_by_ord?
   replace explicit defn with [f[Qx..Qz]X], which has no support for f in the case of short_ch X?
   replace short_ch to have support for a trivial f (i.e. f 0 = a \<and> f 1 = b or rev)? *)
      (* and I6: "\<lbrakk>Q \<in> \<P>; b \<notin> Q; b \<in> \<E>; Qx \<in> (\<emptyset> Q b); Qz \<in> (\<emptyset> Q b); Qx\<noteq>Qz\<rbrakk>
               \<Longrightarrow> \<exists>X. \<exists>f. [f[Qx..Qz]X]
                         \<and> (\<forall>i\<in>{1 .. card X - 1}. (f i) \<in> \<emptyset> Q b
                            \<and> (\<forall>Qy\<in>\<E>. [[(f(i-1)) Qy (f i)]] \<longrightarrow> Qy \<in> \<emptyset> Q b))
                         \<and> (short_ch X \<longrightarrow> Qx\<in>X \<and> Qz\<in>X \<and> (\<forall>Qy\<in>\<E>. [[Qx Qy Qz]] \<longrightarrow> Qy \<in> \<emptyset> Q b))" *)
      and I6: "\<lbrakk>Q \<in> \<P>; b \<notin> Q; b \<in> \<E>; Qx \<in> (\<emptyset> Q b); Qz \<in> (\<emptyset> Q b); Qx\<noteq>Qz\<rbrakk>
               \<Longrightarrow> \<exists>X. \<exists>f. ch_by_ord f X \<and> f 0 = Qx \<and> f (card X - 1) = Qz
                         \<and> (\<forall>i\<in>{1 .. card X - 1}. (f i) \<in> \<emptyset> Q b
                              \<and> (\<forall>Qy\<in>\<E>. [[(f(i-1)) Qy (f i)]] \<longrightarrow> Qy \<in> \<emptyset> Q b))
                         \<and> (short_ch X \<longrightarrow> Qx\<in>X \<and> Qz\<in>X \<and> (\<forall>Qy\<in>\<E>. [[Qx Qy Qz]] \<longrightarrow> Qy \<in> \<emptyset> Q b))"
      (* and I6: "\<lbrakk>Q \<in> \<P>; b \<notin> Q; b \<in> \<E>; Qx \<in> \<emptyset> Q b; Qz \<in> \<emptyset> Q b\<rbrakk>
               \<Longrightarrow> \<exists>X f. ch_by_ordering f X \<and> f 0 = Q0 \<and> f (card X - 1) = Qn \<and> Q0 = Qx \<and> Qn = Qz
                         \<and> (\<forall>i\<in>{1 .. card X - 1}. f i \<in> \<emptyset> Q b
                              \<and> (\<forall>Qy\<in>Q. [[(f (i - 1)) Qy (f i)]] \<longrightarrow> Qy \<in> \<emptyset> Q b))" *)
      (* Does this really provide boundedness? If the unreachable set is the whole path, then you
         can't pick some Qx outside of it. *)
      (* and I7: "\<lbrakk>Q \<in> \<P>; b \<notin> Q; b \<in> \<E>; Qx \<in> Q - \<emptyset> Q b; Qy \<in> \<emptyset> Q b\<rbrakk>
               \<Longrightarrow> \<exists>X Q0 Qm Qn. [[Q0..Qm..Qn]X] \<and> Q0 = Qx \<and> Qm = Qy \<and> Qn \<in> Q - \<emptyset> Q b" *)
      and I7: "\<lbrakk>Q \<in> \<P>; b \<notin> Q; b \<in> \<E>; Qx \<in> Q - \<emptyset> Q b; Qy \<in> \<emptyset> Q b\<rbrakk>
               \<Longrightarrow> \<exists>g X Qn. [g[Qx..Qy..Qn]X] \<and> Qn \<in> Q - \<emptyset> Q b"
begin

lemma card_unreach_geq_2:
  assumes "Q\<in>\<P>" "b\<in>\<E>-Q"
  shows "2 \<le> card (\<emptyset> Q b) \<or> (infinite (\<emptyset> Q b))"
  using DiffD1 assms(1) assms(2) card_le_Suc0_iff_eq two_in_unreach by fastforce

end

section "MinkowskiSymmetry: Symmetry"

locale MinkowskiSymmetry = MinkowskiUnreachable +
      (* Finding this a bit difficult. Not sure how to constrain \<theta> and \<Theta> to just \<E> and \<P>,
         nor what it means to say that the events of Q are invariant, or to just state
         \<Theta> : R \<Rightarrow> S. I guess the latter means "therefore \<Theta> maps R to S." *)
      (* What I really want to do for the Symmetry axiom, I think, is state that the bijection
         \<Theta> induced by \<theta> must be from the (family of) \<theta> that maps all events belonging to
         the same path only to events in one other path, and no two events coming from different
         paths can map into one path (because no two paths can map to one path, as \<Theta> is injective).
         And whatever else needs to be true about \<theta> for it to be the kind of mapping which does
         generate a bijective \<Theta>.
         Or should I just say there's a \<theta> which makes a bijection \<Theta> and prove more about it
         later, if that is even possible? *)
      (* I haven't yet included part (iii) or (iv) of the statement. *)
      (* The way I've stated the properties of \<theta> and what that means for \<Theta> is wrong,
         but it's a preliminary thing so I can get off the ground with this one. *)
 (* assumes S: "\<lbrakk>Q \<in> \<P>; R \<in> \<P>; S \<in> \<P>; Q \<noteq> R; Q \<noteq> S; R \<noteq> S; x \<in> Q\<inter>R\<inter>S; Qa \<in> Q; Qa \<noteq> x;
              \<emptyset> Q from Qa via R at x = \<emptyset> Q from Qa via S at x\<rbrakk>
              \<Longrightarrow> \<exists>\<theta>::'a \<Rightarrow> 'a. \<exists>\<Theta>::'a set \<Rightarrow> 'a set.
                      bij \<Theta> \<and> \<Theta> R = S
                      \<^cancel>\<open>Distinct events from distinct paths map to distinct paths.\<close>
                      \<and> (\<forall>e1\<in>\<E>. \<forall>e2\<in>\<E>. e1 \<noteq> e2 \<and> p1 \<in> \<P> \<and> e1 \<in> p1 \<and> p2 \<in> \<P> \<and> e2 \<in> p2 \<and> p1 \<noteq> p2
                                        \<and> \<theta> e1 = a \<and> a \<in> p3 \<and> p3 \<in> \<P> \<and> \<theta> e2 = b \<and> b \<in> p4 \<and> p4 \<in> \<P>
                         \<longrightarrow> p3 \<noteq> p4 \<and> \<Theta> p1 = p3 \<and> \<Theta> p2 = p4)
                      \<^cancel>\<open>Distinct events from the same path map to the same path\<close>
                      \<and> (\<forall>e1\<in>\<E>. \<forall>e2\<in>\<E>. e1 \<noteq> e2 \<and> p \<in> \<P> \<and> e1 \<in> p \<and> e2 \<in> p
                                        \<and> \<theta> e1 = a \<and> a \<in> p1 \<and> p1 \<in> \<P> \<and> \<theta> e2 = b \<and> b \<in> p2 \<and> p2 \<in> \<P>
                         \<longrightarrow> p1 = p2 \<and> \<Theta> p = p1)" *)
  assumes Symmetry: "\<lbrakk>Q \<in> \<P>; R \<in> \<P>; S \<in> \<P>; Q \<noteq> R; Q \<noteq> S; R \<noteq> S;
               x \<in> Q\<inter>R\<inter>S; Q\<^sub>a \<in> Q; Q\<^sub>a \<noteq> x;
\<^cancel>\<open>the above could all be stated as Q R S \<in> SPRAY x - better? worse?\<close>
               \<emptyset> Q from Q\<^sub>a via R at x = \<emptyset> Q from Q\<^sub>a via S at x\<rbrakk>
               \<Longrightarrow> \<exists>\<theta>::'a\<Rightarrow>'a.                               \<^cancel>\<open>i) there is a map \<theta>:\<E>\<Rightarrow>\<E>\<close>
                     \<^cancel>\<open>bij (\<lambda>P. {z. y\<in>P \<and> (z = \<theta> y)})         \<^cancel>\<open>ii) which induces a bijection \<Theta>\<close>\<close>
                     bij_betw (\<lambda>P. {\<theta> y | y. y\<in>P}) \<P> \<P>
                     \<and> (y\<in>Q \<longrightarrow> \<theta> y = y)                    \<^cancel>\<open>iii) \<theta> leaves Q invariant\<close>
                     \<and> (\<lambda>P. {\<theta> y | y. y\<in>P}) R = S     \<^cancel>\<open>iv) \<Theta> maps R to S\<close>
\<^cancel>\<open>needs extra statement to ensure \<Theta> T is a path for any path T - I doubt it's automatic.\<close>
\<^cancel>\<open>TODO is it automatic for \<theta> that 'a\<Rightarrow>'a \<longleftrightarrow> \<E>\<Rightarrow>\<E> ?\<close>
                     \<^cancel>\<open>\<and> (T\<in>\<P> \<longrightarrow> (\<lambda>P. {z. y\<in>P \<and> (z = \<theta> y)}) T \<in>\<P>)\<close>"


section "MinkowskiContinuity: Continuity"

locale MinkowskiContinuity = MinkowskiSymmetry +
  assumes Continuity: "bounded Q \<Longrightarrow> (\<exists>Q\<^sub>b. closest_bound Q\<^sub>b Q)"
  (* assumes Continuity: "(infinite Q \<and> ch Q \<and> bounded Q) \<longrightarrow> (\<exists>Q\<^sub>b. closest_bound Q\<^sub>b Q)" *)



section "MinkowskiSpacetime: Dimension (I4)"

locale MinkowskiSpacetime = MinkowskiContinuity +
  (* I4 *)
  (* I've omitted the antecedent "\<E> \<noteq> {}" as this is already an axiom, and then omitting it
     proves the omitted axiom. *)
  assumes ex_3SPRAY [simp]: "\<lbrakk>\<E> \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>x\<in>\<E>. three_SPRAY x"
  (* assumes ex_3SPRAY [simp]: "\<exists>x\<in>\<E>. three_SPRAY x" *)
begin

(* substitute for I1, if I1 is omitted *)
(* lemma nonempty_events:
  "\<E> \<noteq> {}"
using ex_3SPRAY by blast *)

(* There exists an event by nonempty_events, and by ex_3SPRAY there is a three-SPRAY, which by
   three_SPRAY_ge4 means that there are at least four paths. *)
lemma four_paths:
  "\<exists>Q1\<in>\<P>. \<exists>Q2\<in>\<P>. \<exists>Q3\<in>\<P>. \<exists>Q4\<in>\<P>. Q1 \<noteq> Q2 \<and> Q1 \<noteq> Q3 \<and> Q1 \<noteq> Q4 \<and> Q2 \<noteq> Q3 \<and> Q2 \<noteq> Q4 \<and> Q3 \<noteq> Q4"
using nonempty_events ex_3SPRAY three_SPRAY_ge4 by blast

end

end
