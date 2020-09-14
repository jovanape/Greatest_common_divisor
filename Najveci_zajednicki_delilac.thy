theory Najveci_zajednicki_delilac
  imports Main begin

fun gcd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "gcd m n = (if n = 0 then m else gcd n (m mod n))"

(*
   U daljim dokazima, gde je bilo potrebno nesto dokazati preko indukcije,
   lakse mi je bilo da to dokazem koristeci funkciju gcd_prim,
   zbog toga imam dve funkcije koje rade istu stvar.
*)

fun gcd_prim :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "gcd_prim m 0 = m" |
  "gcd_prim m n = gcd_prim n (m mod n)"

(* Euklidov algoritam *)

(* gcd za n = 0 i n > 0*)
lemma gcd_0 [simp]: "gcd m 0 = m"
  using gcd.simps(1)
  by simp

lemma gcd_ne_0 [simp]: "0 < n \<Longrightarrow> gcd m n = gcd n (m mod n)"
  using gcd.simps
  by simp

declare gcd.simps [simp del]

(* Dokaz da broj koji deli m i deli n, deli i njihov nzd  *)
lemma deli_oba_deli_gcd: "\<forall> d. d dvd m \<and> d dvd n \<longrightarrow> d dvd (gcd_prim m n)"
proof (induction m n rule: gcd_prim.induct)
  case (1 m) (* \<forall>d. d dvd m \<and> d dvd 0 \<longrightarrow> d dvd gcd_prim m 0 *)
  then show ?case
  proof (cases "n = 0")
    case True
    then show ?thesis
      using gcd_prim.simps(1)
      by simp
  next
    case False
    then show ?thesis
      using gcd_prim.simps(2)
      by simp
  qed
next
  case (2 m v)
 then show ?case (*d dvd Suc v \<and> d dvd m mod Suc v \<longrightarrow> d dvd gcd_prim (Suc v) (m mod Suc v) *)
   by (simp add: dvd_mod)
qed

thm dvd_mod (* ako neki broj deli m i n, deli i njihov ostatak *)
thm dvd_mod_imp_dvd (* ako neki broj deli ostatak od a i b i deli b, deli i a*)

(* Dokaz da gcd m n deli i m i n *)
lemma gcd_deli_oba [simp]: "(gcd m n) dvd m \<and> (gcd m n) dvd n"
proof(induction m n rule: gcd_prim.induct)
    case (1 m)  (* (nzd m 0) dvd m \<and> (nzd m 0) dvd 0, a imamo "nzd m 0 = m" iz fun nzd \<Rightarrow> m dvd m \<and> m dvd 0 *)
    then show ?case by simp
  next
    case (2 m v)
    then show ?case using dvd_mod_imp_dvd by auto
  qed

  thm gcd_dvd1 (* gcd a b deli a*)

lemmas gcd_dvd1 [iff] = gcd_deli_oba [THEN conjunct1] (* gcd m n deli m *)
lemmas gcd_dvd2 [iff] = gcd_deli_oba [THEN conjunct2] (* gcd m n deli n *)


(* Maksimalnost: "Za sve m, n, d, ako d deli m i ako d deli n onda d deli njihov nzd." *)
lemma gcd_najveci_zajednicki_prim [rule_format]:  "d dvd m \<longrightarrow> d dvd n \<longrightarrow> d dvd (gcd_prim m n)"
proof (induction m n rule: gcd_prim.induct)
  case (1 m)
  then show ?case
  proof (cases "n = 0")
    case True
    then show ?thesis
      using gcd_prim.simps(1)
      by simp
  next
    case False
    then show ?thesis
      using gcd_prim.simps(2)
      by simp
  qed
next
  case (2 m v)
 then show ?case (* \<forall>d. d dvd Suc v \<and> d dvd m mod Suc v \<longrightarrow> d dvd gcd_prim (Suc v) (m mod Suc v) *)
   by (simp_all add: dvd_mod)
qed

(*
Termovi se formiraju primenom funkcija na argumente.
Kada na dva terma t1-->t2 primenimo funkciju f, dobijamo f(t1) --> f(t2).

Isabelle moze da razlikuje slucajeve zasnovane na termovima pomocu: apply (case_tac <term>).

Tako i u dokazu naredne leme, kada kazemo apply (case_tac "n=0"), Isabelle deli na dva slucaja
u zavisnosti od toga da li je n = 0 ili n \<noteq> 0:
1. n = 0 \<Longrightarrow> d dvd m \<longrightarrow> d dvd n \<longrightarrow> d dvd gcd m n
2. n \<noteq> 0 \<Longrightarrow> d dvd m \<longrightarrow> d dvd n \<longrightarrow> d dvd gcd m n

dvd_mod - ako k deli m i k deli n, onda k deli i njihov ostatak (tj. m mod n)
*)

(*
Sledeca lema je kao prethodna, ali dokazana na drugi nacin, da bi mogla gcd_najveci_zajednicki_iff da se dok.
Iz predhodne se jasnije vidi dokaz, pa sam je zato ostavila.
*)

(* Maksimalnost: "Za sve m, n, d, ako d deli m i ako d deli n onda d deli njihov nzd." *)
lemma gcd_najveci_zajednicki [rule_format]: "d dvd m \<longrightarrow> d dvd n \<longrightarrow> d dvd gcd m n"
apply (induct_tac m n rule: gcd.induct)
apply (case_tac "n=0")
apply (simp_all add: dvd_mod)
  done

(* Broj koji deli gcd m n, deli m i deli n *)
theorem gcd_najveci_zajednicki_iff [iff]: "(k dvd gcd m n) = (k dvd m \<and> k dvd n)"
  sledgehammer
  by (meson Najveci_zajednicki_delilac.gcd_dvd1 Najveci_zajednicki_delilac.gcd_dvd2 Najveci_zajednicki_delilac.gcd_najveci_zajednicki gcd_nat.trans)

definition is_gcd :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
    "is_gcd p m n == (p dvd m)  \<and>  (p dvd n)  \<and>  (\<forall> d. d dvd m \<and> d dvd n \<longrightarrow> d dvd p)"

(* Funkcija gcd daje najveci zajednicki delilac *)
lemma euklid_nzd_is_gcd:
  shows "is_gcd (gcd m n) m n"
(* Znaci ovo treba pokazati:
"((gcd m n) dvd m) \<and> ((gcd m n) dvd n) \<and> (\<forall>d. d dvd m \<and> d dvd n \<longrightarrow> d dvd (gcd m n))" *)
proof -
  have "(gcd m n) dvd m \<and> (gcd m n) dvd n"
    using gcd_deli_oba by simp
  also have "\<forall>d. d dvd m \<and> d dvd n \<longrightarrow> d dvd (gcd m n)"
    using gcd_deli_oba by simp
 ultimately show "is_gcd (gcd m n) m n"
    by (simp add: is_gcd_def)
qed

value "euklid_nzd_is_gcd 3 3 27"

(* Drugi nacin *)
lemma is_gcd: "is_gcd (gcd m n) m n"
apply (simp add: is_gcd_def gcd_najveci_zajednicki)
  done

(* Jedinstvenost nzd *)
lemma gcd_jedinstven: "is_gcd m a b \<Longrightarrow> is_gcd n a b \<Longrightarrow> m = n" (* za a i b postoji jedinstven nzd m = n *)
apply (simp add: is_gcd_def)
apply (blast intro: dvd_antisym)
  done

(* Asocijativnost nzd *)
lemma gcd_asocijativnost: "gcd (gcd k m) n = gcd k (gcd m n)"
  apply (rule gcd_jedinstven)
  apply (rule is_gcd)
  apply (simp add: is_gcd_def)
  apply (blast intro: dvd_trans)
  done

thm dvd_trans

lemma bezuov_stav [simp]:
  assumes ex: "\<exists>(d::nat) x y. d dvd a \<and> d dvd b \<and> (a * x = b * y + d \<or> b * x = a * y + d)"
  shows "\<exists>d x y. d dvd a \<and> d dvd a + b \<and> (a * x = (a + b) * y + d \<or> (a + b) * x = a * y + d)"
  using ex
 (*
 sledgehammer
  by (metis add.left_neutral bezout_add_strong_nat gcd_nat.extremum gcd_nat.refl mult.right_neutral mult_0)
*)
  apply clarsimp
  apply (rule_tac x="d" in exI, simp)
  apply (case_tac "a * x = b * y + d", simp_all)
  apply (rule_tac x="x + y" in exI)
  apply (rule_tac x="y" in exI)
  apply algebra
  apply (rule_tac x="x" in exI)
  apply (rule_tac x="x + y" in exI)
  apply algebra
  done

lemma pomocna:
  assumes "is_gcd d a b"
  shows "\<exists>m n. m*a + n*b = d"
  sorry

lemma pomocna_obrnuto:
  assumes "\<exists>m n. m*a + n*b = d"
  shows "is_gcd d a b"
  sorry


(* Dokaz da je nzd (a/d, b/d) = 1, ako su a, b > 0 i d = nzd(a, b). *)
lemma
  fixes d::nat
  assumes "0 < a \<and> 0 < b \<and> is_gcd d a b"
  shows "is_gcd 1 (a div d) (b div d)"
proof-
  have "(gcd a b) dvd a \<and> (gcd a b) dvd b"
          unfolding gcd_deli_oba
          by simp
        hence "\<exists>m n. m*a + n*b = d"
          unfolding pomocna
          using assms pomocna by auto
        hence "\<exists>m n. m*(a div d) + n*(b div d) = 1" sorry
(*          unfolding pomocna
          sledgehammer
          by (metis Euclidean_Division.div_eq_0_iff Nat.add_0_right One_nat_def add.commute add.left_neutral add_Suc_right add_cancel_left_right add_less_cancel_left add_mult_distrib2 assms div_mult_self1_is_m div_mult_self_is_m dividend_less_div_times dividend_less_times_div dvd_add_times_triv_left_iff dvd_add_triv_right_iff dvd_mult_div_cancel dvd_refl gcd_nat.trans is_gcd_def less_add_same_cancel1 mult.assoc mult.commute mult.left_commute mult_0_right mult_cancel1 mult_is_0 mult_zero_right nat.simps(3) nat_0_less_mult_iff nat_add_right_cancel nat_dvd_not_less nat_mult_1 nat_mult_1_right nat_mult_eq_1_iff nat_neq_iff neq0_conv not_less0 plus_nat.add_0 plus_nat.simps(2))
  *)     
        hence "is_gcd 1 (a div d) (b div d)"
          unfolding pomocna_obrnuto
          using pomocna_obrnuto by simp
  thus ?thesis
          by simp
qed

(* definicija *)

abbreviation uzajamno_prosti where
  "uzajamno_prosti x y \<equiv> is_gcd 1 x y"

lemma 
  fixes n a b :: nat
  assumes "is_gcd 1 a b"
  shows "is_gcd 1 (a*a) (b*b)"
proof-
  have "\<exists>m n. m*a + n*b = 1"
    unfolding pomocna
    using assms pomocna by simp
  hence "\<exists>m n. m*a = 1 - n*b"
    sledgehammer
    by (metis add_diff_cancel_right')
  hence "\<exists>m n. (m*a)^2  = (1 - n*b)^2"
    by simp
  hence "\<exists>m n. m^2 * a^2  = 1 - 2*n*b + n^2*b^2"
    by (metis (no_types, lifting) Suc_1 even_add even_plus_one_iff gcd_jedinstven mult_2 numeral_One one_add_one one_power2 pomocna_obrnuto power_add_numeral power_one_right semiring_norm(2))
  hence "\<exists>m n. 2*n*b - n^2*b^2 = 1 - m^2 * a^2"
       by (metis Suc_eq_plus1 add_cancel_left_left add_cancel_right_left assms id_apply gcd_jedinstven mult_eq_0_iff nat_1_eq_mult_iff of_nat_eq_id pomocna_obrnuto semiring_1_class.of_nat_simps(2) semiring_normalization_rules(4) zero_neq_one)
     hence "\<exists>m n. b^2 * (2*n - n^2*b)^2 = (1 - m^2 * a^2)^2"
       by (metis Suc_eq_plus1 add_cancel_left_left add_cancel_right_left assms id_apply gcd_jedinstven mult_eq_0_iff nat_1_eq_mult_iff of_nat_eq_id pomocna_obrnuto semiring_1_class.of_nat_simps(2) semiring_normalization_rules(4) zero_neq_one)
     hence "\<exists>m n. b^2 * (2*n - n^2*b)^2 = 1 - a * m^2 * a^2 + m^4 * a^4"
       by (metis Suc_eq_plus1 add_cancel_left_left add_cancel_right_left assms id_apply gcd_jedinstven mult_eq_0_iff nat_1_eq_mult_iff of_nat_eq_id pomocna_obrnuto semiring_1_class.of_nat_simps(2) semiring_normalization_rules(4) zero_neq_one)
     hence "\<exists>m n. b^2 * (2*n - n^2*b)^2 + a * m^2 * a^2 - m^4 * a^4 = 1"
       by (metis Suc_eq_plus1 add_cancel_left_left add_cancel_right_left assms id_apply gcd_jedinstven mult_eq_0_iff nat_1_eq_mult_iff of_nat_eq_id pomocna_obrnuto semiring_1_class.of_nat_simps(2) semiring_normalization_rules(4) zero_neq_one)
     hence "\<exists>m n. b^2 * (2*n - n^2*b)^2 + a^2 * (a * m^2 - m^4 * a^2) = 1"
       by (metis Suc_eq_plus1 add_cancel_left_left add_cancel_right_left assms id_apply gcd_jedinstven mult_eq_0_iff nat_1_eq_mult_iff of_nat_eq_id pomocna_obrnuto semiring_1_class.of_nat_simps(2) semiring_normalization_rules(4) zero_neq_one)
     hence "is_gcd 1 (a^2) (b^2)"
       by (metis Suc_eq_plus1 add_cancel_left_left add_cancel_right_left assms id_apply gcd_jedinstven mult_eq_0_iff nat_1_eq_mult_iff of_nat_eq_id pomocna_obrnuto semiring_1_class.of_nat_simps(2) semiring_normalization_rules(4) zero_neq_one)
     thus ?thesis
       by (simp add: semiring_normalization_rules(29))
   qed

(* Ako je gcd(a,n) = 1 \<and> gcd(b,n) = 1, onda je gcd(ab,n) = 1. *)
lemma
  assumes "is_gcd 1 a n \<and> is_gcd 1 b n"
  shows "is_gcd 1 (a*b) n"
proof-
  have *: "\<exists> x y. a*x + n*y = 1"
    unfolding pomocna
    by (metis assms mult.commute pomocna)
  have **: "\<exists> z w. b*z + n*w = 1"
    by (metis assms mult.commute pomocna)
  hence "\<exists> x y z w. (a*x + n*y) * (b*z + n*w) = 1 * 1"
  using "*" "**" by auto
  hence "\<exists> x y z w. a*b*x*z + a*x*n*w + b*z*n*y + (n^2)*y*w = 1 * 1"
  by (metis One_nat_def even_plus_one_iff is_gcd_def mult_eq_1_iff one_add_one pomocna_obrnuto)
  hence "\<exists> x y z w. a*b*(x*z) + n*(a*x*w + b*z*y + n*y*w) = 1"
    by (metis even_plus_one_iff is_gcd_def nat_1_eq_mult_iff one_add_one pomocna_obrnuto)
  hence "is_gcd 1 (a*b) n"
    by (metis mult.commute pomocna_obrnuto)
     thus ?thesis
       by simp
   qed



lemma
  fixes n a b :: nat
  assumes "a dvd (b*c) \<and> is_gcd 1 a b"
  shows "a dvd c"
proof-
  have "\<exists> x y. a*x + b*y = 1"
    by (metis assms mult.commute pomocna)
  have *: "\<exists> x y. a*x*c + b*y*c = 1*c"
    by (metis \<open>\<exists>x y. a * x + b * y = 1\<close> add_mult_distrib nat_mult_1)
  hence "\<exists> x. a dvd a*c*x \<and> a dvd b*c"
    by (simp add: assms)
  hence "\<exists> x y. a dvd b*c*y"
    by simp
  hence "\<exists> x y. a dvd (a*c*x + b*c*y)"
    by (metis add.commute add_cancel_right_left dvdI mult.assoc mult.commute mult_0 mult_0_right)
  hence "a dvd c"
    by (metis (no_types, hide_lams) add_cancel_right_left dvd_mult2 is_gcd_def gcd_jedinstven mult.right_neutral mult_0_right nat_mult_1 pomocna_obrnuto)
  thus ?thesis
    by simp
qed

(* 11|6^(2n)+3^(n+2)+3^n *)

lemma deljivost_sa_11:
  fixes n :: nat
shows "(11::nat) dvd (6^(2*n::nat) + 3^(n+2) + 3^n)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof -
  (* [[show_types]] *)
  (* mora da bude oblika nesto = nesto *)
    have "(6::nat)^(2*(Suc n)) + 3^((Suc n) + 2) + 3^ (Suc n) = 6^(2*(n + 1)) + 3^((n + 1) + 2) + 3^ (n + 1)"
  (*using [[show_types]] --- pokazuje da mora da se doda nat na pocetku *)
      by simp
    also have "... = 6^(2*n+2) + 3^(n+2)*3 + 3^n*3"
      by (simp add: algebra_simps power_add)
    also have "... = 6^(2*n) * 6^2 + 3^(n + 2) * 3 + 3^n * 3"
      by (simp add: algebra_simps)
    also have "... = 6^(2*n) * 36 + 3 * 3^(n + 2) + 3 * 3^n"
      by (simp add: algebra_simps)
    also have "... = 36 * 6^(2*n) + 3 * 3^(n + 2) + 3 * 3^n"
      by (simp add: algebra_simps)
    also have "... = 36 * 6^(2*n) + (36-33) * 3^(n + 2) + (36-33) * 3^n"
      by (simp add: algebra_simps)
    also have "... = 36 * 6^(2*n) + 36 * 3^(n + 2) - 33 * 3^(n + 2) + 36 * 3^n - 33 * 3^n"
      by (simp add: algebra_simps)
    also have "... = 36 * (6^(2*n) + 3^(n + 2) + 3^n) - 33 * (3^(n + 2) + 3^n)"
      by (simp add: algebra_simps)
    also have "... = 36 * (6^(2*n) + 3^(n + 2) + 3^n) - 11 * 3 * (3^(n + 2) + 3^n)"
      by (simp add: algebra_simps)
    also have "... = (36::nat) * (6^(2*n) + 3^(n + 2) + 3^n) - 11 * (3^(n + 3) + 3^(n+1))"
      by (simp add: algebra_simps power_add)
    finally show ?case
      
  (* sledgehammer *)
      by (smt Suc.IH dvd_diff_nat dvd_trans dvd_triv_left dvd_triv_right)
  qed
qed

end