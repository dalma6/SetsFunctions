
theory Teoreme
imports Complex_Main
begin

(* 108. Simetricna razlika skupova definise na sledeci nacin: *)
 fun simetricnaRazlika :: "nat set => nat set => nat set" where 
  "simetricnaRazlika A B = (A - B) \<union> (B - A)" 

(* a) *)
lemma "simetricnaRazlika A B = (A \<union> B) - (A \<inter> B)" (is "?levo = ?desno")
proof 
  show "?levo \<subseteq> ?desno"
    proof
      fix x
      assume "x \<in> ?levo"
          hence "(x \<in> A-B) \<or> (x \<in> B-A)"
            by auto
          hence "(x \<in> A \<and> x \<notin> B) \<or> (x \<in> B \<and> x \<notin> A)"
            by auto
          hence "(x \<in> A \<union> B) \<and> (x \<notin> (A \<inter> B))"
            by auto
          thus "x \<in> ?desno"
            by auto
     qed
next
  show "?desno \<subseteq> ?levo"
    proof
      fix x
      assume "x \<in> ?desno"
        hence "x \<in> (A \<union> B) \<and> x \<notin> (A \<inter> B)"
          by auto
        hence "(x \<in> A \<or> x \<in> B) \<and> (x \<in> -A \<or> x \<in> -B)"
          by auto
        hence "(x \<in> A-B) \<or> (x \<in> B-A)"
          by auto
        thus "x \<in> ?levo"
          by auto
  qed
qed
      
(* b) *)  
lemma "simetricnaRazlika A B = simetricnaRazlika B A" (is "?levo = ?desno")
proof
  show "?levo \<subseteq> ?desno"
  (*i ovo je moglo by auto, ali je uradjeno ovako cisto kao mali primer*)
  proof
    fix x
    assume "x \<in> ?levo"
      hence "x \<in> A - B \<or> x \<in> B - A"
        by auto
      thus "x \<in> ?desno"
        by auto
   qed
next
  show "?desno \<subseteq> ?levo"
    by auto
  qed

(* v) *)
lemma "simetricnaRazlika A A = {}" (is "?levo = ?desno")
  proof
    show "?levo \<subseteq> ?desno"
    proof 
      fix x
      assume "x \<in> ?levo"
        hence "x \<in> A-A"
          by auto
        thus "x \<in> ?desno"
          by auto
     qed
next
  show "?desno \<subseteq> ?levo"
  proof
    fix x
    assume "x \<in> ?desno"
      hence "x \<in> A-A"
        by auto
  qed
qed

(* g) *)
lemma "simetricnaRazlika A (simetricnaRazlika B C) = simetricnaRazlika (simetricnaRazlika A B) C"
    by auto

(* d) *)
lemma "simetricnaRazlika A (simetricnaRazlika A B) = B" 
  by auto

(* dj) *)
lemma "A \<union> B = simetricnaRazlika (simetricnaRazlika A B) (A \<inter> B)"
  by auto
  
(* e) *)
lemma "A \<inter> simetricnaRazlika B C = simetricnaRazlika (A \<inter> B) (A \<inter> C)" 
  by auto


(* 38. *)    
(* g) *)
lemma "A - (B \<inter> C) = (A - B) \<union> (A - C)" (is "?levo = ?desno")
proof
  show "?levo \<subseteq> ?desno"
    proof
    fix x
    assume "x \<in> ?levo"
      hence "x \<in> A \<and> x \<notin> (B \<inter> C)"
        by auto
      hence "x \<in> A \<and> (x \<notin> B \<or> x \<notin> C)"
        by auto
      hence "x \<in> A \<and> x \<notin> B \<or> x \<in> A \<and> x \<notin> C"
        by auto
      thus "x \<in> ?desno"
        by auto
    qed
next
  show "?desno \<subseteq> ?levo"
  proof
    fix x
    assume "x \<in> ?desno"
    hence "x \<in> A-B \<or> x \<in> A-C"
      by auto
    hence "x \<in> A \<and> (x \<notin> B \<or> x \<notin> C)"
      by auto
    thus "x \<in> ?levo"
      by auto
  qed
qed

(* dj) *)
lemma "A \<inter> (B-C) = (A \<inter> B) - (A \<inter> C)" (is "?levo = ?desno")
proof
  show "?levo \<subseteq> ?desno"
  proof
    fix x
    assume "x \<in> ?levo"
    hence "x \<in> A \<and> x \<in> B \<and> x \<notin> C"
      by auto
    hence "x \<in> A \<inter> B \<and> x \<notin> A \<inter> C"
      by auto
    thus "x \<in> ?desno"
      by auto
   qed
next 
  show "?desno \<subseteq> ?levo"
  proof
    fix x
    assume "x \<in> ?desno"
    hence "x \<in> A \<inter> B \<and> x \<notin> A \<inter> C"
      by auto
    hence "x \<in> A \<and> x \<in> B \<and> x \<notin> C"
      by auto
    thus "x \<in> ?levo"
      by auto
  qed
qed

(* z) *)
lemma "A - (B - C) = (A-B) \<union> (A \<inter> C)" (is "?levo = ?desno")
proof 
  show "?levo \<subseteq> ?desno"
  proof
    fix x
    assume "x \<in> ?levo"
      hence "x \<in> A \<and> x \<notin> (B - C)"
        by auto
      hence "x \<in> A \<and> (x \<notin> B \<or> x \<in> C)"
        by auto
      hence "x \<in> A \<and> x \<notin> B \<or> x \<in> A \<and> x \<in> C"
        by metis
      thus "x \<in> ?desno"
        by auto
  qed
next
  show "?desno \<subseteq> ?levo"
  proof
      fix x
      assume "x \<in> ?desno"
      hence "x \<in> A \<and> x \<notin> B \<or> x \<in> A \<and> x \<in> C"
        by auto
      hence "x \<in> A \<and> x \<notin> B-C"
        by auto
      thus "x \<in> ?levo"
        by auto
  qed
qed

(* 37. *)
(* a) *)
lemma "A \<union> (-A \<inter> B) = A \<union> B" (is "?levo = ?desno") 
proof 
  show "?levo \<subseteq> ?desno"
  proof
    fix x
    assume "x \<in> ?levo"
      hence "x \<in> A \<or> x \<in> (-A \<inter> B)"
        by auto
      hence "(x \<in> A \<or> x \<notin> A) \<and> (x \<in> A \<or> x \<in> B)"
        by auto
      thus "x \<in> A \<union> B"
        by auto
   qed
next
  show "?desno \<subseteq> ?levo"
  proof
    fix x
    assume "x \<in> ?desno"
      hence "x \<in> A \<or> x \<in> B"
        by auto
      hence "x \<in> A \<or> x \<in> (-A \<inter> B)"
        by auto
      thus "x \<in> A \<union> (-A \<inter> B)"
        by auto
   qed
qed

(* 43. *)
(* a) *)

lemma "(A ∪ B) × C = (A × C) ∪ (B × C)" (is "?levo = ?desno")
proof
  show "?levo ⊆ ?desno"
  proof
    fix z
    assume *: "z ∈ (A ∪ B) × C"
    obtain x y where z: "z = (x, y)"
      by (cases z) auto
      have "(x, y) ∈ ?levo"
      using * z
      by auto
    hence "x ∈ A ∪ B ∧ y ∈ C"
      by (metis `(x, y) ∈ (A ∪ B) × C` mem_Sigma_iff)
    hence "(x ∈ A ∨ x ∈ B) ∧ y ∈ C"
      by auto
    hence "(x ∈ A ∧ y ∈ C) ∨ (x ∈ B ∧ y ∈ C)"
      by auto
    hence "(x, y) ∈ A × C ∨ (x, y) ∈ B × C"
      by auto
    hence "(x, y) ∈ A × C ∪ B × C"
      by auto
    hence "(x, y) ∈ A × C ∪ B × C"
      by (metis Sigma_Un_distrib1 `(x, y) ∈ (A ∪ B) × C`)
    hence "(x, y) ∈ ?desno"
      by metis
    thus "z \<in> ?desno"
     using * z
     by auto
qed
next
show "?desno ⊆ ?levo"
 proof
    fix z
    assume *: "z ∈ ?desno"
    obtain x y where z: "z = (x, y)"
      by (cases z) auto
    have "(x, y) ∈ ?desno"
      using * z
      by auto
    hence "x ∈ A ∧ y ∈ C ∨ x ∈ B ∧ y ∈ C"
      by auto
    hence "x ∈ A ∨ x ∈ B ∧ y ∈ C"
      by auto
    hence "(x, y) ∈ (A ∪ B) × C"
      by (metis "*" Sigma_Un_distrib1 z)
    thus "z \<in> ?levo"
     using * z
     by auto
   qed
qed

(* v) *)
lemma "(A - B) × C = (A × C) - (B × C)" (is "?levo = ?desno")
proof
  show "?levo ⊆ ?desno"
  proof
    fix z
      assume *: "z ∈ ?levo"
      obtain x y where z: "z = (x, y)"
        by (cases z) auto
      have "(x, y) ∈ ?levo"
        using * z
        by auto
      hence "x ∈ A ∧ x ∉ B ∧ y ∈ C"
        by auto
      hence "(x, y) ∈ ?desno"
        by auto
      thus "z ∈ ?desno"  
        using * z
        by auto
    qed
next 
show "?desno ⊆ ?levo"
proof
    fix z
    assume *: "z ∈ ?desno"
    obtain x y where z: "z = (x, y)"
      by (cases z) auto
    have "(x, y) ∈ ?desno"
      using * z
      by auto
   hence "x ∈ A ∧ y ∈ C ∧ ¬ (x ∈ B ∧ y ∈ C)"
    by auto
   hence "(x, y) ∈ ?levo"
    by auto
   thus "z ∈ ?levo"
    using z *
    by auto
  qed
qed

(* 123. *)
(* a) *)

(* Dokaz injektivnosti funkcije f po slucajevima *)
definition W :: "real set" where "W = {x. 0 ≤ x ∧ x ≤ 1}"
definition f :: "real ⇒ real" where
 "f x = (if x ∈ W then x^2 + 1 else x + 1)"

(* x1 i x2 su oba u skupu W *)
lemma "∀ x1 ∈ W. ∀ x2 ∈ W. f x1 = f x2 ⟶ x1 = x2"
proof safe
  fix x1::real
  fix x2::real
  assume *: "f x1 = f x2" and "x1 ∈ W" and "x2 ∈ W"
    hence "x1^2 + 1 = x2^2 + 1"
      using *
      unfolding f_def
      by auto
    hence "x1^2 = x2^2"
      by auto  
    thus "x1 = x2"  
       using `f x1 = f x2`
       using `x1 ∈ W` and `x2 ∈ W`
       unfolding W_def
       apply auto
       by (metis power2_eq_imp_eq)
qed

(* nijedan od x1 i x2 nije u skupu W *)
lemma "x1 ∉ W ∧ x2 ∉ W ∧ f x1 = f x2 ⟶ x1 = x2"
proof safe
  fix x1::real
  fix x2::real
assume *: "f x1 = f x2" and "x1 ∉ W" and "x2 ∉ W"
  hence "x1 + 1 = x2 + 1"
    using *
    unfolding f_def
    by auto
  thus "x1 = x2"
    by auto
qed

(* jedan od x1 i x2, recimo x1, je u W, a drugi nije, 
ovde ne mozemo ni imati iste slike za x1 i x2, a evo i zasto *)
lemma kvadrat: shows "x \<in> W \<longrightarrow> x^2 \<in> W"
proof safe
  assume "x \<in> W"
  thus "x^2 \<in> W"
    unfolding f_def
    unfolding W_def
    by (auto simp add: Power.linordered_idom_class.abs_square_le_1)
qed

lemma "x1 \<in> W \<and> x2 \<notin> W \<longrightarrow> f x1 \<noteq> f x2"
proof safe
  fix x1::real
  fix x2::real
  assume *: "x1 \<in> W" and "x2 \<notin> W"
  hence "f x1 = x1^2+1"
    using `x1 \<in> W`
    unfolding f_def
    by (auto simp add:f_def)
  also have "x1^2 \<in> W"
    using kvadrat `x1 \<in> W` 
    by auto
  hence "(x1^2 + 1) \<in> {x. 1 \<le> x \<and> x \<le> 2}"
    using kvadrat `x1 \<in> W`
    by (auto simp add: W_def)
  hence "f x1 \<in> {x. 1 \<le> x \<and> x \<le> 2}"
    using `x1 \<in> W`
    by (auto simp add: f_def W_def)
  have "(x2 + 1 >  2 \<or> x2 + 1 < 1)"
    using `x2 \<notin> W`
    by (auto simp add:W_def)
  hence "(x2 + 1 \<notin> {x. 1 \<le> x \<and> x \<le> 2})"
    using `x2 \<notin> W`
    by auto
  hence "f x2 \<notin> {x. 1 \<le> x \<and> x \<le> 2}"
    using `x2 \<notin> W`
    by (auto simp add: f_def W_def)
  thus " x1 \<in> W \<Longrightarrow> x2 \<notin> W \<Longrightarrow> f x1 = f x2 \<Longrightarrow> False"
    using `x2 \<notin> W` `x1 \<in> W` `x1^2 \<in> W`
    by (auto simp add: W_def f_def)
qed

(* dokaz surjektivnosti funkcije f po slucajevima: *)
definition skup1 :: "real set" where "skup1 = {x. 1 ≤ x ∧ x ≤ 2}"

lemma "x \<in> W \<longrightarrow> f x \<in> skup1"
  proof
    fix x::real
    assume "x \<in> W"
    obtain y where "y = f x"
      by auto
    hence "y = x^2 +1"
      using `x \<in> W`
      unfolding f_def
      by auto
    hence "y \<in> skup1"
      unfolding skup1_def
      using `y = f x`
      by (smt W_def ‹x ∈ W› mem_Collect_eq one_power2 power_mono zero_le_power2)
    thus "f x \<in> skup1"
     by (simp add: ‹y = f x›)
 qed

definition skup2 :: "real set" where "skup2 = {x. x < 1 \<or> x > 2}"

lemma "x \<notin> W \<longrightarrow> f x \<in> skup2"
proof
    fix x::real
    assume "x \<notin> W"
    hence "x < 0 \<or> x > 1"
      unfolding W_def
      by auto
    obtain y where "y = f x"
      by auto
    hence "y = x + 1"
      using `x \<notin> W`
      unfolding f_def
      by auto
    hence "y \<in> skup2"
      unfolding skup2_def
      using `y = f x`
      by (simp add: ‹y = f x› ‹x < 0 ∨ 1 < x›)
    thus "f x \<in> skup2"
      sledgehammer
      by (simp add: ‹y = f x›)
  qed

   
