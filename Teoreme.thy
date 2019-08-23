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

(* 123. *)
(* a) *)

definition A :: "real set" where "A = {x. 0 \<le> x \<and> x \<le> 1}"
definition f :: "real \<Rightarrow> real" where
 "f x = (if x \<in> A then x^2 + 1 else x + 1)"

lemma "\<forall> x1 \<in> A. \<forall> x2 \<in> A. f x1 = f x2 \<longrightarrow> x1 = x2"
proof
  fix x1::real
  fix x2::real
  assume "f x1 = f x2" and "x1 \<in> A" and "x2 \<in> A" and "0 \<le> x1 \<and> x1 \<le> 1 \<and> 0 \<le> x2 \<and> x2 \<le> 1"
    hence "x1^2 + 1 = x2^2 + 1"
      using assms
      by (metis f_def linorder_linear order_trans zero_le_one)
    hence "x1^2 = x2^2"
      by auto  
    hence "x1 = x2"  
       using assms
       using `f x1 = f x2`
       using `x1 \<in> A` and `x2 \<in> A`
       unfolding inj_on_def
       using `0 \<le> x1 \<and> x1 \<le> 1 \<and> 0 \<le> x2 \<and> x2 \<le> 1`
       by (metis power2_eq_imp_eq)

(* 43. *)
(* a) *)
(*lemma "(A \<union> B) \<times> C = (A \<times> C) \<union> (B \<times> C)" (is "?levo = ?desno")
proof
  show "?levo \<subseteq> ?desno"
  proof
    fix x and y
    assume "(x, y) \<in> ?levo"
    hence "x \<in> A \<union> B \<and> y \<in> C"
      by (metis `(x, y) \<in> (A \<union> B) \<times> C` mem_Sigma_iff)
    hence "(x \<in> A \<or> x \<in> B) \<and> y \<in> C"
      by auto
    hence "(x \<in> A \<and> y \<in> C) \<or> (x \<in> B \<and> y \<in> C)"
      by auto
    hence "(x, y) \<in> A \<times> C \<or> (x, y) \<in> B \<times> C"
      by auto
    hence "(x, y) \<in> A \<times> C \<union> B \<times> C"
      by auto
    hence "(x, y) \<in> A \<times> C \<union> B \<times> C"
      by (metis Sigma_Un_distrib1 `(x, y) \<in> (A \<union> B) \<times> C`)
    hence "(x, y) \<in> ?desno"
      by metis*)

end
