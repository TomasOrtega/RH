import Mathlib
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory.OffDiagK

def sgn {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : ℝ := if ε a then 1 else -1

def fi {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : ℝ := if ε a then 0 else 1

/- English proof (translation)
Apply the tactic sequence `unfold Jm sgn; congr 1; funext a; split_ifs <;> simp`.
-/
lemma Jm_eq {n : ℕ} (ε : Fin n → Bool) :
    Jm ε = Matrix.diagonal (fun a => ((sgn ε a : ℝ) : ℂ)) := by
  unfold Jm sgn; congr 1; funext a; split_ifs <;> simp

/- English proof (translation)
Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `push_cast`. Both sides reduce to the same expression.
-/
lemma star_mul_self' (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl

/- English proof (translation)
Rewrite using `[mul_comm, star_mul_self']`.
-/
lemma mul_star_self' (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, star_mul_self']

/- English proof (translation)
Establish `hb` using `congrFun (congrFun h b) b`. Rewrite `hb` using `[Jm_eq, Matrix.mul_apply]`. Simplify using `only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at hb`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Use `push_cast`.

Rewrite using `[← hb]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[mul_right_comm, star_mul_self']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma col_sum {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ * Jm ε * M = Jm ε) (b : Fin n) :
    ∑ a, sgn ε a * ‖M a b‖ ^ 2 = sgn ε b := by
  have hb := congrFun (congrFun h b) b
  rw [Jm_eq, Matrix.mul_apply] at hb
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at hb
  apply Complex.ofReal_injective
  push_cast
  rw [← hb]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_right_comm, star_mul_self']; push_cast; ring

/- English proof (translation)
Establish `ha` using `congrFun (congrFun h a) a`. Rewrite `ha` using `[Jm_eq, Matrix.mul_apply]`. Simplify using `only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at ha`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Use `push_cast`.

Rewrite using `[← ha]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[mul_right_comm, mul_star_self']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma row_sum {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : M * Jm ε * Mᴴ = Jm ε) (a : Fin n) :
    ∑ b, sgn ε b * ‖M a b‖ ^ 2 = sgn ε a := by
  have ha := congrFun (congrFun h a) a
  rw [Jm_eq, Matrix.mul_apply] at ha
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at ha
  apply Complex.ofReal_injective
  push_cast
  rw [← ha]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_right_comm, mul_star_self']; push_cast; ring

/- English proof (translation)
Establish `hJ` using `Formalism.REAL.Jm_mul_self ε`. Establish `h1 : (Jm ε * Mᴴ * Jm ε) * M = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, h, hJ]`. Establish `h2 : M * (Jm ε * Mᴴ * Jm ε) = 1` using `mul_eq_one_comm.mp h1`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc, hJ, Matrix.mul_one]`. Use `_ = Jm ε := by rw [h2, Matrix.one_mul]`.
-/
lemma other_side {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ * Jm ε * M = Jm ε) : M * Jm ε * Mᴴ = Jm ε := by
  have hJ := Formalism.REAL.Jm_mul_self ε
  have h1 : (Jm ε * Mᴴ * Jm ε) * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, h, hJ]
  have h2 : M * (Jm ε * Mᴴ * Jm ε) = 1 := mul_eq_one_comm.mp h1
  calc M * Jm ε * Mᴴ = M * (Jm ε * Mᴴ * Jm ε) * Jm ε := by
        simp only [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = Jm ε := by rw [h2, Matrix.one_mul]

/- English proof (translation)
Establish `h1 : ∑ b, fi ε b * (∑ a, sgn ε a * ‖M a b‖ ^ 2) = ∑ b, fi ε b * sgn ε b`. Simplify using `only [col_sum ε M h]`. Establish `h2 : ∑ a, fi ε a * (∑ b, sgn ε b * ‖M a b‖ ^ 2) = ∑ a, fi ε a * sgn ε a`. Simplify using `only [row_sum ε M (other_side ε M h)]`. Simplify using `only [Finset.mul_sum] at h1 h2`.

Rewrite `h1` using `[Finset.sum_comm]`. Simplify using `only [sub_mul, Finset.sum_sub_distrib]`. Rewrite using `[show (∑ a, ∑ b, fi ε b * sgn ε a * ‖M a b‖ ^ 2) = ∑ a, ∑ b, fi ε b * (sgn ε a * ‖M a b‖ ^ 2) by`. Simplify using `only [mul_assoc],`. Use `show (∑ a, ∑ b, fi ε a * sgn ε b * ‖M a b‖ ^ 2) = ∑ a, ∑ b, fi ε a * (sgn ε b * ‖M a b‖ ^ 2) by`.

Simplify using `only [mul_assoc], h1, h2, sub_self]`.
-/
lemma key {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ * Jm ε * M = Jm ε) :
    ∑ a, ∑ b, (fi ε b * sgn ε a - fi ε a * sgn ε b) * ‖M a b‖ ^ 2 = 0 := by
  have h1 : ∑ b, fi ε b * (∑ a, sgn ε a * ‖M a b‖ ^ 2) = ∑ b, fi ε b * sgn ε b := by
    simp only [col_sum ε M h]
  have h2 : ∑ a, fi ε a * (∑ b, sgn ε b * ‖M a b‖ ^ 2) = ∑ a, fi ε a * sgn ε a := by
    simp only [row_sum ε M (other_side ε M h)]
  simp only [Finset.mul_sum] at h1 h2
  rw [Finset.sum_comm] at h1
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [show (∑ a, ∑ b, fi ε b * sgn ε a * ‖M a b‖ ^ 2) = ∑ a, ∑ b, fi ε b * (sgn ε a * ‖M a b‖ ^ 2) by
      simp only [mul_assoc],
    show (∑ a, ∑ b, fi ε a * sgn ε b * ‖M a b‖ ^ 2) = ∑ a, ∑ b, fi ε a * (sgn ε b * ‖M a b‖ ^ 2) by
      simp only [mul_assoc], h1, h2, sub_self]

/- English proof (translation)
Establish `hk` using `key ε M h`. Establish `hs : ∑ a, ∑ b, (fi ε b * sgn ε a - fi ε a * sgn ε b) * ‖M a b‖ ^ 2 = - ∑ a, ∑ b, (if ε a = false ∧ ε b = true then ‖M a b‖ ^ 2 else 0)`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp [fi, sgn, ha, hb, hTF a b]`. Rewrite `hk` using `[hs, neg_eq_zero]`. Introduce `a b ha hb`. Apply the tactic sequence `have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg fun b _ => by split_ifs <;> positivity)).mp hk a (Finset.mem_univ _)`.

Apply the tactic sequence `have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by split_ifs <;> positivity)).mp h0 b (Finset.mem_univ _)`. Simplify using `only [ha, hb, and_self, if_true] at h1`. Simplify using `using h1`.
-/
lemma offdiag_zero {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ * Jm ε * M = Jm ε) (hTF : ∀ a b, ε a = true → ε b = false → M a b = 0) :
    ∀ a b, ε a = false → ε b = true → M a b = 0 := by
  have hk := key ε M h
  have hs : ∑ a, ∑ b, (fi ε b * sgn ε a - fi ε a * sgn ε b) * ‖M a b‖ ^ 2
      = - ∑ a, ∑ b, (if ε a = false ∧ ε b = true then ‖M a b‖ ^ 2 else 0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    cases ha : ε a <;> cases hb : ε b <;> simp [fi, sgn, ha, hb, hTF a b]
  rw [hs, neg_eq_zero] at hk
  intro a b ha hb
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg fun b _ => by
    split_ifs <;> positivity)).mp hk a (Finset.mem_univ _)
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by
    split_ifs <;> positivity)).mp h0 b (Finset.mem_univ _)
  simp only [ha, hb, and_self, if_true] at h1
  simpa using h1

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp [sgn, ha, hb, hTF a b, hFT a b]`.
-/
lemma comm_of {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (hTF : ∀ a b, ε a = true → ε b = false → M a b = 0)
    (hFT : ∀ a b, ε a = false → ε b = true → M a b = 0) : M * Jm ε = Jm ε * M := by
  ext a b
  rw [Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]
  cases ha : ε a <;> cases hb : ε b <;> simp [sgn, ha, hb, hTF a b, hFT a b]

end GlobalTheory.OffDiagK

open GlobalTheory.OffDiagK in

/- English proof (translation)
Introduce `n ε g`. Establish `hg : (toM g)ᴴ * Jm ε * toM g = Jm ε` using `g.2`. Rewrite using `[Formalism.REAL.mem_KG, Fintype.sum_eq_zero_iff_of_nonneg (fun _ => by positivity)]`. Prove the components needed by the constructor for the conclusion. Introduce `h0`.

Establish `hTF : ∀ a b, ε a = true → ε b = false → toM g a b = 0`. Introduce `a b ha hb`. Use `congrFun h0 ⟨(a, b), ha, hb⟩` as an intermediate fact. Simplify using `using this`. Establish `hFT` using `offdiag_zero ε _ hg hTF`.

Establish `hc` using `comm_of ε _ hTF hFT`. Use `⟨?_, hc⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff']`. Establish `hJ` using `Formalism.REAL.Jm_mul_self ε`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, hJ, Matrix.mul_one, Matrix.star_eq_conjTranspose]`. Use `_ = 1 := by rw [hc, ← Matrix.mul_assoc, hg, hJ]`. Introduce and unpack `⟨_, hc⟩`. Use function extensionality and compare the values at `z`. Take `⟨⟨a, b⟩, ha, hb⟩` from `z`.

Simplify using `only at ha hb`. Establish `e` using `congrFun (congrFun hc a) b`. Rewrite `e` using `[Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Simplify using `only [sgn, ha, hb] at e`. Move the coercions through the operations in `at e`.

Establish `h0 : toM g a b = 0` using `by linear_combination (-1/2 : ℂ) * e`. Simplify using `[h0]`.
-/
theorem GlobalTheory.offDiag_zero_iff_mem_K : ∀ (n : ℕ) (ε : Fin n → Bool) (g : UJ ε),
    ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 = 0 ↔ g ∈ KG ε := by
  intro n ε g
  have hg : (toM g)ᴴ * Jm ε * toM g = Jm ε := g.2
  rw [Formalism.REAL.mem_KG, Fintype.sum_eq_zero_iff_of_nonneg (fun _ => by positivity)]
  constructor
  · intro h0
    have hTF : ∀ a b, ε a = true → ε b = false → toM g a b = 0 := by
      intro a b ha hb
      have := congrFun h0 ⟨(a, b), ha, hb⟩
      simpa using this
    have hFT := offdiag_zero ε _ hg hTF
    have hc := comm_of ε _ hTF hFT
    refine ⟨?_, hc⟩
    rw [Matrix.mem_unitaryGroup_iff']
    have hJ := Formalism.REAL.Jm_mul_self ε
    calc star (toM g) * toM g = (toM g)ᴴ * (toM g * Jm ε) * Jm ε := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hJ, Matrix.mul_one, Matrix.star_eq_conjTranspose]
      _ = 1 := by rw [hc, ← Matrix.mul_assoc, hg, hJ]
  · rintro ⟨_, hc⟩
    funext z
    obtain ⟨⟨a, b⟩, ha, hb⟩ := z
    simp only at ha hb
    have e := congrFun (congrFun hc a) b
    rw [Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    simp only [sgn, ha, hb] at e
    push_cast at e
    have h0 : toM g a b = 0 := by linear_combination (-1/2 : ℂ) * e
    simp [h0]
