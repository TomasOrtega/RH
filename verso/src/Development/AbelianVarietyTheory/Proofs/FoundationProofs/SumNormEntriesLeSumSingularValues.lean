import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc

namespace GlobalTheory.CartanInt.Frob
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

/- English proof (translation)
Establish `h1 : star U * U = 1` using `Matrix.mem_unitaryGroup_iff'.mp hU`. Establish `h2` using `congrFun (congrFun h1 a) a`. Simplify using `only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.star_def, Complex.conj_mul'] at h2`. Establish `h3 : ∑ i, ‖U i a‖ ^ 2 = 1` using `by exact_mod_cast h2`. Establish `h4` using `sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖U i a‖)`.

Simplify `h4` using `[h3]`.
-/
theorem sq_col_le {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (a : Fin n) : (∑ i, ‖U i a‖) ^ 2 ≤ n := by
  have h1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have h2 := congrFun (congrFun h1 a) a
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.star_def,
    Complex.conj_mul'] at h2
  have h3 : ∑ i, ‖U i a‖ ^ 2 = 1 := by exact_mod_cast h2
  have h4 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖U i a‖)
  simpa [h3] using h4

/- English proof (translation)
Rewrite using `[Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin q, (if a = (b : ℕ) then s a else 0)) p]`. Establish `h : ∀ a : ℕ, ∑ b : Fin q, (if a = (b : ℕ) then s a else 0) = if a ∈ Finset.range q then s a else 0` using `fun a => by`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun b => if a = b then s a else 0) q, Finset.sum_ite_eq]`. Simplify using `only [h]`. Rewrite using `[← Finset.sum_filter]`.

Use `congr 1`. Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
theorem sum_diag (p q : ℕ) (s : ℕ → ℝ) :
    ∑ a : Fin p, ∑ b : Fin q, (if (a : ℕ) = (b : ℕ) then s a else 0) =
      ∑ i ∈ Finset.range (min p q), s i := by
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin q, (if a = (b : ℕ) then s a else 0)) p]
  have h : ∀ a : ℕ, ∑ b : Fin q, (if a = (b : ℕ) then s a else 0) =
      if a ∈ Finset.range q then s a else 0 := fun a => by
    rw [Fin.sum_univ_eq_sum_range (fun b => if a = b then s a else 0) q, Finset.sum_ite_eq]
  simp only [h]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

/- English proof (translation)
Introduce `p q B`. Take `⟨U, hU, V, hV, hB⟩` from `GlobalTheory.RectSVD.exists_svd_singularValues p q B`. Use `set d : Fin p → Fin q → ℝ := fun a b => if (a : ℕ) = (b : ℕ) then singVal B a else 0 with hd`. Establish `hd0 : ∀ a b, 0 ≤ d a b` using `fun a b => by`. Simplify using `only [hd]`.

Use `split_ifs`. Conclude with `singVal_nonneg _ _`. Conclude with `le_rfl`. Establish `h1 : ∀ i j, ‖B i j‖ ≤ ∑ b, ∑ a, ‖U i a‖ * d a b * ‖V j b‖`. Introduce `i j`.

Establish `e` using `congrFun (congrFun hB i) j`. Rewrite using `[e, Matrix.mul_apply]`. Use `norm_sum_le_of_le _ fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_mul]`. Use `norm_sum_le_of_le _ fun a _ => le_of_eq ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_mul, Matrix.conjTranspose_apply, norm_star, Matrix.of_apply]`. Use `congr 2`. Simplify using `only [hd]`. Use `split_ifs`. Rewrite using `[Complex.norm_real]`.

Conclude with `Real.norm_of_nonneg (singVal_nonneg B a)`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_mul_sum, Finset.sum_mul]`. Repeatedly rewrite using `[Finset.sum_comm (s := (Finset.univ : Finset (Fin q))) (t := (Finset.univ : Finset (Fin q))) (f := fun j b => ∑ a, ‖U _ a‖ * d a b * ‖V j b‖)]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Repeatedly rewrite using `[Finset.sum_comm (s := (Finset.univ : Finset (Fin q))) (t := (Finset.univ : Finset (Fin p))) (f := fun j a => ‖U _ a‖ * d a b * ‖V j b‖)]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ∑ b, ∑ a, (((p + q : ℕ) : ℝ) + 1) / 2 * d a b := by`. Use `Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right ?_ (hd0 a b)` and prove the remaining obligations. Use `sq_col_le hU a` as an intermediate fact.

Use `sq_col_le hV b` as an intermediate fact. Use `push_cast`. Use polynomial arithmetic with `[sq_nonneg ((∑ i, ‖U i a‖) - ∑ j, ‖V j b‖)]`. Use `_ = _ := by`. Rewrite using `[← sum_diag, Finset.sum_comm]`.

Simplify using `only [Finset.mul_sum, hd]`.
-/
theorem sum_norm_le_sum_singVal : ∀ (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ),
    ∑ i, ∑ j, ‖B i j‖ ≤
      (((p + q : ℕ) : ℝ) + 1) / 2 * ∑ i ∈ Finset.range (min p q), singVal B i := by
  intro p q B
  obtain ⟨U, hU, V, hV, hB⟩ := GlobalTheory.RectSVD.exists_svd_singularValues p q B
  set d : Fin p → Fin q → ℝ := fun a b => if (a : ℕ) = (b : ℕ) then singVal B a else 0 with hd
  have hd0 : ∀ a b, 0 ≤ d a b := fun a b => by
    simp only [hd]; split_ifs
    · exact singVal_nonneg _ _
    · exact le_rfl
  have h1 : ∀ i j, ‖B i j‖ ≤ ∑ b, ∑ a, ‖U i a‖ * d a b * ‖V j b‖ := by
    intro i j
    have e := congrFun (congrFun hB i) j
    rw [e, Matrix.mul_apply]
    refine norm_sum_le_of_le _ fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine norm_sum_le_of_le _ fun a _ => le_of_eq ?_
    rw [norm_mul, norm_mul, Matrix.conjTranspose_apply, norm_star, Matrix.of_apply]
    congr 2
    simp only [hd]
    split_ifs
    · rw [Complex.norm_real]; exact Real.norm_of_nonneg (singVal_nonneg B a)
    · simp
  calc ∑ i, ∑ j, ‖B i j‖ ≤ ∑ i, ∑ j, ∑ b, ∑ a, ‖U i a‖ * d a b * ‖V j b‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
    _ = ∑ b, ∑ a, ((∑ i, ‖U i a‖) * ∑ j, ‖V j b‖) * d a b := by
        simp only [Finset.sum_mul_sum, Finset.sum_mul]
        simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin q))) (t := (Finset.univ : Finset (Fin q))) (f := fun j b => ∑ a, ‖U _ a‖ * d a b * ‖V j b‖)]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin q))) (t := (Finset.univ : Finset (Fin p))) (f := fun j a => ‖U _ a‖ * d a b * ‖V j b‖)]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum]; ring
    _ ≤ ∑ b, ∑ a, (((p + q : ℕ) : ℝ) + 1) / 2 * d a b := by
        refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_right ?_ (hd0 a b)
        have := sq_col_le hU a
        have := sq_col_le hV b
        push_cast
        nlinarith [sq_nonneg ((∑ i, ‖U i a‖) - ∑ j, ‖V j b‖)]
    _ = _ := by
        rw [← sum_diag, Finset.sum_comm]
        simp only [Finset.mul_sum, hd]

end GlobalTheory.CartanInt.Frob
