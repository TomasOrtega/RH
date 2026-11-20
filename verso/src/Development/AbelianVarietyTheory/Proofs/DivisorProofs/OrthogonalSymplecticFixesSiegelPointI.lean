import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory

/- English proof (translation)
Establish `hJ : s * J l ℝ = J l ℝ * s`. Establish `h2 : s * J l ℝ * sᵀ = J l ℝ` using `SymplecticGroup.mem_iff.mp hs`. Combine the equalities or inequalities in the displayed calculation. Establish `e1 : ∀ a b, s (.inl a) (.inr b) = - s (.inr a) (.inl b)`. Introduce `a b`.

Use `congrFun (congrFun hJ (.inl a)) (.inl b)` as an intermediate fact. Simplify `this` using `[J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]`. Establish `e2 : ∀ a b, s (.inr a) (.inr b) = s (.inl a) (.inl b)`. Introduce `a b`. Use `congrFun (congrFun hJ (.inl a)) (.inr b)` as an intermediate fact.

Simplify using `[J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hh : GlobalTheory.Published.Metaplectic.holPart s = P`. Use extensionality with `a b`. Simplify using `only [GlobalTheory.Published.Metaplectic.holPart, hP, e2, e1]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hQP : Q = (-I) • P`. Use extensionality with `a b`. Simplify using `only [hP, hQ, e2, e1, Matrix.smul_apply, smul_eq_mul]`.

Use `push_cast`. Put the polynomial expressions in normal form. Rewrite using `[I_sq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hinv : -(Q * P⁻¹) = I • (1 : Matrix l l ℂ)`.

Rewrite using `[hQP, Matrix.smul_mul, mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hd), neg_smul, neg_neg]`. Use `⟨hh, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hinv, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]`. Use `congr 1`. Simplify using `only [dotProduct]`.

Use `push_cast`. Put the polynomial expressions in normal form. Rewrite using `[I_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem holPart_eq_and_gaussian_of_orthogonal_symplectic (l : Type) [Fintype l] [DecidableEq l]
    (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ)
    (hP : ∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ))
    (hQ : ∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ))
    (hs : s ∈ Matrix.symplecticGroup l ℝ) (ho : sᵀ * s = 1) (hd : P.det ≠ 0) :
    GlobalTheory.Published.Metaplectic.holPart s = P ∧ ∀ x : l → ℝ,
      cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) =
        cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) := by
  have hJ : s * J l ℝ = J l ℝ * s := by
    have h2 : s * J l ℝ * sᵀ = J l ℝ := SymplecticGroup.mem_iff.mp hs
    calc s * J l ℝ = s * J l ℝ * (sᵀ * s) := by rw [ho, Matrix.mul_one]
      _ = (s * J l ℝ * sᵀ) * s := by simp only [Matrix.mul_assoc]
      _ = J l ℝ * s := by rw [h2]
  have e1 : ∀ a b, s (.inl a) (.inr b) = - s (.inr a) (.inl b) := by
    intro a b
    have := congrFun (congrFun hJ (.inl a)) (.inl b)
    simpa [J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] using this
  have e2 : ∀ a b, s (.inr a) (.inr b) = s (.inl a) (.inl b) := by
    intro a b
    have := congrFun (congrFun hJ (.inl a)) (.inr b)
    simp [J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] at this
    linarith
  have hh : GlobalTheory.Published.Metaplectic.holPart s = P := by
    ext a b
    simp only [GlobalTheory.Published.Metaplectic.holPart, hP, e2, e1]
    push_cast; ring
  have hQP : Q = (-I) • P := by
    ext a b
    simp only [hP, hQ, e2, e1, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring_nf; rw [I_sq]; ring
  have hinv : -(Q * P⁻¹) = I • (1 : Matrix l l ℂ) := by
    rw [hQP, Matrix.smul_mul, mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hd), neg_smul, neg_neg]
  refine ⟨hh, fun x => ?_⟩
  rw [hinv, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  simp only [dotProduct]
  push_cast
  ring_nf; rw [I_sq]; ring

end GlobalTheory
