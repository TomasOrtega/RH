import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

/- English proof (translation)
Introduce `_ n _ _ μ _ E k k' _ _ hk' x hx k₂`. Use `haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V`. Establish `hinv : E.ρ k₂ * E.ρ k₂⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`. Establish `hinv' : E.ρ k₂⁻¹ * E.ρ k₂ = 1` using `by rw [← map_mul, inv_mul_cancel, map_one]`. Set `L : (E.V →L[ℂ] E.V) ≃L[ℂ] (E.V →L[ℂ] E.V)` to `ContinuousLinearEquiv.equivOfInverse ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ k₂)) ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ k₂⁻¹)) (fun A => by simp [mul_assoc, hinv]) (fun A => by simp [mul_assoc, hinv'])`.

Establish `hL : ∀ A, L A = A * E.ρ k₂` using `fun A => rfl`. Establish `hmem : ∀ y : G n, (y⁻¹ : G n).val * x ∈ GLs n`. Introduce `y`. Establish `h1 : ((y⁻¹ : G n).val).det ≠ 0`. Use `(Matrix.isUnit_iff_isUnit_det _).1 (y⁻¹ : G n).isUnit` as an intermediate fact.

Conclude with `this.ne_zero`. Express the relevant statement in the definitionally equal form `((y⁻¹ : G n).val * x).det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero h1 hx`. Unfold `conv`.

Rewrite using `[← hL, ← L.integral_comp_comm]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `k y.val * k' ((y⁻¹ : G n).val * (x * k₂.1)) = L (k y.val * k' ((y⁻¹ : G n).val * x))`. Rewrite using `[hL, ← mul_assoc, hk' _ (hmem y) k₂, mul_assoc]`.
-/
theorem conv_right_equivariant : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k k' : Mat n → (E.V →L[ℂ] E.V)), KReg k → KReg k' → (∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k' (y * k₂.1) = k' y * E.ρ k₂) → ∀ x ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, conv μ E k k' (x * k₂.1) = conv μ E k k' x * E.ρ k₂ := by
  intro _ n _ _ μ _ E k k' _ _ hk' x hx k₂
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hinv : E.ρ k₂ * E.ρ k₂⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : E.ρ k₂⁻¹ * E.ρ k₂ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  let L : (E.V →L[ℂ] E.V) ≃L[ℂ] (E.V →L[ℂ] E.V) :=
    ContinuousLinearEquiv.equivOfInverse
      ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ k₂))
      ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ k₂⁻¹))
      (fun A => by simp [mul_assoc, hinv]) (fun A => by simp [mul_assoc, hinv'])
  have hL : ∀ A, L A = A * E.ρ k₂ := fun A => rfl
  have hmem : ∀ y : G n, (y⁻¹ : G n).val * x ∈ GLs n := by
    intro y
    have h1 : ((y⁻¹ : G n).val).det ≠ 0 := by
      have := (Matrix.isUnit_iff_isUnit_det _).1 (y⁻¹ : G n).isUnit
      exact this.ne_zero
    change ((y⁻¹ : G n).val * x).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero h1 hx
  unfold conv
  rw [← hL, ← L.integral_comp_comm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change k y.val * k' ((y⁻¹ : G n).val * (x * k₂.1)) = L (k y.val * k' ((y⁻¹ : G n).val * x))
  rw [hL, ← mul_assoc, hk' _ (hmem y) k₂, mul_assoc]

end GlobalTheory.CompanionTheory.WaveMult
