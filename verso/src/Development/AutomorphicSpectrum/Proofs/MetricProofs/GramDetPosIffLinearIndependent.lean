import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp.GramPos

open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ]

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem posDef_Hm_transpose (R : RiemLat E g Λ) : (R.Hmᵀ).PosDef := by
  have hH : (R.Hmᵀ).IsHermitian := by
    ext i j
    exact R.herm.apply j i
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have h1 := R.pos x hx
  have e : star x ⬝ᵥ (R.Hmᵀ *ᵥ x) = x ⬝ᵥ R.Hm *ᵥ star x := by
    rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
  have him : (star x ⬝ᵥ (R.Hmᵀ *ᵥ x)).im = 0 := hH.im_star_dotProduct_mulVec_self x
  rw [Complex.pos_iff]
  exact ⟨by rw [e]; exact h1, him.symm⟩

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_eq_mul (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ) :
    R.gram u = ((Matrix.of u)ᵀ)ᴴ * R.Hmᵀ * (Matrix.of u)ᵀ := by
  ext a b
  simp only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec,
    Matrix.conjTranspose_apply, Matrix.transpose_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem det_pos_of_linearIndependent (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ)
    (hu : LinearIndependent ℂ u) : 0 < (R.gram u).det := by
  have hC : Function.Injective ((Matrix.of u)ᵀ).mulVec := Matrix.mulVec_injective_iff.2 hu
  rw [gram_eq_mul]
  exact ((posDef_Hm_transpose R).conjTranspose_mul_mul_same hC).det_pos

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem linearIndependent_of_det_ne_zero (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ)
    (hd : (R.gram u).det ≠ 0) : LinearIndependent ℂ u := by
  have hinj : Function.Injective (R.gram u).mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd))
  have hC : Function.Injective ((Matrix.of u)ᵀ).mulVec := by
    intro x y hxy
    apply hinj
    have hxy' : (Matrix.of u)ᵀ *ᵥ x = (Matrix.of u)ᵀ *ᵥ y := hxy
    simp only [gram_eq_mul, ← Matrix.mulVec_mulVec, hxy']
  exact Matrix.mulVec_injective_iff.1 hC

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem gram_det_pos_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (u : Fin m → Fin g → ℂ), (LinearIndependent ℂ u → 0 < (R.gram u).det.re ∧ (R.gram u).det.im = 0) ∧ ((R.gram u).det ≠ 0 → LinearIndependent ℂ u) := by
  intro E _ _ _ g Λ _ _ R m u
  refine ⟨fun hu => ?_, linearIndependent_of_det_ne_zero R u⟩
  have h := Complex.pos_iff.1 (det_pos_of_linearIndependent R u hu)
  exact ⟨h.1, h.2.symm⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.GramPos
