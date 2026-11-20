import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange

/- English proof (translation)
Establish `hg : ∀ a b, R.gram u a b = u b ⬝ᵥ R.Hm *ᵥ star (u a)` using `fun _ _ => rfl`. Use extensionality with `a b`. Rewrite using `[hg]`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_eq' {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ) :
    R.gram u = (Matrix.of u).map (starRingEnd ℂ) * R.Hmᵀ * (Matrix.of u)ᵀ := by
  have hg : ∀ a b, R.gram u a b = u b ⬝ᵥ R.Hm *ᵥ star (u a) := fun _ _ => rfl
  ext a b
  rw [hg]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Introduce `E _ _ _ g Λ _ _ R m u f T hf`. Establish `hfT : Matrix.of f = Tᵀ * Matrix.of u`. Use extensionality with `i k`. Simplify using `[hf, Matrix.mul_apply, Finset.sum_apply]`. Establish `hc : (Tᵀ.map (starRingEnd ℂ)).det = starRingEnd ℂ T.det`.

Rewrite using `[Matrix.transpose_map, Matrix.det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]`. Establish `hn : ((‖T.det‖ ^ 2 : ℝ) : ℂ) = T.det * starRingEnd ℂ T.det`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Rewrite using `[GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange.gram_eq', GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange.gram_eq', hfT, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_transpose]`. Rewrite using `[show Tᵀ.map (starRingEnd ℂ) * (Matrix.of u).map (starRingEnd ℂ) * R.Hmᵀ * ((Matrix.of u)ᵀ * T) = Tᵀ.map (starRingEnd ℂ) * ((Matrix.of u).map (starRingEnd ℂ) * R.Hmᵀ * (Matrix.of u)ᵀ) * T by`.

Simplify using `only [Matrix.mul_assoc]]`. Rewrite using `[Matrix.det_mul, Matrix.det_mul, hc, hn]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_det_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (u f : Fin m → Fin g → ℂ) (T : Matrix (Fin m) (Fin m) ℂ), (∀ i, f i = ∑ j, T j i • u j) → (R.gram f).det = ((‖T.det‖ ^ 2 : ℝ) : ℂ) * (R.gram u).det := by
  intro E _ _ _ g Λ _ _ R m u f T hf
  have hfT : Matrix.of f = Tᵀ * Matrix.of u := by
    ext i k
    simp [hf, Matrix.mul_apply, Finset.sum_apply]
  have hc : (Tᵀ.map (starRingEnd ℂ)).det = starRingEnd ℂ T.det := by
    rw [Matrix.transpose_map, Matrix.det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]
  have hn : ((‖T.det‖ ^ 2 : ℝ) : ℂ) = T.det * starRingEnd ℂ T.det := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange.gram_eq', GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange.gram_eq',
    hfT, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [show Tᵀ.map (starRingEnd ℂ) * (Matrix.of u).map (starRingEnd ℂ) * R.Hmᵀ * ((Matrix.of u)ᵀ * T) =
      Tᵀ.map (starRingEnd ℂ) * ((Matrix.of u).map (starRingEnd ℂ) * R.Hmᵀ * (Matrix.of u)ᵀ) * T by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.det_mul, Matrix.det_mul, hc, hn]
  ring

end GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange
