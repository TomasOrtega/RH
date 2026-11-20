import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramMatrixIntegralAlmostAllPlaces
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SiegelND.Coef.hermOf_sub_gramH_mem_latH` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGramMatrixIntegralAlmostAllPlaces.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.gram_matrix_integral_almost_all_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)), hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ latH σ b v n := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.hermOf_sub_gramH_mem_latH | exact GlobalTheory.CompanionTheory.SiegelND.Coef.hermOf_sub_gramH_mem_latH | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.hermOf_sub_gramH_mem_latH <;> assumption)
