import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizableSchwartzOrbitalIntegral
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SiegelND.Coef.pureN_isSchwartzBruhat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFactorizableSchwartzOrbitalIntegral.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.factorizable_schwartz_orbital_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : (∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))), IsSchwartzArch φ → (∀ v, IsCompact (A v) ∧ IsOpen (A v)) → (∀ v, v ∉ S → A v = latV b v) → IsSchwartzBruhat (pureN φ A) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.pureN_isSchwartzBruhat | exact GlobalTheory.CompanionTheory.SiegelND.Coef.pureN_isSchwartzBruhat | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.pureN_isSchwartzBruhat <;> assumption)
