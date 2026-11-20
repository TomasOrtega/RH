import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilConstantQuadraticCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWeilConstantQuadraticCharacter.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.weil_constant_quadratic_character : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → ∀ η : Fˣ →* ℂˣ, Continuous η → (∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) → ∀ g : F → ℂ, g ∈ schwartzBruhat F → g 0 = 0 → ∀ t : F, localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g) t = GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g t := by
  first | exact @GlobalTheory.CompanionTheory.GaussLam.localFourier_gTil | exact GlobalTheory.CompanionTheory.GaussLam.localFourier_gTil | (intros; apply GlobalTheory.CompanionTheory.GaussLam.localFourier_gTil <;> assumption)
