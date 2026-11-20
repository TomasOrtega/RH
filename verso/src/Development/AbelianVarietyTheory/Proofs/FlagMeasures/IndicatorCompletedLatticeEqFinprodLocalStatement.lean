import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndicatorCompletedLatticeEqFinprodLocal
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIndicatorCompletedLatticeEqFinprodLocal.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.indicator_completedLattice_eq_finprod_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ X : Fin 1 → Fin n → Af F ⊗[F] E, {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}.indicator (1 : (Fin 1 → Fin n → Af F ⊗[F] E) → ℂ) X = ∏ᶠ v : HeightOneSpectrum (𝓞 F), {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v X) := by
  first | exact @GlobalTheory.AdelicU.indicator_latHat_eq_finprod | exact GlobalTheory.AdelicU.indicator_latHat_eq_finprod | (intros; apply GlobalTheory.AdelicU.indicator_latHat_eq_finprod <;> assumption)
