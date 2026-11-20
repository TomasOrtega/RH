import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MeasurableFiniteLevelLatticeSet
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.BB.measurableSet_natMul_int` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FMeasurableFiniteLevelLatticeSet.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.measurable_finite_level_lattice_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ), MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (N : Fv F v ⊗[F] E) * X p i) ∈ latV b v}} := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.measurableSet_natMul_int | exact GlobalTheory.CompanionTheory.SW.BB.measurableSet_natMul_int | (intros; apply GlobalTheory.CompanionTheory.SW.BB.measurableSet_natMul_int <;> assumption)
