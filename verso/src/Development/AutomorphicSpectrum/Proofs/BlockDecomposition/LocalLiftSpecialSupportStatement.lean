import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLiftSpecialSupport
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SaGen.LiftSupp.lift_det_one_mem_supp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalLiftSpecialSupport.lean&line=110#L110)
-/
theorem _root_.GlobalTheory.T.local_lift_special_support : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → ∀ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 → L x ∈ SUSupp σ J (P.inj 1) := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.LiftSupp.lift_det_one_mem_supp | exact GlobalTheory.CompanionTheory.SaGen.LiftSupp.lift_det_one_mem_supp | (intros; apply GlobalTheory.CompanionTheory.SaGen.LiftSupp.lift_det_one_mem_supp <;> assumption)
