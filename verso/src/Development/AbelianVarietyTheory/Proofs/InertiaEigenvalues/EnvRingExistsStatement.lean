import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EnvRingExists
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FEnvRingExists.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.nonempty_envRing : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A) (d p : A), J.FG → (l : A) ∈ J → d ∈ J → IsUnit (D.δ d) → IsAdicComplete J A → Nonempty (EnvRing D J d p) := by
  first | exact @GlobalTheory.BSP.envRing_exists | exact GlobalTheory.BSP.envRing_exists | (intros; apply GlobalTheory.BSP.envRing_exists <;> assumption)
