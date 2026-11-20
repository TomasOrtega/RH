import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgEquivExtendingWittTiltFrobenius
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TameFrob.exists_algEquiv_iotaO_sigma` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsAlgEquivExtendingWittTiltFrobenius.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_algEquiv_extending_wittTiltFrobenius : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a], ∃ Φ : Om l ≃ₐ[ℚ_[l]] Om l,
    ∀ w : Wq l a, Φ (GlobalTheory.TameFrob.iotaO l a w) = GlobalTheory.TameFrob.iotaO l a (sigma l a w) := by
  first | exact @GlobalTheory.TameFrob.exists_algEquiv_iotaO_sigma | exact GlobalTheory.TameFrob.exists_algEquiv_iotaO_sigma | (intros; apply GlobalTheory.TameFrob.exists_algEquiv_iotaO_sigma <;> assumption)
