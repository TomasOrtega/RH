import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFilDvdEisensteinPowOnDisc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAcrisFilDvdEisensteinPowOnDisc.lean&line=161#L161)
-/
theorem _root_.GlobalTheory.T.acris_fil_dvd_eisenstein_pow_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (γ : Per.Acris l →+* bk.DA bk.ρ₀), (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) → (∀ x, ‖γ x‖ ≤ 1) → ∀ (m : ℕ) (y : Per.Acris l), C.j y ∈ Per.FilP l m → bk.iS bk.E ^ m ∣ γ y := by
  first | exact @GlobalTheory.AcrisDisc.main | exact GlobalTheory.AcrisDisc.main | (intros; apply GlobalTheory.AcrisDisc.main <;> assumption)
