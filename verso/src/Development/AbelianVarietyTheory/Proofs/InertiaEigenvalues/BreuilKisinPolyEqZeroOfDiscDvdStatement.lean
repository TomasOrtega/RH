import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPolyEqZeroOfDiscDvd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBreuilKisinPolyEqZeroOfDiscDvd.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.breuilKisin_poly_eq_zero_of_disc_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (r : Polynomial (Wq l bk.a)), r.degree < bk.Ep.degree → toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ (r : bk.S) → r = 0 := by
  first | exact @GlobalTheory.BSP.DiscRem.eq_zero_of_dvd | exact GlobalTheory.BSP.DiscRem.eq_zero_of_dvd | (intros; apply GlobalTheory.BSP.DiscRem.eq_zero_of_dvd <;> assumption)
