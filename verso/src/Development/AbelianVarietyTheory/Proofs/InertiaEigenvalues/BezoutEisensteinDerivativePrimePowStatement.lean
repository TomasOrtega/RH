import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BezoutEisensteinDerivativePrimePow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BSP.bezout_Ep_derivative` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBezoutEisensteinDerivativePrimePow.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.bezout_eisenstein_derivative_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (c : ℕ) (a b : Polynomial (Wq l bk.a)), a * bk.Ep + b * Polynomial.derivative bk.Ep = Polynomial.C ((l : Wq l bk.a) ^ c) := by
  first | exact @GlobalTheory.BSP.bezout_Ep_derivative | exact GlobalTheory.BSP.bezout_Ep_derivative | (intros; apply GlobalTheory.BSP.bezout_Ep_derivative <;> assumption)
