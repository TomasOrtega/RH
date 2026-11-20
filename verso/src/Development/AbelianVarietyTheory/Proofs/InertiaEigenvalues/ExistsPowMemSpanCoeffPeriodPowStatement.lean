import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMemSpanCoeffPeriodPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsPowMemSpanCoeffPeriodPow.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.exists_pow_mem_span_coeff_period_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (M : ℕ), ∃ r : ℕ, (l : bk.S) ^ r ∈ Ideal.span (Set.range fun i => TB.c i (τ ^ M)) := by
  first | exact @GlobalTheory.BSP.pow_l_mem_span_coeff | exact GlobalTheory.BSP.pow_l_mem_span_coeff | (intros; apply GlobalTheory.BSP.pow_l_mem_span_coeff <;> assumption)
