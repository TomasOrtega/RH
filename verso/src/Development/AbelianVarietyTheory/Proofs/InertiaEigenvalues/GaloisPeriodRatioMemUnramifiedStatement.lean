import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisPeriodRatioMemUnramified
import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PeriodQuot.galois_periodRatio_mem_unramified` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FGaloisPeriodRatioMemUnramified.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.galois_periodRatio_mem_unramified_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (x : P.R.B), IsUnit x → (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] x = (l : P.R.B) * x → P.ιB x ∈ (P.PD K).Fil 1 → P.ιB x ∉ (P.PD K).Fil 2 → (∀ j : ℕ, 0 < j → j < finrank ℚ_[l] ↥(K0 K) → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1) → ∀ g : ↥(GK K), ∃ a : ↥(K0 K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B a * x := by
  first | exact @GlobalTheory.PeriodQuot.galois_periodRatio_mem_unramified | exact GlobalTheory.PeriodQuot.galois_periodRatio_mem_unramified | (intros; apply GlobalTheory.PeriodQuot.galois_periodRatio_mem_unramified <;> assumption)
