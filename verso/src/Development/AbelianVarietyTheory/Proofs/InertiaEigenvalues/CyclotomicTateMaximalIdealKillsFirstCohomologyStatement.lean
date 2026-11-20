import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTateMaximalIdealKillsFirstCohomology
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Cyc.AveragingRankOne.cyclotomic_maximalIdeal_smul_cocycle_isCoboundary` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCyclotomicTateMaximalIdealKillsFirstCohomology.lean&line=164#L164)
-/
theorem _root_.GlobalTheory.T.cyclotomic_tate_maximalIdeal_kills_first_cohomology : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act → ∀ (K : FinExt l) (r : ℕ) (a : PadicComplex l), a ∈ inC (Kinf K) → ‖a‖ < 1 → ∀ c : GQ l → Fin r → PadicComplex l, CocOn (Hinf K) (fun g y k => act g (y k)) (ball l r) c → CobOn (Hinf K) (fun g y k => act g (y k)) (ball l r) (fun g => a • c g) := by
  first | exact @GlobalTheory.Cyc.AveragingRankOne.cyclotomic_maximalIdeal_smul_cocycle_isCoboundary | exact GlobalTheory.Cyc.AveragingRankOne.cyclotomic_maximalIdeal_smul_cocycle_isCoboundary | (intros; apply GlobalTheory.Cyc.AveragingRankOne.cyclotomic_maximalIdeal_smul_cocycle_isCoboundary <;> assumption)
