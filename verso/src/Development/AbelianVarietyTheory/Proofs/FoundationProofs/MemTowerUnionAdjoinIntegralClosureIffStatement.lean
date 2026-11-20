import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTowerUnionAdjoinIntegralClosureIff
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FMemTowerUnionAdjoinIntegralClosureIff.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.mem_towerUnionAdjoinIntegralClosure_iff : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω) (s : (integralClosure (O0 p) Ω)), s ∈ towerAlg T ↔ (s : Ω) ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
  first | exact @GlobalTheory.towerAlg_mem_iff | exact GlobalTheory.towerAlg_mem_iff | (intros; apply GlobalTheory.towerAlg_mem_iff <;> assumption)
