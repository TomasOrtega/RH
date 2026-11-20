import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTowerUnionAdjoinOfGaloisFixed
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FMemTowerUnionAdjoinOfGaloisFixed.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.mem_towerUnionAdjoin_of_galois_fixed : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (x : (integralClosure (O0 p) Ω)), (∀ g ∈ ⨅ n, Gn T n, g (x : Ω) = x) → x ∈ towerAlg T := by
  first | exact @GlobalTheory.K5.mem_towerAlg_of_fixed | exact GlobalTheory.K5.mem_towerAlg_of_fixed | (intros; apply GlobalTheory.K5.mem_towerAlg_of_fixed <;> assumption)
