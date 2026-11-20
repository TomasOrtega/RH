import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMapMemSkewTrace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
open Matrix GlobalTheory.SUCong
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLevelMapMemSkewTrace.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.level_map_mem_skew_trace : ∀ {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (S : Subring A) (σ : A →+* A) (H : Matrix n n A) (ϖ : A) (q k : ℕ), GoodRing S σ ϖ q → GoodForm S σ H → 1 ≤ k → ∀ (g : GL n A), g ∈ congSU S σ H ϖ k → levMap S ϖ k (g : Matrix n n A) ∈ skewTr S σ H ϖ := by
  first | exact @GlobalTheory.SUCong.levMap_mem_skewTr | exact GlobalTheory.SUCong.levMap_mem_skewTr | (intros; apply GlobalTheory.SUCong.levMap_mem_skewTr <;> assumption)
