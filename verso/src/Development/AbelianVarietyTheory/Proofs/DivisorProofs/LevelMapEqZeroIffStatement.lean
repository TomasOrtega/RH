import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMapEqZeroIff
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
open Matrix GlobalTheory.SUCong
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLevelMapEqZeroIff.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.level_map_eq_zero_iff : ∀ {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (S : Subring A) (σ : A →+* A) (H : Matrix n n A) (ϖ : A) (q k : ℕ), GoodRing S σ ϖ q → ∀ (g : GL n A), g ∈ congSU S σ H ϖ k → (levMap S ϖ k (g : Matrix n n A) = 0 ↔ g ∈ congSU S σ H ϖ (k + 1)) := by
  first | exact @GlobalTheory.SUCong.levMap_eq_zero_iff_mem_succ | exact GlobalTheory.SUCong.levMap_eq_zero_iff_mem_succ | (intros; apply GlobalTheory.SUCong.levMap_eq_zero_iff_mem_succ <;> assumption)
