import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMapAdditive
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
open Matrix GlobalTheory.SUCong
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SUCong.levMap_mul_of_goodRing` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLevelMapAdditive.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.level_map_additive : ∀ {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (S : Subring A) (σ : A →+* A) (H : Matrix n n A) (ϖ : A) (q k : ℕ), GoodRing S σ ϖ q → 1 ≤ k → ∀ (g h : GL n A), g ∈ congSU S σ H ϖ k → h ∈ congSU S σ H ϖ k → levMap S ϖ k ((g * h : GL n A) : Matrix n n A) = levMap S ϖ k (g : Matrix n n A) + levMap S ϖ k (h : Matrix n n A) := by
  first | exact @GlobalTheory.SUCong.levMap_mul_of_goodRing | exact GlobalTheory.SUCong.levMap_mul_of_goodRing | (intros; apply GlobalTheory.SUCong.levMap_mul_of_goodRing <;> assumption)
