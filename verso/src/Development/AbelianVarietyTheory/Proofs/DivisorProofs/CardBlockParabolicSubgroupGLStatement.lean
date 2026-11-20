import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardBlockParabolicSubgroupGL
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowBlockIndicatorFromLtIff
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StdLoc.card_blockPar` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCardBlockParabolicSubgroupGL.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.card_blockParabolicSubgroupGL : ∀ (R : Type) [CommRing R] [Finite R] (a d : ℕ), a ≤ d →
    Nat.card (blockPar R a d) = Nat.card (GL (Fin a) R) * Nat.card (GL (Fin (d - a)) R) * Nat.card R ^ (a * (d - a)) := by
  first | exact @GlobalTheory.StdLoc.card_blockPar | exact GlobalTheory.StdLoc.card_blockPar | (intros; apply GlobalTheory.StdLoc.card_blockPar <;> assumption)
