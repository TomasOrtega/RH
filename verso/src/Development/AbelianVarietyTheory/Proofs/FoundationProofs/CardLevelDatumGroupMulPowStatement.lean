import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardLevelDatumGroupMulPow
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCardLevelDatumGroupMulPow.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.card_levelDatum_group_mul_pow : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N, Nat.card {u // L.Mem u} * g ^ (if L.sharp = true then L.k else 0) = g ^ (N * (N - 1) / 2) := by
  first | exact @GlobalTheory.BadShare.lev_card | exact GlobalTheory.BadShare.lev_card | (intros; apply GlobalTheory.BadShare.lev_card <;> assumption)
