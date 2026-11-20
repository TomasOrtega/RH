import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankLevelDatumIdempotentEqOfSameShape
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FRankLevelDatumIdempotentEqOfSameShape.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.rank_levelDatum_idempotent_eq_of_same_shape : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), ∀ L L' : Lev g N, L.sharp = L'.sharp → L.s = L'.s → L.k = L'.k → rk ρ L.e = rk ρ L'.e := by
  first | exact @GlobalTheory.BadShare.CoDiag.rk_e_eq | exact GlobalTheory.BadShare.CoDiag.rk_e_eq | (intros; apply GlobalTheory.BadShare.CoDiag.rk_e_eq <;> assumption)
