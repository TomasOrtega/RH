import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumSubgroupCharacterProperties
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FLevelDatumSubgroupCharacterProperties.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N, L.Mem 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.Mem (u * v)) ∧ L.chi 1 = 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.chi (u * v) = L.chi u * L.chi v) ∧ ∀ u, L.Mem u → IsNilpotent (u.val - 1) := by
  first | exact @GlobalTheory.BadShare.LevGroup.lev_group | exact GlobalTheory.BadShare.LevGroup.lev_group | (intros; apply GlobalTheory.BadShare.LevGroup.lev_group <;> assumption)
