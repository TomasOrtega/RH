import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterProps
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BadShare.ZCalc.zc_calc` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCentralIdempotentIrreducibleCharacterProps.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.centralIdempotent_irreducible_character_props : ∀ (G : Type) [Group G] [Fintype G], ∀ (V : FDRep ℂ G) [CategoryTheory.Simple V], IsProj (zc V.character) ∧ (∀ a : G → ℂ, conv (zc V.character) a = conv a (zc V.character)) ∧ (∀ (W : FDRep ℂ G) [CategoryTheory.Simple W], V.character ≠ W.character → conv (zc V.character) (zc W.character) = 0) ∧ ∀ e : G → ℂ, conv e e = e → conv (zc V.character) e 1 = (Module.finrank ℂ V : ℂ) * (rk V.ρ e : ℂ) / (Fintype.card G : ℂ) := by
  first | exact @GlobalTheory.BadShare.ZCalc.zc_calc | exact GlobalTheory.BadShare.ZCalc.zc_calc | (intros; apply GlobalTheory.BadShare.ZCalc.zc_calc <;> assumption)
