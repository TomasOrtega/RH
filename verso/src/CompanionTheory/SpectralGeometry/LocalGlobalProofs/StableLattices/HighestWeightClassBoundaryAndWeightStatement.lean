import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HighestWeightClassBoundaryAndWeight
import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RgCOBlock.TopU.top_cycle_weight` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FHighestWeightClassBoundaryAndWeight.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.highest_weight_class_boundary_and_weight : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (γ : Fin n → ℝ) (u : V), Monotone lev → KHighest ε E γ u →
    bd (allT n) E (Pi.single (omU ε lev) u) = 0 ∧
    ∀ a, lF E a a (Pi.single (omU ε lev) u) = (((γ a + wt (omU ε lev) a : ℝ)) : ℂ) • (Pi.single (omU ε lev) u : Cn n V) := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.TopU.top_cycle_weight | exact GlobalTheory.CompanionTheory.RgCOBlock.TopU.top_cycle_weight | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.TopU.top_cycle_weight <;> assumption)
