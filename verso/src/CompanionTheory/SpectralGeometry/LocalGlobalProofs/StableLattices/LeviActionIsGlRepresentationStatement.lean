import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionIsGlRepresentation
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
Apply `GlobalTheory.CompanionTheory.RgCOBlock.lF_glRel` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FLeviActionIsGlRepresentation.lean&line=184#L184)
-/
theorem _root_.GlobalTheory.T.levi_action_is_gl_representation : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), Monotone lev → GlRel E → ∀ (x : Cn n V), SuppIn (inU lev) x → ∀ p q r v, lev p = lev q → lev r = lev v → lF E p q (lF E r v x) - lF E r v (lF E p q x) = (if q = r then lF E p v x else 0) - (if v = p then lF E r q x else 0) := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.lF_glRel | exact GlobalTheory.CompanionTheory.RgCOBlock.lF_glRel | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.lF_glRel <;> assumption)
