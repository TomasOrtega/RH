import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCocycleCoboundary
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.symm_int_cocycle_stdLat_coboundary` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeCocycleCoboundary.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.lattice_cocycle_coboundary : ∀ {g : ℕ} (c : Fl g → Fl g → ℤ), (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, c l l' = c l' l) → (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ l'' ∈ stdLat g, c l l' + c (l + l') l'' = c l (l' + l'') + c l' l'') → ∃ a : Fl g → ℤ, ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, c l l' = a (l + l') - a l - a l' := by
  first | exact @GlobalTheory.symm_int_cocycle_stdLat_coboundary | exact GlobalTheory.symm_int_cocycle_stdLat_coboundary | (intros; apply GlobalTheory.symm_int_cocycle_stdLat_coboundary <;> assumption)
