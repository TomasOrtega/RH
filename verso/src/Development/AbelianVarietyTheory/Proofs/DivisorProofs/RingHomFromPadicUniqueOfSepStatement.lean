import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomFromPadicUniqueOfSep
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.padicInt_ringHom_ext_of_separated` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRingHomFromPadicUniqueOfSep.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.ring_hom_from_padic_unique_of_sep : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [Ring R], (∀ x : R, (∀ n : ℕ, ∃ y : R, x = (p : R) ^ n * y) → x = 0) → ∀ f g : ℤ_[p] →+* R, f = g := by
  first | exact @GlobalTheory.padicInt_ringHom_ext_of_separated | exact GlobalTheory.padicInt_ringHom_ext_of_separated | (intros; apply GlobalTheory.padicInt_ringHom_ext_of_separated <;> assumption)
