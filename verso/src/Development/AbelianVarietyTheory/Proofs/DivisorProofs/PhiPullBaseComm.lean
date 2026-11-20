import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff

set_option autoImplicit false

namespace GlobalTheory.TorsionForm.OneVec

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem card_pair_castAdd_natAdd {n : ℕ} (i k : Fin n) :
    ({i.castAdd n, k.natAdd n} : Finset (Fin (n + n))).card = 2 := by
  rw [Finset.card_pair]
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

/- English proof (translation)
Evaluate the decidable proposition. A detailed English derivation is pending.
-/
theorem card_of_ne_small (S : Finset (Fin (1 + 1))) (h0 : ¬ S = ∅)
    (h1 : ¬ S = {Fin.castAdd 1 (0 : Fin 1)}) (h2 : ¬ S = {Fin.natAdd 1 (0 : Fin 1)}) :
    S.card = 2 := by
  revert h0 h1 h2
  revert S
  decide

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Substitute using the available equality. Simplify using the standard rewrite rules. Substitute using the available equality.

Simplify using the standard rewrite rules. Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem phi_pullBaseL {n : ℕ} (a : Fin n → ℂ) (y : Ext (n + n)) :
    phi (pullBaseL a y) = pullBaseL a (phi y) := by
  funext S
  show phi (pullBase a y) S = pullBase a (phi y) S
  simp only [phi, pullBase]
  split_ifs with h0 h1 h2
  · subst h0; simp
  · subst h1; simp [Finset.mul_sum]
  · subst h2; simp [Finset.mul_sum]
  · rw [card_of_ne_small S h0 h1 h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [card_pair_castAdd_natAdd]
    ring

end GlobalTheory.TorsionForm.OneVec
