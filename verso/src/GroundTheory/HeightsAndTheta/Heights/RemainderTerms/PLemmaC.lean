import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AltFrob
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem numStandardTable_eq_frobDim (h1 : FrobeniusDimensionFormula.Statement) {m : ℕ}
    (lam : Fin m → ℕ) (hlam : Antitone lam) :
    (numStandardTable lam : ℚ) = GroundTheory.Heights₂.Heights.frobDim lam := by
  rw [h1 m lam hlam, GroundTheory.Heights₂.Heights.frobDim]
  congr 2
  unfold vandermondeOf
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem LemmaC.proof (h1 : FrobeniusDimensionFormula.Statement) : LemmaC.Statement := by
  intro r a nu hnu
  have hsum : Antitone (fun i => a + nu i) := fun i j hij => Nat.add_le_add_left (hnu hij) a
  have hrect : Antitone (rectangle r a) := fun _ _ _ => le_rfl
  have hb := GroundTheory.Heights₂.Heights.FrobeniusRectangleBound.intersectionNumber_baseChange r a nu hnu
  rw [← numStandardTable_eq_frobDim h1 _ hsum, ← numStandardTable_eq_frobDim h1 nu hnu,
    show (fun _ : Fin r => a) = rectangle r a from rfl,
    ← numStandardTable_eq_frobDim h1 _ hrect] at hb
  exact_mod_cast hb

end GroundTheory.Heights₂.Heights.RestTerms
