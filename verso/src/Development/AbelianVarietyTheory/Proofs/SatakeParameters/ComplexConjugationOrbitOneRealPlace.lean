import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AutomorphicArithmetic.CyclotomicBounds.PlaceOfLetterInjective
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.ConjWord

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cc_comm {fr : Formalism.HC.Frame} (g : fr.GG) : g * fr.cc = fr.cc * g := mul_comm _ _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem plc_cc_mul {fr : Formalism.HC.Frame} (g : fr.GG) : plc (fr.cc * g) = plc g := UpperTheory.KStar.Words.placeOf_cc_mul g

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Replace the chosen expression with an arbitrary variable. Proceed by induction. Treat this case separately.

Treat this case separately.
-/
theorem conj_word_one_place {fr : Formalism.HC.Frame} (τ : fr.GG) :
    orderOf fr.cc = 2 ∧ ∀ i : ZMod (orderOf fr.cc), plc (letter τ fr.cc i) = plc τ := by
  refine ⟨fr.orderOf_cc, fun i => ?_⟩
  unfold letter
  generalize i.val = k
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ fr.cc k, ← mul_assoc, cc_comm, plc_cc_mul, ih]

end GlobalTheory.HTW.ConjWord
