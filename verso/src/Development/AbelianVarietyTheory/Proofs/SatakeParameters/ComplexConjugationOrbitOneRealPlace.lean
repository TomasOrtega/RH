import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AutomorphicArithmetic.CyclotomicBounds.PlaceOfLetterInjective
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.ConjWord

/- English proof (translation)
The claim follows from `mul_comm _ _`.
-/
theorem cc_comm {fr : Formalism.HC.Frame} (g : fr.GG) : g * fr.cc = fr.cc * g := mul_comm _ _

/- English proof (translation)
The claim follows from `UpperTheory.KStar.Words.placeOf_cc_mul g`.
-/
theorem plc_cc_mul {fr : Formalism.HC.Frame} (g : fr.GG) : plc (fr.cc * g) = plc g := UpperTheory.KStar.Words.placeOf_cc_mul g

/- English proof (translation)
Use `⟨fr.orderOf_cc, fun i => ?_⟩` and prove the remaining obligations. Unfold `letter`. Generalize the expression as in `i.val = k`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih => rw [pow_succ fr.cc k, ← mul_assoc, cc_comm, plc_cc_mul, ih]`.
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
