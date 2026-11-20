import Mathlib
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff

/- English proof (translation)
Introduce `R H`. Establish `h` using `H.gal_sqd H.conj`. Establish `hc : H.gal H.conj = R.toFrame.cc` using `H.gal.apply_symm_apply _`. Establish `h2 : (R.toFrame.cc).1.2 = -1` using `rfl`. Rewrite `h` using `[hc, h2]`.

Simplify using `using h`.
-/
theorem UpperTheory.Reformulated.B.Rc9.conj_sqrt :
    ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R),
    (H.conj : H.E → H.E) H.sqd =
      -H.sqd := by
  intro R H
  have h := H.gal_sqd H.conj
  have hc : H.gal H.conj = R.toFrame.cc := H.gal.apply_symm_apply _
  have h2 : (R.toFrame.cc).1.2 = -1 := rfl
  rw [hc, h2] at h
  simpa using h
