import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

/- English proof (translation)
Establish `h2` using `PreTilt.mk_untilt_eq_coeff_zero (((frobeniusEquiv (Per.Fl l) l).symm^[n]) e)`. Establish `h3` using `PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n e`. Rewrite `h3` using `[zero_add]`. Rewrite using `[← h3, ← h2]`. Both sides reduce to the same expression.
-/
theorem coeff_eq_mk_rootT {l : ℕ} [Fact l.Prime] (e : Per.Fl l) (n : ℕ) :
    PreTilt.coeff n e = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (rootT e n) := by
  have h2 := PreTilt.mk_untilt_eq_coeff_zero (((frobeniusEquiv (Per.Fl l) l).symm^[n]) e)
  have h3 := PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n e
  rw [zero_add] at h3
  rw [← h3, ← h2]
  rfl

/- English proof (translation)
Introduce `_ _ C n` and use `coeff_eq_mk_rootT C.ε n`.
-/
theorem eps_coeff : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (n : ℕ),
    PreTilt.coeff n C.ε = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (rootT C.ε n) :=
  fun _ _ C n => coeff_eq_mk_rootT C.ε n

end GlobalTheory.MemLoc
