import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial

namespace Formalism.HermitianLatticeCounting.Final.S6

/- English proof (translation)
Use `first`. Consider the case `exact Formalism.HermitianLatticeCounting.P.wedgeMapInLieAlgebra`. Consider the case `exact Formalism.HermitianLatticeCounting.P.S6e.wedgeMapInLieAlgebra`.
-/
theorem y1 : Formalism.HermitianLatticeCounting.S6.Y1 := by
  first
    | exact Formalism.HermitianLatticeCounting.P.wedgeMapInLieAlgebra
    | exact Formalism.HermitianLatticeCounting.P.S6e.wedgeMapInLieAlgebra
/- English proof (translation)
Use `first`. Consider the case `exact Formalism.HermitianLatticeCounting.P.memOfOrthogonalAnisotropic`. Consider the case `exact Formalism.HermitianLatticeCounting.P.S6e.memOfOrthogonalAnisotropic`.
-/
theorem n0c : Formalism.HermitianLatticeCounting.S6.MemOfOrthogonalAnisotropic := by
  first
    | exact Formalism.HermitianLatticeCounting.P.memOfOrthogonalAnisotropic
    | exact Formalism.HermitianLatticeCounting.P.S6e.memOfOrthogonalAnisotropic
/- English proof (translation)
Use `first`. Consider the case `exact Formalism.HermitianLatticeCounting.P.normalFormZero`. Consider the case `exact Formalism.HermitianLatticeCounting.P.S6e.normalFormZero`.
-/
theorem nFJZero : Formalism.HermitianLatticeCounting.S6.NFJZero := by
  first
    | exact Formalism.HermitianLatticeCounting.P.normalFormZero
    | exact Formalism.HermitianLatticeCounting.P.S6e.normalFormZero

/- English proof (translation)
Use `first`. Consider the case `exact Formalism.HermitianLatticeCounting.P.existsNormalForm`. Consider the case `exact Formalism.HermitianLatticeCounting.P.S6e.existsNormalForm`.
-/
theorem normalForm : Formalism.HermitianLatticeCounting.S6.NormalForm := by
  first
    | exact Formalism.HermitianLatticeCounting.P.existsNormalForm
    | exact Formalism.HermitianLatticeCounting.P.S6e.existsNormalForm

/- English proof (translation)
Use `first`. Consider the case `exact Formalism.HermitianLatticeCounting.P.norm_singular_value_bound`. Consider the case `exact Formalism.HermitianLatticeCounting.P.S6e.norm_singular_value_bound`.
-/
theorem normSgBound : Formalism.HermitianLatticeCounting.S6.NormSgBound := by
  first
    | exact Formalism.HermitianLatticeCounting.P.norm_singular_value_bound
    | exact Formalism.HermitianLatticeCounting.P.S6e.norm_singular_value_bound

/- English proof (translation)
Use `first`. Consider the case `exact Formalism.HermitianLatticeCounting.P.minkowski_number_dvd_factorial`. Consider the case `exact Formalism.HermitianLatticeCounting.P.S6e.minkowski_number_dvd_factorial`.
-/
theorem minkowskiDvdFactorial : Formalism.HermitianLatticeCounting.S6.MinkowskiDvdFactorial := by
  first
    | exact Formalism.HermitianLatticeCounting.P.minkowski_number_dvd_factorial
    | exact Formalism.HermitianLatticeCounting.P.S6e.minkowski_number_dvd_factorial
/- English proof (translation)
Introduce `hMk s f G hG`. Establish `h1` using `(hMk (2 * s * f) G hG).trans (minkowskiDvdFactorial (2 * s * f))`. Establish `h2 : Nat.card G ≤ (2 * (2 * s * f)).factorial` using `Nat.le_of_dvd (Nat.factorial_pos _) h1`. Establish `h3 : (2 * (2 * s * f)).factorial ≤ (4 * s * f) ^ (4 * s * f)`. Establish `e : 2 * (2 * s * f) = 4 * s * f` using `by ring`.

Rewrite using `[e]`. Conclude with `Nat.factorial_le_pow _`. Conclude with `h2.trans h3` after adjusting the coercions.
-/
theorem autBound_of_minkowskiBound : Formalism.HermitianLatticeCounting.S6.MinkowskiBound → Formalism.HermitianLatticeCounting.S6.AutBound := by
  intro hMk s f G hG
  have h1 := (hMk (2 * s * f) G hG).trans (minkowskiDvdFactorial (2 * s * f))
  have h2 : Nat.card G ≤ (2 * (2 * s * f)).factorial := Nat.le_of_dvd (Nat.factorial_pos _) h1
  have h3 : (2 * (2 * s * f)).factorial ≤ (4 * s * f) ^ (4 * s * f) := by
    have e : 2 * (2 * s * f) = 4 * s * f := by ring
    rw [e]
    exact Nat.factorial_le_pow _
  exact_mod_cast h2.trans h3

/- English proof (translation)
Use `first`. Consider the case `exact Formalism.HermitianLatticeCounting.P.exponential_identity`. Consider the case `exact Formalism.HermitianLatticeCounting.P.S6e.exponential_identity`.
-/
theorem expIdentity : Formalism.HermitianLatticeCounting.S6.ExpIdentity := by
  first
    | exact Formalism.HermitianLatticeCounting.P.exponential_identity
    | exact Formalism.HermitianLatticeCounting.P.S6e.exponential_identity
/- English proof (translation)
Use `first`. Consider the case `exact Formalism.HermitianLatticeCounting.P.final_sum_bound`. Consider the case `exact Formalism.HermitianLatticeCounting.P.S6e.final_sum_bound`.
-/
theorem finalSum : Formalism.HermitianLatticeCounting.S6.FinalSum := by
  first
    | exact Formalism.HermitianLatticeCounting.P.final_sum_bound
    | exact Formalism.HermitianLatticeCounting.P.S6e.final_sum_bound

end Formalism.HermitianLatticeCounting.Final.S6
