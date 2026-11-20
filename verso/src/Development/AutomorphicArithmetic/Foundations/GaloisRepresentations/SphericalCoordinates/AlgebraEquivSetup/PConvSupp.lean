import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms
open scoped Classical

namespace UpperTheory.Gal.W2.Seed

/- English proof (translation)
Introduce `X _ K f f' g h`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Apply `h` to reduce the goal to its premises. Unfold `conv`.

Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises. Introduce `q`. Assume the negation of the conclusion as `hq`. Take `⟨h1, h2⟩` from `mul_ne_zero_iff.mp hq`. Conclude with `hne _ _ h1 h2 (mul_inv_cancel_left _ _).symm`.
-/
theorem pConvSupp : ConvSupp := by
  intro X _ K f f' g h
  by_contra hne
  push_neg at hne
  apply h
  unfold conv
  apply finsum_eq_zero_of_forall_eq_zero
  intro q
  by_contra hq
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hq
  exact hne _ _ h1 h2 (mul_inv_cancel_left _ _).symm

end UpperTheory.Gal.W2.Seed
