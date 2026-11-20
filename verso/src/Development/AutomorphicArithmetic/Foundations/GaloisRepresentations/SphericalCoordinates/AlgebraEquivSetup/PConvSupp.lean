import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms
open scoped Classical

namespace UpperTheory.Gal.W2.Seed

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
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
