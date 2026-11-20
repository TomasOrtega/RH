import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSchurHomogeneous
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalMulOfIsHomogeneous

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qh65.aeval_mul_of_isHomogeneous hP y g`.
-/
private theorem aeval_mul_of_isHomogeneous {σ R : Type} [Fintype σ] [CommRing R] [Algebra ℚ R]
    {P : MvPolynomial σ ℚ} {d : ℕ} (hP : P.IsHomogeneous d) (y : R) (g : σ → R) :
    aeval (fun k => y * g k) P = y ^ d * aeval g P :=
  _root_.UpperTheory.Reformulated.B.Qh65.aeval_mul_of_isHomogeneous hP y g

/- English proof (translation)
Introduce `R _ _ n lam g y`. Unfold `sch`. Conclude with `aeval_mul_of_isHomogeneous (GroundTheory.Heights₂.Heights.RestTerms.SchSchurHomogeneous.proof (Fin n) n lam) y g`.
-/
theorem schurHomog : SchurHomog := by
  intro R _ _ n lam g y
  unfold sch
  exact aeval_mul_of_isHomogeneous
    (GroundTheory.Heights₂.Heights.RestTerms.SchSchurHomogeneous.proof (Fin n) n lam) y g

end UpperTheory.Gal.Schur
