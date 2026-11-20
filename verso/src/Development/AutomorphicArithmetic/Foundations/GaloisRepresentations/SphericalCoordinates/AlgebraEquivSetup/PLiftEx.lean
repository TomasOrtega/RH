import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

/- English proof (translation)
Unfold `UpperTheory.Gal.W2.Seed.LiftEx`. Introduce `E _ _ τ₀`. Set `sA : E →ₐ[ℚ] AlgebraicClosure ℚ` to `IsAlgClosed.lift`. Use `letI : Algebra E (AlgebraicClosure ℚ) := sA.toRingHom.toAlgebra`. Use `letI : Algebra E ℂ := τ₀.toAlgebra`.

Use `haveI : IsScalarTower ℚ E (AlgebraicClosure ℚ) := IsScalarTower.of_algebraMap_eq (fun x => (sA.commutes x).symm)`. Use `haveI hQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ`. Use `haveI : Algebra.IsAlgebraic E (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) E`. Set `iA : AlgebraicClosure ℚ →ₐ[E] ℂ` to `IsAlgClosed.lift`. Use `⟨sA.toRingHom, iA.toRingHom, fun x => ?_⟩` and prove the remaining obligations.

Conclude with `iA.commutes x`.
-/
theorem UpperTheory.Gal.W2.Seed.pLiftEx :
    LiftEx := by
  unfold UpperTheory.Gal.W2.Seed.LiftEx
  intro E _ _ τ₀
  let sA : E →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  letI : Algebra E (AlgebraicClosure ℚ) := sA.toRingHom.toAlgebra
  letI : Algebra E ℂ := τ₀.toAlgebra
  haveI : IsScalarTower ℚ E (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun x => (sA.commutes x).symm)
  haveI hQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic E (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  let iA : AlgebraicClosure ℚ →ₐ[E] ℂ := IsAlgClosed.lift
  refine ⟨sA.toRingHom, iA.toRingHom, fun x => ?_⟩
  exact iA.commutes x
