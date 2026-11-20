import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

/- English proof (translation)
Introduce `Z X V f y hE`. Establish `hP : IsInitial (pullback f y)` using `isInitialOfIsEmpty`. Use `⟨0, Fin.elim0, fun j => j.elim0, ?_⟩` and prove the remaining obligations. Use `⟨⟨hP.to _, ?_, hP.hom_ext _ _⟩⟩` and prove the remaining obligations. Apply `Sigma.hom_ext` to reduce the goal to its premises.

Introduce `j`. Conclude with `j.elim0`.
-/
theorem splits_of_isEmpty_pullback : ∀ {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X),
    IsEmpty (pullback f y : Scheme.{0}) → GlobalTheory.EtC.Tr.Splits f y := by
  intro Z X V f y hE
  have hP : IsInitial (pullback f y) := isInitialOfIsEmpty
  refine ⟨0, Fin.elim0, fun j => j.elim0, ?_⟩
  refine ⟨⟨hP.to _, ?_, hP.hom_ext _ _⟩⟩
  apply Sigma.hom_ext
  intro j
  exact j.elim0

end GlobalTheory.EtC.Tr
