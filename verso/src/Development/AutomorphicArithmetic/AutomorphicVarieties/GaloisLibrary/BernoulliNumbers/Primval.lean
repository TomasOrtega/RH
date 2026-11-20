import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

open Finset UpperTheory.V.Bern

/- English proof (translation)
Introduce `R _ N _ χ x`. Distinguish the cases in `hx : IsUnit x`. Use `right`. Take `⟨u, hu⟩` from `ZMod.unitsMap_surjective χ.conductor_dvd_level hx.unit`. Use `⟨u, ?_⟩` and prove the remaining obligations.

Use `conv_rhs => rw [← χ.changeLevel_primitiveCharacter]`. Rewrite using `[DirichletCharacter.changeLevel_eq_cast_of_dvd, ← ZMod.unitsMap_val, hu]`. Simplify using the standard rewrite rules. Conclude with `χ.conductor_dvd_level`. Use `left`.

Conclude with `MulChar.map_nonunit _ hx`.
-/
theorem UpperTheory.V.Bern.b_primval :
    ∀ {R : Type} [CommRing R] {N : ℕ} [NeZero N] (χ : DirichletCharacter R N) (x : ZMod χ.conductor), χ.primitiveCharacter x = 0 ∨ ∃ u : (ZMod N)ˣ, χ.primitiveCharacter x = χ u := by
  intro R _ N _ χ x
  by_cases hx : IsUnit x
  · right
    obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective χ.conductor_dvd_level hx.unit
    refine ⟨u, ?_⟩
    conv_rhs => rw [← χ.changeLevel_primitiveCharacter]
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, ← ZMod.unitsMap_val, hu]
    · simp
    · exact χ.conductor_dvd_level
  · left
    exact MulChar.map_nonunit _ hx
