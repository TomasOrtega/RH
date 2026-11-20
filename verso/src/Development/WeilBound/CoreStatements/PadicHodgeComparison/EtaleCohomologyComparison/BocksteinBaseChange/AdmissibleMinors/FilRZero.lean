import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.Inj

/- English proof (translation)
Introduce `_ _ h` and use `GlobalTheory.LogCris.fil_anti _ n h`.
-/
theorem filR_anti {K : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) :
    Antitone (FilR p n) :=
  fun _ _ h => GlobalTheory.LogCris.fil_anti _ n h

/- English proof (translation)
The claim follows from `GlobalTheory.LogCris.fil_zero _ n`.
-/
theorem filR_zero {K : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) :
    FilR p n 0 = Set.univ :=
  GlobalTheory.LogCris.fil_zero _ n

/- English proof (translation)
Introduce and unpack `x ⟨z, rfl, hz⟩`. Conclude with `⟨_, rfl, fun s => hz (s ⋙ (smMor u hu).functor)⟩`.
-/
theorem filR_pull {K : Type} [CommRing K] {X Y : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of K)}
    {q : Y ⟶ Spec (CommRingCat.of K)} (u : X ⟶ Y) (hu : u ≫ q = p) (n r : ℕ) :
    ∀ x ∈ FilR q n r, pullR n u hu x ∈ FilR p n r := by
  rintro x ⟨z, rfl, hz⟩
  exact ⟨_, rfl, fun s => hz (s ⋙ (smMor u hu).functor)⟩

end CrystallineSemistableComparison.Inj
