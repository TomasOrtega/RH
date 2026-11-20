import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.Inj

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem filR_anti {K : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) :
    Antitone (FilR p n) :=
  fun _ _ h => GlobalTheory.LogCris.fil_anti _ n h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem filR_zero {K : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) :
    FilR p n 0 = Set.univ :=
  GlobalTheory.LogCris.fil_zero _ n

/- English proof (translation)
Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem filR_pull {K : Type} [CommRing K] {X Y : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of K)}
    {q : Y ⟶ Spec (CommRingCat.of K)} (u : X ⟶ Y) (hu : u ≫ q = p) (n r : ℕ) :
    ∀ x ∈ FilR q n r, pullR n u hu x ∈ FilR p n r := by
  rintro x ⟨z, rfl, hz⟩
  exact ⟨_, rfl, fun s => hz (s ⋙ (smMor u hu).functor)⟩

end CrystallineSemistableComparison.Inj
