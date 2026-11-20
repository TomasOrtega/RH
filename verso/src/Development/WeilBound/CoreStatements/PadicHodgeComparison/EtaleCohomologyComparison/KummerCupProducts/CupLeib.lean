import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace CrystallineSemistableComparison.E

open CH

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ P _ _ _ h x y` and use `CrystallineSemistableComparison.P.leibniz P h x y`.
-/
theorem cupLeib : CupLeib.{1} := fun _ _ _ _ _ _ _ P _ _ _ h x y => CrystallineSemistableComparison.P.leibniz P h x y

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ P _ _ _ h x y hx hy` and use `CrystallineSemistableComparison.P.cup_cls P h x y hx hy`.
-/
theorem cupCls : CupCls := fun _ _ _ _ _ _ _ P _ _ _ h x y hx hy => CrystallineSemistableComparison.P.cup_cls P h x y hx hy

/- English proof (translation)
Introduce `_ _ _ _ A p x` and use `((CrystallineSemistableComparison.P.cup_ring A).1 p x).2`.
-/
theorem cupOne : CupOne := fun _ _ _ _ A p x => ((CrystallineSemistableComparison.P.cup_ring A).1 p x).2

/- English proof (translation)
Introduce `R R' _ _ σ C _ A A' m ρ hρ`. Use `⟨?_, fun p q n h x y => ?_⟩` and prove the remaining obligations. Use `congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => ?_))` and prove the remaining obligations. Conclude with `(hρ _ _).trans (map_one (ρ _))`. Conclude with `CrystallineSemistableComparison.P.cup_pull (mulP A) (mulP A') m.G m.τ m.τ m.τ m.nat m.nat m.nat (fun T (a b : A.obj (m.G.obj T)) => by`.

Rewrite using `[hρ, hρ, hρ]`. Conclude with `map_mul (ρ T) a b) h x y`.
-/
theorem morCup : MorCup := by
  intro R R' _ _ σ C _ A A' m ρ hρ
  refine ⟨?_, fun p q n h x y => ?_⟩
  · refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => ?_))
    exact (hρ _ _).trans (map_one (ρ _))
  · exact CrystallineSemistableComparison.P.cup_pull (mulP A) (mulP A') m.G m.τ m.τ m.τ m.nat m.nat m.nat (fun T (a b : A.obj (m.G.obj T)) => by
      rw [hρ, hρ, hρ]; exact map_mul (ρ T) a b) h x y

end CrystallineSemistableComparison.E
