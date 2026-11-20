import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

/- English proof (translation)
Take `⟨a, rfl⟩ : ∃ a, Spec.map a = κ` from `⟨_, Spec.map_preimage κ⟩`. Take `⟨a', rfl⟩ : ∃ a, Spec.map a = κ'` from `⟨_, Spec.map_preimage κ'⟩`. Establish `e : Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ a) = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ a')`. Rewrite using `[Spec.map_comp, Spec.map_comp]`. Conclude with `h.trans h'.symm`.

Establish `e2` using `Spec.map_injective e`. Use `congr 1`. Use `ext1`. Apply `IsLocalization.ringHom_ext (nonZeroDivisors R)` to reduce the goal to its premises. Conclude with `congrArg CommRingCat.Hom.hom e2`.
-/
theorem genPt_map_unique {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V)
    (κ κ' : Sp (FractionRing V) ⟶ Sp (FractionRing R)) (h : κ ≫ jK R = jK V ≫ spMap θ)
    (h' : κ' ≫ jK R = jK V ≫ spMap θ) : κ = κ' := by
  obtain ⟨a, rfl⟩ : ∃ a, Spec.map a = κ := ⟨_, Spec.map_preimage κ⟩
  obtain ⟨a', rfl⟩ : ∃ a, Spec.map a = κ' := ⟨_, Spec.map_preimage κ'⟩
  have e : Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ a) =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ a') := by
    rw [Spec.map_comp, Spec.map_comp]
    exact h.trans h'.symm
  have e2 := Spec.map_injective e
  congr 1
  ext1
  apply IsLocalization.ringHom_ext (nonZeroDivisors R)
  exact congrArg CommRingCat.Hom.hom e2

end GlobalTheory.TInj
