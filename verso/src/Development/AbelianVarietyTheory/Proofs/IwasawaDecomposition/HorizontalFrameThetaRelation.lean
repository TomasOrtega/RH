import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrRatio
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqPf

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.RayEv
open Formalism.MainNotions.DIV.Cons (SCF intO)

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.RayEv

namespace GlobalTheory.RayEv.CocRatio

open Formalism.MainNotions.ModuliIntegralCharts.H1

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem gam_injective (B : Type) [CommRing B] : Function.Injective (GaugeR.gam B) := fun u v huv => by
  have := congrArg (toΓ B) huv
  simpa [GaugeR.gam, toΓ] using this

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem gs_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (y : Sp B) (a : A) :
    gs (spMap f) y ⊤ (toΓ A a) = gs (𝟙 (Sp B)) y ⊤ (toΓ B (f a)) := by
  have e : ((spMap f).app ⊤).hom (toΓ A a) = toΓ B (f a) := by
    apply gam_injective
    rw [GaugeR.gam_pull, GaugeR.gam_toΓ, GaugeR.gam_toΓ]
  have := gs_pull (𝟙 _) (spMap f) y ⊤ trivial (toΓ A a)
  rw [Category.id_comp, e] at this
  exact this.symm

end GlobalTheory.RayEv.CocRatio
