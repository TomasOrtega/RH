import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobalFunctionsDvrPowers
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobalFunctionsDvrGeneric

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open ReciprocityTheory.ChartRestriction.G.Out

/- English proof (translation)
Introduce `E _ _ _ H V _ _ _ _hcomp t hprop n`. Use `letI : GrpObj t.G := t.grp`. Establish `hsemi : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian t.G` using `t.semi`. Use `haveI : Smooth t.G.hom := hsemi.smooth`. Use `haveI : IsSeparated t.G.hom := hsemi.separated`.

Use `haveI : QuasiCompact t.G.hom := hsemi.quasiCompact`. Take `⟨h1, h2, h3⟩` from `GlobalFunctionsDvrGeneric.powObj_props t.G n`. Use `haveI := h1`. Use `haveI := h2`. Use `haveI := h3`.

Use `haveI := hprop`. Establish `hK` using `GlobalFunctionsDvrPowers.pull_powObj_globalFns hGF (spMap (algebraMap V (FractionRing V))) t.G hsemi n`. Conclude with `GlobalFunctionsDvrGeneric.bij_of_generic (powObj t.G n) hK`.
-/
theorem globalFnsDvr_of_globalFns (hGF : GlobalFnsSt) : GlobalFnsDvrSt := by
  intro E _ _ _ H V _ _ _ _hcomp t hprop n
  letI : GrpObj t.G := t.grp
  have hsemi : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian t.G := t.semi
  haveI : Smooth t.G.hom := hsemi.smooth
  haveI : IsSeparated t.G.hom := hsemi.separated
  haveI : QuasiCompact t.G.hom := hsemi.quasiCompact
  obtain ⟨h1, h2, h3⟩ := GlobalFunctionsDvrGeneric.powObj_props t.G n
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := hprop
  have hK := GlobalFunctionsDvrPowers.pull_powObj_globalFns hGF
    (spMap (algebraMap V (FractionRing V))) t.G hsemi n
  exact GlobalFunctionsDvrGeneric.bij_of_generic (powObj t.G n) hK

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
