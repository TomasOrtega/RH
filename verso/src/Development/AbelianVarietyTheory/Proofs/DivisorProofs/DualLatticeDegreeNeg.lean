import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtOverClosureIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFiniteFreeFinrankLeFourMulDim
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo

variable {p : ℕ} [Fact p.Prime]

def actAf (D : Datum p) (c : D.O) : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  Module.End.baseChangeHom ℚ (AfP p) (VQ D) (actQ D c)

/- English proof (translation)
Use `show LinearMap.baseChange (AfP p) (actQ D c) (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) = _`. Rewrite using `[LinearMap.baseChange_tmul, actQ, LinearMap.baseChange_tmul]`. Both sides reduce to the same expression.
-/
theorem actAf_tmul (D : Datum p) (c : D.O) (a : AfP p) (x : D.La) :
    actAf D c (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) = a ⊗ₜ ((1 : ℚ) ⊗ₜ (c • x)) := by
  show LinearMap.baseChange (AfP p) (actQ D c) (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) = _
  rw [LinearMap.baseChange_tmul, actQ, LinearMap.baseChange_tmul]
  rfl

/- English proof (translation)
The claim follows from `actAf_tmul D c 1 x`.
-/
theorem actAf_inAf (D : Datum p) (c : D.O) (x : D.La) : actAf D c (inAf D x) = inAf D (c • x) :=
  actAf_tmul D c 1 x

/- English proof (translation)
Proceed by induction on `hv using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, x, ha, rfl⟩` from `hz`. Rewrite using `[actAf_tmul]`. Conclude with `AddSubgroup.subset_closure ⟨a, c • x, ha, rfl⟩`.

Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add u w _ _ hu hw => rw [map_add]`. Conclude with `add_mem hu hw`. Consider the case `neg u _ hu => rw [map_neg]`.

Conclude with `neg_mem hu`.
-/
theorem actAf_mem_laHat (D : Datum p) (c : D.O) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    actAf D c v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    rw [actAf_tmul]
    exact AddSubgroup.subset_closure ⟨a, c • x, ha, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [map_add]; exact add_mem hu hw
  | neg u _ hu => rw [map_neg]; exact neg_mem hu

/- English proof (translation)
Establish `key : ∀ z : AfP p ⊗[ℚ] G.C, Commute (actOn L.rep (AfP p) z) (actAf D c)`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero]`. Conclude with `Commute.zero_left _`.

Consider the case `tmul r x`. Establish `h1 : Commute (L.rep x) (actQ D c)` using `(L.rep_range (L.rep x)).1 ⟨x, rfl⟩ c`. Simplify using `only [actOn, Algebra.TensorProduct.lift_tmul]`. Use `Commute.mul_left ?_ ?_` and prove the remaining obligations. Conclude with `Algebra.commute_algebraMap_left r _`.

Conclude with `h1.map (Module.End.baseChangeHom ℚ (AfP p) (VQ D))`. Consider the case `add a b ha hb => rw [map_add]`. Conclude with `ha.add_left hb`. Unfold `Link.actG`. Simplify using `only [MonoidHom.coe_comp, Function.comp_apply]`.

Conclude with `LinearMap.congr_fun (key _).eq v`.
-/
theorem actG_actAf {D : Datum p} {G : HTGroup p} (L : Link D G) (g : G.GAf) (c : D.O)
    (v : AfP p ⊗[ℚ] VQ D) : L.actG g (actAf D c v) = actAf D c (L.actG g v) := by
  have key : ∀ z : AfP p ⊗[ℚ] G.C, Commute (actOn L.rep (AfP p) z) (actAf D c) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Commute.zero_left _
    | tmul r x =>
      have h1 : Commute (L.rep x) (actQ D c) := (L.rep_range (L.rep x)).1 ⟨x, rfl⟩ c
      simp only [actOn, Algebra.TensorProduct.lift_tmul]
      refine Commute.mul_left ?_ ?_
      · exact Algebra.commute_algebraMap_left r _
      · exact h1.map (Module.End.baseChangeHom ℚ (AfP p) (VQ D))
    | add a b ha hb => rw [map_add]; exact ha.add_left hb
  unfold Link.actG
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  exact LinearMap.congr_fun (key _).eq v

end GlobalTheory.LKGeo

namespace GlobalTheory.LKGeo

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.LKGeo
