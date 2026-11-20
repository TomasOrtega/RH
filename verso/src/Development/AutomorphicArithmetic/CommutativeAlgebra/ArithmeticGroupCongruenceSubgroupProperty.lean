import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel

set_option autoImplicit false

noncomputable section

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open scoped TensorProduct

namespace UpperTheory.Gal.Int.Geo

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [map_add, add_mul, mul_add, ha, hb]`. Consider the case `tmul a c`. Establish `hc : L.rep c * actQ D (algebraMap (𝓞 D.F) D.O x) = actQ D (algebraMap (𝓞 D.F) D.O x) * L.rep c` using `(L.rep_range (L.rep c)).1 ⟨c, rfl⟩ _`.

Establish `hb : (Module.End.baseChangeHom ℚ (AfP p) (VQ D) (L.rep c)) * mulF D x = mulF D x * (Module.End.baseChangeHom ℚ (AfP p) (VQ D) (L.rep c))`. Use `congrArg (Module.End.baseChangeHom ℚ (AfP p) (VQ D)) hc` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul]`. Conclude with `this`. Establish `ht : actOn L.rep (AfP p) (a ⊗ₜ[ℚ] c) = algebraMap (AfP p) (Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) a * Module.End.baseChangeHom ℚ (AfP p) (VQ D) (L.rep c)` using `Algebra.TensorProduct.lift_tmul _ _ _ a c`.

Rewrite using `[ht, mul_assoc, hb, ← mul_assoc, ← mul_assoc, Algebra.commutes]`.
-/
private theorem actOn_comm_mulF (x : 𝓞 D.F) (y : AfP p ⊗[ℚ] G.C) :
    actOn L.rep (AfP p) y * mulF D x = mulF D x * actOn L.rep (AfP p) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, add_mul, mul_add, ha, hb]
  | tmul a c =>
    have hc : L.rep c * actQ D (algebraMap (𝓞 D.F) D.O x) = actQ D (algebraMap (𝓞 D.F) D.O x) * L.rep c :=
      (L.rep_range (L.rep c)).1 ⟨c, rfl⟩ _
    have hb : (Module.End.baseChangeHom ℚ (AfP p) (VQ D) (L.rep c)) * mulF D x =
        mulF D x * (Module.End.baseChangeHom ℚ (AfP p) (VQ D) (L.rep c)) := by
      have := congrArg (Module.End.baseChangeHom ℚ (AfP p) (VQ D)) hc
      rw [map_mul, map_mul] at this
      exact this
    have ht : actOn L.rep (AfP p) (a ⊗ₜ[ℚ] c) = algebraMap (AfP p) (Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) a *
        Module.End.baseChangeHom ℚ (AfP p) (VQ D) (L.rep c) :=
      Algebra.TensorProduct.lift_tmul _ _ _ a c
    rw [ht, mul_assoc, hb, ← mul_assoc, ← mul_assoc, Algebra.commutes]

/- English proof (translation)
The claim follows from `congrArg (fun f : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) => f v) (actOn_comm_mulF L x _)`.
-/
private theorem actG_mulF (g : G.GAf) (x : 𝓞 D.F) (v : AfP p ⊗[ℚ] VQ D) :
    L.actG g (mulF D x v) = mulF D x (L.actG g v) :=
  congrArg (fun f : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) => f v) (actOn_comm_mulF L x _)

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨x, hx, v, hv, rfl⟩` from `hz`. Rewrite using `[actG_mulF]`. Conclude with `AddSubgroup.subset_closure ⟨x, hx, _, hg v hv, rfl⟩`.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`. Consider the case `neg a _ ha => rw [map_neg]`. Conclude with `neg_mem ha`.
-/
private theorem actG_idHat {g : G.GAf} (hg : Integ L g) (𝔟 : Ideal (𝓞 D.F)) {z : AfP p ⊗[ℚ] VQ D}
    (hz : z ∈ idHat D 𝔟) : L.actG g z ∈ idHat D 𝔟 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨x, hx, v, hv, rfl⟩ := hz
    rw [actG_mulF]
    exact AddSubgroup.subset_closure ⟨x, hx, _, hg v hv, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

end UpperTheory.Gal.Int.Geo

open UpperTheory.Gal.Int.Geo in
/- English proof (translation)
Introduce `p _ D G L 𝔫 K₀ hK h u _ hc hu hg`. Use `(hK _).2 ⟨hg, fun v hv => ?_⟩` and prove the remaining obligations. Take `⟨huK, huC⟩` from `(hK u).1 hu`. Establish `huv : L.actG u v ∈ LaHat D` using `integ_of_mem huK v hv`. Establish `e1` using `hc _ huv`.

Establish `e2` using `huC v hv`. Establish `e3` using `actG_idHat L (integ_of_mem hg) 𝔫 (hc v hv)`. Establish `hcomp : L.actG (h * u * h⁻¹) (L.actG h v) = L.actG h (L.actG u v)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`. Simplify using the standard rewrite rules.

Establish `key : L.actG (h * u * h⁻¹) v - v = (L.actG h (L.actG u v) - L.actG u v) + (L.actG u v - v) - L.actG (h * u * h⁻¹) (L.actG h v - v)`. Rewrite using `[map_sub, hcomp]`. Normalize the expressions using the abelian group laws. Rewrite using `[key]`. Conclude with `sub_mem (add_mem e1 e2) e3`.
-/
theorem UpperTheory.arithmeticGroup_congruenceSubgroupProperty : UpperTheory.Gal.Int.Geo.GrpCong := by
  intro p _ D G L 𝔫 K₀ hK h u _ hc hu hg
  refine (hK _).2 ⟨hg, fun v hv => ?_⟩
  obtain ⟨huK, huC⟩ := (hK u).1 hu
  have huv : L.actG u v ∈ LaHat D := integ_of_mem huK v hv
  have e1 := hc _ huv
  have e2 := huC v hv
  have e3 := actG_idHat L (integ_of_mem hg) 𝔫 (hc v hv)
  have hcomp : L.actG (h * u * h⁻¹) (L.actG h v) = L.actG h (L.actG u v) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp
  have key : L.actG (h * u * h⁻¹) v - v = (L.actG h (L.actG u v) - L.actG u v) + (L.actG u v - v)
      - L.actG (h * u * h⁻¹) (L.actG h v - v) := by
    rw [map_sub, hcomp]; abel
  rw [key]
  exact sub_mem (add_mem e1 e2) e3

end
