import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelSetDiagNormOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRapidDecaySiegelGLOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSmoothAdelicFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import GroundTheory.AutomorphicForms.ReductionFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDirac
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section
open scoped ContDiff

namespace GlobalTheory.SmoothClosure

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Take `⟨u, hu⟩` from `id hx`. Establish `e : x = toL u.val` using `hu.symm`. Substitute `e` using the available equality. Rewrite using `[chart_val, lieD, chart_mul]`. Establish `e1 : lmul (toL u.val) (oneL E a) = toL u.val` using `mul_one u.val`.

Rewrite using `[fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL u.val)).differentiableAt, e1, ContinuousLinearMap.fderiv]`. Rewrite using `[ContinuousLinearMap.comp_apply]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `Z = u.val * ((Matrix.of (toL u.val))⁻¹ * Matrix.of Z)`. Establish `: (Matrix.of (toL u.val))⁻¹ = (↑(u⁻¹) : Matrix (Fin a) (Fin a) (Cinf E))`.

Express the relevant statement in the definitionally equal form `(u.val)⁻¹ = _`. Rewrite using `[Matrix.coe_units_inv]`. Rewrite using `[this, ← mul_assoc, Units.mul_inv, one_mul]`. Both sides reduce to the same expression.
-/
theorem fderiv_chart_apply (F : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a)
    (hd : DifferentiableAt ℝ (chart F g) x) (Z : Lie E a) :
    fderiv ℝ (chart F g) x Z = chart (lieD (toL ((Matrix.of x)⁻¹ * Matrix.of Z)) F) g x := by
  obtain ⟨u, hu⟩ := id hx
  have e : x = toL u.val := hu.symm
  subst e
  rw [chart_val, lieD, chart_mul]
  have e1 : lmul (toL u.val) (oneL E a) = toL u.val := mul_one u.val
  rw [fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL u.val)).differentiableAt, e1, ContinuousLinearMap.fderiv]
  rw [ContinuousLinearMap.comp_apply]
  congr 1
  change Z = u.val * ((Matrix.of (toL u.val))⁻¹ * Matrix.of Z)
  have : (Matrix.of (toL u.val))⁻¹ = (↑(u⁻¹) : Matrix (Fin a) (Fin a) (Cinf E)) := by
    change (u.val)⁻¹ = _
    rw [Matrix.coe_units_inv]
  rw [this, ← mul_assoc, Units.mul_inv, one_mul]
  rfl

/- English proof (translation)
Take `⟨u, hu⟩` from `id hx`. Establish `e : x = toL u.val` using `hu.symm`. Substitute `e` using the available equality. Simplify using `only [chart_val, lieD]`. Use `conv_lhs => rw [← b.sum_repr W]`.

Rewrite using `[map_sum]`. Simplify using `only [map_smul]`.
-/
theorem chart_lieD_basis {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (Lie E a)) (F : GA E a → ℂ) (g : GA E a)
    {x : Lie E a} (hx : x ∈ invSet E a) (W : Lie E a) :
    chart (lieD W F) g x = ∑ k, b.repr W k • chart (lieD (b k) F) g x := by
  obtain ⟨u, hu⟩ := id hx
  have e : x = toL u.val := hu.symm
  subst e
  simp only [chart_val, lieD]
  conv_lhs => rw [← b.sum_repr W]
  rw [map_sum]
  simp only [map_smul]

/- English proof (translation)
Introduce `E _ _ _ a S hdiff hlie`. Set `b` to `Module.finBasis ℝ (Lie E a)`. Establish `key : ∀ n : ℕ, ∀ F ∈ S, ∀ g : GA E a, ContDiffOn ℝ n (chart F g) (invSet E a)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Introduce `F hF g`. Conclude with `contDiffOn_zero.2 (hdiff F hF g).continuousOn`. Consider the case `succ n ih`. Introduce `F hF g`.

Rewrite using `[Nat.cast_succ]`. Use `contDiffOn_succ_of_fderiv_apply (hdiff F hF g) (by simp) fun Z => ?_` and prove the remaining obligations. Establish `hc : ∀ k, ContDiffOn ℝ n (fun x : Lie E a => (b.coord k).toContinuousLinearMap (rmul Z (toL (Matrix.of x)⁻¹))) (invSet E a)` using `fun k => (b.coord k).toContinuousLinearMap.contDiff.comp_contDiffOn ((rmul Z).contDiff.comp_contDiffOn (GlobalTheory.GLFin.Inhab.contDiffOn_invL.of_le (by exact_mod_cast le_top)))`. Establish `hsum : ContDiffOn ℝ n (fun x => ∑ k ∈ Finset.univ, (b.coord k).toContinuousLinearMap (rmul Z (toL (Matrix.of x)⁻¹)) • chart (lieD (b k) F) g x) (invSet E a)` using `ContDiffOn.sum fun k _ => (hc k).smul (ih _ (hlie F hF (b k)) g)`. Use `hsum.congr fun x hx => ?_` and prove the remaining obligations.

Rewrite using `[fderivWithin_of_isOpen isOpen_invSet hx, fderiv_chart_apply F g hx ((hdiff F hF g).differentiableAt (isOpen_invSet.mem_nhds hx)) Z, chart_lieD_basis b F g hx]`. Both sides reduce to the same expression. Introduce `F hF g`. Conclude with `contDiffOn_infty.2 fun n => key n F hF g`.
-/
theorem le_Sm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Submodule ℂ (GA E a → ℂ)),
    (∀ F ∈ S, ∀ g : GA E a, DifferentiableOn ℝ (chart F g) (invSet E a)) →
    (∀ F ∈ S, ∀ X : Lie E a, lieD X F ∈ S) → S ≤ Sm E a := by
  intro E _ _ _ a S hdiff hlie
  let b := Module.finBasis ℝ (Lie E a)
  have key : ∀ n : ℕ, ∀ F ∈ S, ∀ g : GA E a, ContDiffOn ℝ n (chart F g) (invSet E a) := by
    intro n
    induction n with
    | zero =>
      intro F hF g
      exact contDiffOn_zero.2 (hdiff F hF g).continuousOn
    | succ n ih =>
      intro F hF g
      rw [Nat.cast_succ]
      refine contDiffOn_succ_of_fderiv_apply (hdiff F hF g) (by simp) fun Z => ?_
      have hc : ∀ k, ContDiffOn ℝ n (fun x : Lie E a =>
          (b.coord k).toContinuousLinearMap (rmul Z (toL (Matrix.of x)⁻¹))) (invSet E a) := fun k =>
        (b.coord k).toContinuousLinearMap.contDiff.comp_contDiffOn
          ((rmul Z).contDiff.comp_contDiffOn (GlobalTheory.GLFin.Inhab.contDiffOn_invL.of_le (by exact_mod_cast le_top)))
      have hsum : ContDiffOn ℝ n (fun x => ∑ k ∈ Finset.univ, (b.coord k).toContinuousLinearMap
          (rmul Z (toL (Matrix.of x)⁻¹)) • chart (lieD (b k) F) g x) (invSet E a) :=
        ContDiffOn.sum fun k _ => (hc k).smul (ih _ (hlie F hF (b k)) g)
      refine hsum.congr fun x hx => ?_
      rw [fderivWithin_of_isOpen isOpen_invSet hx,
        fderiv_chart_apply F g hx ((hdiff F hF g).differentiableAt (isOpen_invSet.mem_nhds hx)) Z,
        chart_lieD_basis b F g hx]
      rfl
  intro F hF g
  exact contDiffOn_infty.2 fun n => key n F hF g

end GlobalTheory.SmoothClosure
