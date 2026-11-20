import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar BottChern ArRing ArChow HolAtlas Alt IsType IsReal dens chPart tdPart hermMat eval₂ bas relCot dRel IsRelAcyclic IsGenSmooth)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

namespace GlobalTheory.CxForm

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.
-/
theorem bas_univ_one : bas 1 Finset.univ = dz 0 * dzb 0 := by
  rw [← bas_pair]
  congr 1

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem vol_one : (vol 1 : Alt 1) = (Complex.I / 2) • bas 1 Finset.univ := by
  rw [bas_univ_one, vol, Fin.prod_univ_one, Subalgebra.coe_smul]
  rfl

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem repr_univ_one (α : Alt 1) : (bas 1).repr α Finset.univ = Complex.I / 2 * dens α := by
  have hI : Complex.I / 2 ≠ 0 := by simp
  rw [dens, vol_one, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
    _root_.mul_one, mul_div_cancel₀ _ hI]

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Evaluate the decidable proposition. A detailed English derivation is pending.
-/
theorem IsType.repr_eq_zero_one {α : Alt 1} (h : IsType 1 1 α) {S : Finset (Fin (1 + 1))} (hS : S ≠ Finset.univ) :
    (bas 1).repr α S = 0 := by
  by_contra h0
  have := h S h0
  revert hS this
  clear h0
  revert S
  decide

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem IsType.eq_smul_one {α : Alt 1} (h : IsType 1 1 α) :
    α = (bas 1).repr α Finset.univ • bas 1 Finset.univ := by
  refine (bas 1).ext_elem fun S => ?_
  rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, smul_eq_mul]
  by_cases hS : S = Finset.univ
  · rw [hS, Finsupp.single_eq_same, _root_.mul_one]
  · rw [h.repr_eq_zero_one hS, Finsupp.single_eq_of_ne hS, mul_zero]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem swap_bas_univ_one : swap (bas 1 Finset.univ) = -bas 1 Finset.univ := by
  rw [bas_univ_one, map_mul, (swap_dz 0).1, (swap_dz 0).2, dz, dzb]
  exact eq_neg_of_add_eq_zero_right (ExteriorAlgebra.ι_add_mul_swap _ _)

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Apply the first step, then apply the next step to every resulting obligation. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem dens_re_one {α : Alt 1} (h : IsType 1 1 α) (hr : IsReal α) : ((dens α).re : ℂ) = dens α := by
  have e := hr Finset.univ
  conv_lhs at e => rw [h.eq_smul_one]
  rw [map_smul, swap_bas_univ_one, map_smul, map_neg, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.neg_apply,
    Finsupp.single_eq_same, repr_univ_one] at e
  have e' := congrArg Complex.re e
  simp only [smul_eq_mul, Complex.conj_re] at e'
  simp at e'
  apply Complex.ext <;> simp
  linarith

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem repr_const_add_eq_curveForm : ∀ (t : ℝ) (α : Alt 1), IsType 1 1 α → IsReal α → ⇑((bas 1).repr (algebraMap ℂ (Alt 1) t + α)) = curveForm t (dens α).re := by
  intro t α h hr
  funext S
  have hne : (∅ : Finset (Fin (1 + 1))) ≠ Finset.univ := by decide
  rw [map_add, Finsupp.add_apply, Algebra.algebraMap_eq_smul_one, ← bas_empty, map_smul, Module.Basis.repr_self,
    Finsupp.smul_apply, smul_eq_mul, curveForm]
  split_ifs with h₁ h₂
  · rw [h₁, Finsupp.single_eq_same, h.repr_eq_zero_one hne, _root_.mul_one, add_zero]
  · rw [h₂, Finsupp.single_eq_of_ne hne.symm, mul_zero, zero_add, repr_univ_one, dens_re_one h hr]
  · rw [Finsupp.single_eq_of_ne h₁, h.repr_eq_zero_one h₂, mul_zero, add_zero]

end GlobalTheory.CxForm
