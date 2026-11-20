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

noncomputable section

namespace GlobalTheory.CxForm

/- English proof (translation)
Establish `e : a = algebraMap ℂ (Alt n) ((bas n).repr a ∅)`. Use `(bas n).ext_elem fun S => ?_` and prove the remaining obligations. Rewrite using `[Algebra.algebraMap_eq_smul_one, ← bas_empty, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]`. Use `split_ifs with hS`. Substitute `hS` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[smul_zero]`. Assume the negation of the conclusion as `h0`. Take `⟨h3, h4⟩` from `h₁ S h0`. Use `hS (Finset.eq_empty_of_forall_notMem fun i hi => ?_).symm` and prove the remaining obligations.

Break down `lt_or_ge i.val n with h | h` into its components or cases. Conclude with `Finset.notMem_empty i (Finset.card_eq_zero.1 h3 ▸ Finset.mem_filter.2 ⟨hi, h⟩)`. Conclude with `Finset.notMem_empty i (Finset.card_eq_zero.1 h4 ▸ Finset.mem_filter.2 ⟨hi, h⟩)`. Establish `hs : swap a = a` using `by rw [e, AlgHom.commutes]`. Establish `hr` using `h₂ ∅`.

Rewrite `hr` using `[hs]`. Rewrite using `[Complex.conj_eq_iff_re.1 hr.symm]`. Conclude with `e`.
-/
theorem eq_algebraMap_of_isType_zero {n : ℕ} {a : Alt n} (h₁ : IsType 0 0 a) (h₂ : IsReal a) :
    a = algebraMap ℂ (Alt n) (((bas n).repr a ∅).re : ℂ) := by
  have e : a = algebraMap ℂ (Alt n) ((bas n).repr a ∅) := by
    refine (bas n).ext_elem fun S => ?_
    rw [Algebra.algebraMap_eq_smul_one, ← bas_empty, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply]
    split_ifs with hS
    · subst hS
      simp
    · rw [smul_zero]
      by_contra h0
      obtain ⟨h3, h4⟩ := h₁ S h0
      refine hS (Finset.eq_empty_of_forall_notMem fun i hi => ?_).symm
      rcases lt_or_ge i.val n with h | h
      · exact Finset.notMem_empty i (Finset.card_eq_zero.1 h3 ▸ Finset.mem_filter.2 ⟨hi, h⟩)
      · exact Finset.notMem_empty i (Finset.card_eq_zero.1 h4 ▸ Finset.mem_filter.2 ⟨hi, h⟩)
  have hs : swap a = a := by rw [e, AlgHom.commutes]
  have hr := h₂ ∅
  rw [hs] at hr
  rw [Complex.conj_eq_iff_re.1 hr.symm]
  exact e

/- English proof (translation)
Set `t : M → ℝ` to `fun y => ((bas n).repr (α ⟨((A.cover y).choose, y), (A.cover y).choose_spec⟩) ∅).re`. Establish `e (x : A.Pt) : α x = algebraMap ℂ (Alt n) (t x.pt : ℂ)`. Set `x' : A.Pt` to `⟨((A.cover x.pt).choose, x.pt), (A.cover x.pt).choose_spec⟩`. Establish `h₁` using `eq_algebraMap_of_isType_zero (hα.2 x').1 (hα.2 x').2`. Conclude with `(hα.1.compat x x' rfl).trans ((congrArg _ h₁).trans (AlgHom.commutes _ _))`.

Use `⟨t, fun i => ?_, funext e⟩` and prove the remaining obligations. Use `(Complex.reCLM.contDiff.comp_contDiffOn (hα.1.smooth i ∅)).congr fun v hv => ?_` and prove the remaining obligations. Establish `h₁ : A.loc α i v = algebraMap ℂ (Alt n) (t ((A.e i).symm v) : ℂ)`. Rewrite using `[HolAtlas.loc, dif_pos hv]`. Conclude with `e ⟨(i, (A.e i).symm v), (A.e i).map_target hv⟩`.

Simplify using `[h₁, Algebra.algebraMap_eq_smul_one, ← bas_empty, -Complex.coe_smul]`.
-/
theorem HolAtlas.IsRealForm.exists_fn {M : Type} [TopologicalSpace M] {n : ℕ} {A : HolAtlas M n} {α : A.Fld}
    (hα : A.IsRealForm 0 α) :
    ∃ t : M → ℝ, (∀ i, ContDiffOn ℝ ∞ (t ∘ (A.e i).symm) (A.e i).target) ∧ α = A.fn t := by
  let t : M → ℝ := fun y => ((bas n).repr (α ⟨((A.cover y).choose, y), (A.cover y).choose_spec⟩) ∅).re
  have e (x : A.Pt) : α x = algebraMap ℂ (Alt n) (t x.pt : ℂ) := by
    let x' : A.Pt := ⟨((A.cover x.pt).choose, x.pt), (A.cover x.pt).choose_spec⟩
    have h₁ := eq_algebraMap_of_isType_zero (hα.2 x').1 (hα.2 x').2
    exact (hα.1.compat x x' rfl).trans ((congrArg _ h₁).trans (AlgHom.commutes _ _))
  refine ⟨t, fun i => ?_, funext e⟩
  refine (Complex.reCLM.contDiff.comp_contDiffOn (hα.1.smooth i ∅)).congr fun v hv => ?_
  have h₁ : A.loc α i v = algebraMap ℂ (Alt n) (t ((A.e i).symm v) : ℂ) := by
    rw [HolAtlas.loc, dif_pos hv]
    exact e ⟨(i, (A.e i).symm v), (A.e i).map_target hv⟩
  simp [h₁, Algebra.algebraMap_eq_smul_one, ← bas_empty, -Complex.coe_smul]

/- English proof (translation)
Introduce `k _ X p D h σ α hα`. Take `⟨t, ht, e⟩` from `hα.exists_fn`. Use `⟨t, fun y => ?_, e⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `(h.atlas σ).cover y`. Conclude with `cInfAt_of_chart isOpen_univ c ((ht c).mono fun _ hv => hv.1) hc trivial`.
-/
theorem IsRegVar.exists_cInfAt_of_isRealForm_zero : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ) (h : IsRegVar p D) (σ : k →+* ℂ) (α : (h.atlas σ).Fld), (h.atlas σ).IsRealForm 0 α → ∃ t : CxPts p σ → ℝ, (∀ y, CInfAt t y) ∧ α = (h.atlas σ).fn t := by
  intro k _ X p D h σ α hα
  obtain ⟨t, ht, e⟩ := hα.exists_fn
  refine ⟨t, fun y => ?_, e⟩
  obtain ⟨c, hc⟩ := (h.atlas σ).cover y
  exact cInfAt_of_chart isOpen_univ c ((ht c).mono fun _ hv => hv.1) hc trivial

end GlobalTheory.CxForm
