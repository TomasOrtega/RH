import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralLinearRelationZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessianOfCombinationMetricLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReDetRelation
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

namespace GlobalTheory.MixFun

/- English proof (translation)
Use `set A := Finsupp.linearCombination ℝ v`. Use `set F := Finsupp.linearCombination ℝ f`. Establish `hker : LinearMap.ker A ≤ LinearMap.ker F` using `fun c hc => h c hc`. Take `⟨g, hg⟩` from `LinearMap.exists_extend (((LinearMap.ker A).liftQ F hker).comp A.quotKerEquivRange.symm.toLinearMap)`. Use `⟨g, fun a => ?_⟩` and prove the remaining obligations.

Establish `e1 : v a = A (Finsupp.single a 1)` using `by simp [A]`. Establish `e2` using `LinearMap.congr_fun hg ⟨A (Finsupp.single a 1), LinearMap.mem_range_self _ _⟩`. Rewrite using `[e1]`. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image, Submodule.liftQ_apply] at e2`. Rewrite using `[e2]`.

Simplify using `[F]`.
-/
theorem exists_linear_of_rel {α V : Type} [AddCommGroup V] [Module ℝ V] (v : α → V) (f : α → ℝ)
    (h : ∀ c : α →₀ ℝ, Finsupp.linearCombination ℝ v c = 0 → Finsupp.linearCombination ℝ f c = 0) :
    ∃ Ψ : V →ₗ[ℝ] ℝ, ∀ a, Ψ (v a) = f a := by
  set A := Finsupp.linearCombination ℝ v
  set F := Finsupp.linearCombination ℝ f
  have hker : LinearMap.ker A ≤ LinearMap.ker F := fun c hc => h c hc
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    (((LinearMap.ker A).liftQ F hker).comp A.quotKerEquivRange.symm.toLinearMap)
  refine ⟨g, fun a => ?_⟩
  have e1 : v a = A (Finsupp.single a 1) := by simp [A]
  have e2 := LinearMap.congr_fun hg ⟨A (Finsupp.single a 1), LinearMap.mem_range_self _ _⟩
  rw [e1]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.liftQ_apply] at e2
  rw [e2]
  simp [F]

end GlobalTheory.MixFun

namespace GlobalTheory.MixFun

/- English proof (translation)
Introduce `k _ Y _ q hq e ι _ L M r hr hint`. Use `hq.finite` as an intermediate fact. Use `haveI : Finite (k →+* ℂ) := .of_equiv _ (RingHom.equivIntAlgHom k ℂ).symm`. Use `letI := Fintype.ofFinite (k →+* ℂ)`. Use `GlobalTheory.MixFun.exists_linear_of_rel (fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ e) (fun n => (comb L n).archInt M e hr) ?_` and prove the remaining obligations.

Introduce `c hc`. Rewrite `hc`, the goal using `[Finsupp.linearCombination_apply, Finsupp.sum]`. Simplify using `only [HermLB.archInt, finsum_eq_sum_of_fintype, smul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_coe_sort c.support]`. Use `GlobalTheory.ChernLinRel.sum_chernInt_eq_zero k Y q hq.isProjOver σ e c.support (fun j => c j) (fun j => comb L j) ?_ _ _ (fun j => hint j σ)` and prove the remaining obligations. Introduce `ch y hy`. Establish `key : ∀ n : ι → ℤ, ch.chernDens ((comb L n).φ σ) y = e.factorial / Real.pi ^ e * (Matrix.det (∑ l, ((n l : ℝ) : ℂ) • ch.hess ((L l).φ σ) (pick ((L l).φ σ).isLB y) y)).re`. Introduce `n`.

Rewrite using `[AlgChart.chernDens, GlobalTheory.Mean4O.ReadsProj.hess_comb L n σ ch hy _ (mem_pick _ y) _ (fun l => mem_pick _ y)]`. Simplify using `only [key]`. Establish `hrel : ∑ j : c.support, MvPolynomial.C (c j) * (∑ i, MvPolynomial.C ((j.1 i : ℝ)) * MvPolynomial.X i : MvPolynomial ι ℝ) ^ e = 0`. Rewrite using `[← hc, ← Finset.sum_coe_sort c.support]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[MvPolynomial.C_mul']`. Both sides reduce to the same expression. Establish `h0` using `GlobalTheory.MxDet.re_det_relation ι c.support e (fun j => c j) (fun j i => (j.1 i : ℝ)) hrel (fun l => ch.hess ((L l).φ σ) (pick ((L l).φ σ).isLB y) y)`. Repeatedly rewrite using `[mul_left_comm _ ((e.factorial : ℝ) / Real.pi ^ e)]`. Rewrite using `[← Finset.mul_sum, h0, mul_zero]`.
-/
theorem exists_functional_archInt : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (e : ℕ) (ι : Type) [Fintype ι] (L : ι → HermLB q) (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ n, (comb L n).ArchIntegrable M e hr) → ∃ Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ n : ι → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ e) = (comb L n).archInt M e hr := by
  intro k _ Y _ q hq e ι _ L M r hr hint
  classical
  have := hq.finite
  haveI : Finite (k →+* ℂ) := .of_equiv _ (RingHom.equivIntAlgHom k ℂ).symm
  letI := Fintype.ofFinite (k →+* ℂ)
  refine GlobalTheory.MixFun.exists_linear_of_rel (fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ e)
    (fun n => (comb L n).archInt M e hr) ?_
  intro c hc
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hc ⊢
  simp only [HermLB.archInt, finsum_eq_sum_of_fintype, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [← Finset.sum_coe_sort c.support]
  refine GlobalTheory.ChernLinRel.sum_chernInt_eq_zero k Y q hq.isProjOver σ e c.support (fun j => c j)
    (fun j => comb L j) ?_ _ _ (fun j => hint j σ)
  intro ch y hy
  have key : ∀ n : ι → ℤ, ch.chernDens ((comb L n).φ σ) y = e.factorial / Real.pi ^ e *
      (Matrix.det (∑ l, ((n l : ℝ) : ℂ) • ch.hess ((L l).φ σ) (pick ((L l).φ σ).isLB y) y)).re := by
    intro n
    rw [AlgChart.chernDens, GlobalTheory.Mean4O.ReadsProj.hess_comb L n σ ch hy _ (mem_pick _ y) _ (fun l => mem_pick _ y)]
  simp only [key]
  have hrel : ∑ j : c.support, MvPolynomial.C (c j) *
      (∑ i, MvPolynomial.C ((j.1 i : ℝ)) * MvPolynomial.X i : MvPolynomial ι ℝ) ^ e = 0 := by
    rw [← hc, ← Finset.sum_coe_sort c.support]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.C_mul']
    rfl
  have h0 := GlobalTheory.MxDet.re_det_relation ι c.support e (fun j => c j) (fun j i => (j.1 i : ℝ)) hrel
    (fun l => ch.hess ((L l).φ σ) (pick ((L l).φ σ).isLB y) y)
  simp_rw [mul_left_comm _ ((e.factorial : ℝ) / Real.pi ^ e)]
  rw [← Finset.mul_sum, h0, mul_zero]

end GlobalTheory.MixFun
