import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarCohomologousEvenFormsAlgebraClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumsDbarCohomologousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormNewtonIdentitiesCurvaturePowerSumsStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

/- English proof (translation)
Introduce `M _ n A r _ _ G G' hG j`. Take `⟨h1, -, halg⟩` from `GlobalTheory.T.dbarCohomologousEvenForms_algebra_closed M n A`. Establish `hpow` using `GlobalTheory.T.curvaturePowerSums_dbarCohomologous M n A r G G' hG`. Establish `hzero : DbarCoh A 0 0`. Use `(halg 0 1 1 1 1 h1 h1).1` as an intermediate fact.

Simplify using `using this`. Establish `hsum : ∀ (s : Finset ℕ) (w w' : ℕ → A.Pt → Ev n), (∀ i ∈ s, DbarCoh A (w i) (w' i)) → DbarCoh A (∑ i ∈ s, w i) (∑ i ∈ s, w' i)`. Introduce `s w w' h`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hzero`.

Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `(halg 0 _ _ _ _ (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).2.1`. Establish `key : ∀ (H : M → M → Matrix r r ℂ) (j : ℕ), 0 < j → chernFld A H j = (j : ℂ)⁻¹ • ((-1 : ℂ) • ∑ i ∈ Finset.range j, (-kappa) ^ (i + 1) • (powFld A H (i + 1) * chernFld A H (j - 1 - i)))`. Introduce `H j hj`.

Use function extensionality and compare the values at `x`. Use `(GlobalTheory.T.chernForm_newton_identities_curvature_power_sums n r (fun v => H x.pt (x.ch.symm v)) x.crd).2 j` as an intermediate fact. Simplify using `only [Pi.smul_apply, Finset.sum_apply, Pi.mul_apply, chernFld, powFld, HolAtlas.chern]`. Rewrite using `[neg_one_smul, ← this, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hj.ne'), one_smul]`. Establish `key0 : ∀ H : M → M → Matrix r r ℂ, chernFld A H 0 = 1`.

Introduce `H`. Use function extensionality and compare the values at `x`. Conclude with `(GlobalTheory.T.chernForm_newton_identities_curvature_power_sums n r _ x.crd).1`. Proceed by induction on `j using Nat.strong_induction_on with`. Consider the case `_ j ih`.

Break down `Nat.eq_zero_or_pos j with rfl | hj` into its components or cases. Rewrite using `[key0, key0]`. Conclude with `h1`. Rewrite using `[key G j hj, key G' j hj]`. Use `(halg _ _ _ _ _ ?_ h1).1` and prove the remaining obligations.

Use `(halg _ _ _ _ _ ?_ h1).1` and prove the remaining obligations. Use `hsum _ _ _ fun i hi => ?_` and prove the remaining obligations. Use `(halg _ _ _ _ _ ?_ h1).1` and prove the remaining obligations. Conclude with `(halg 0 _ _ _ _ (hpow (i + 1)) (ih _ (by simp at hi; omega))).2.2`.
-/
theorem dbarCoh_chernFld : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r]
    [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ j, DbarCoh A (chernFld A G j) (chernFld A G' j) := by
  intro M _ n A r _ _ G G' hG j
  obtain ⟨h1, -, halg⟩ := GlobalTheory.T.dbarCohomologousEvenForms_algebra_closed M n A
  have hpow := GlobalTheory.T.curvaturePowerSums_dbarCohomologous M n A r G G' hG
  have hzero : DbarCoh A 0 0 := by
    have := (halg 0 1 1 1 1 h1 h1).1
    simpa using this
  have hsum : ∀ (s : Finset ℕ) (w w' : ℕ → A.Pt → Ev n), (∀ i ∈ s, DbarCoh A (w i) (w' i)) →
      DbarCoh A (∑ i ∈ s, w i) (∑ i ∈ s, w' i) := by
    intro s w w' h
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (halg 0 _ _ _ _ (h a (Finset.mem_insert_self _ _))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).2.1
  have key : ∀ (H : M → M → Matrix r r ℂ) (j : ℕ), 0 < j → chernFld A H j = (j : ℂ)⁻¹ • ((-1 : ℂ) •
      ∑ i ∈ Finset.range j, (-kappa) ^ (i + 1) • (powFld A H (i + 1) * chernFld A H (j - 1 - i))) := by
    intro H j hj
    funext x
    have := (GlobalTheory.T.chernForm_newton_identities_curvature_power_sums n r (fun v => H x.pt (x.ch.symm v)) x.crd).2 j
    simp only [Pi.smul_apply, Finset.sum_apply, Pi.mul_apply, chernFld, powFld, HolAtlas.chern]
    rw [neg_one_smul, ← this, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hj.ne'), one_smul]
  have key0 : ∀ H : M → M → Matrix r r ℂ, chernFld A H 0 = 1 := by
    intro H; funext x
    exact (GlobalTheory.T.chernForm_newton_identities_curvature_power_sums n r _ x.crd).1
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [key0, key0]; exact h1
    · rw [key G j hj, key G' j hj]
      refine (halg _ _ _ _ _ ?_ h1).1
      refine (halg _ _ _ _ _ ?_ h1).1
      refine hsum _ _ _ fun i hi => ?_
      refine (halg _ _ _ _ _ ?_ h1).1
      exact (halg 0 _ _ _ _ (hpow (i + 1)) (ih _ (by simp at hi; omega))).2.2

/- English proof (translation)
The claim follows from `dbarCoh_chernFld`.
-/
example : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r] [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ j, DbarCoh A (chernFld A G j) (chernFld A G' j) := dbarCoh_chernFld

end GlobalTheory.ChernCalc
