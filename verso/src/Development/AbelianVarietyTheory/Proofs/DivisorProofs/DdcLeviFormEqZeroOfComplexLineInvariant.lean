import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory

/- English proof (translation)
Distinguish the cases in `hd : DifferentiableAt ℝ f x`. Establish `hl : HasDerivAt (fun t : ℝ => x + t • (c • ξ)) (c • ξ) 0`. Simplify using `using ((hasDerivAt_id (0 : ℝ)).smul_const (c • ξ)).const_add x`. Establish `hx : x + (0 : ℝ) • (c • ξ) = x` using `by simp`. Establish `hd' : DifferentiableAt ℝ f (x + (0 : ℝ) • (c • ξ))` using `by rw [hx]; exact hd`.

Establish `h1` using `hd'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl`. Rewrite `h1` using `[hx]`. Establish `hconst : (fun t : ℝ => f (x + t • (c • ξ))) = fun _ => f x`. Use function extensionality and compare the values at `t`. Rewrite using `[← smul_assoc]`.

Conclude with `hf x _`. Establish `h2 : HasDerivAt (fun t : ℝ => f (x + t • (c • ξ))) 0 0`. Rewrite using `[hconst]`. Conclude with `hasDerivAt_const _ _`. Conclude with `h1.unique h2`.

Rewrite using `[fderiv_zero_of_not_differentiableAt hd]`. Both sides reduce to the same expression.
-/
theorem fderiv_smul_eq_zero_of_invariant {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (ξ : E) (hf : ∀ (x : E) (c : ℂ), f (x + c • ξ) = f x) (x : E) (c : ℂ) :
    fderiv ℝ f x (c • ξ) = 0 := by
  by_cases hd : DifferentiableAt ℝ f x
  · have hl : HasDerivAt (fun t : ℝ => x + t • (c • ξ)) (c • ξ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (c • ξ)).const_add x
    have hx : x + (0 : ℝ) • (c • ξ) = x := by simp
    have hd' : DifferentiableAt ℝ f (x + (0 : ℝ) • (c • ξ)) := by rw [hx]; exact hd
    have h1 := hd'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rw [hx] at h1
    have hconst : (fun t : ℝ => f (x + t • (c • ξ))) = fun _ => f x := by
      funext t
      rw [← smul_assoc]
      exact hf x _
    have h2 : HasDerivAt (fun t : ℝ => f (x + t • (c • ξ))) 0 0 := by
      rw [hconst]; exact hasDerivAt_const _ _
    exact h1.unique h2
  · rw [fderiv_zero_of_not_differentiableAt hd]; rfl

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `n u z ξ η hu hinv`. Establish `hinv' : ∀ (x : V n) (c : ℂ), (fun y => ((u y : ℝ) : ℂ)) (x + c • ξ) = (fun y => ((u y : ℝ) : ℂ)) x`. Introduce `x c`. Simplify using `only [hinv x c]`. Establish `hdbar : (fun x => dbar (fun y => ((u y : ℝ) : ℂ)) x ξ) = fun _ => 0`.

Use function extensionality and compare the values at `x`. Rewrite using `[dbar_apply]`. Establish `h1` using `fderiv_smul_eq_zero_of_invariant (fun y => ((u y : ℝ) : ℂ)) ξ hinv' x 1`. Establish `h2` using `fderiv_smul_eq_zero_of_invariant (fun y => ((u y : ℝ) : ℂ)) ξ hinv' x Complex.I`. Rewrite `h1` using `[one_smul]`.

Rewrite using `[h1, h2]`. Simplify using the standard rewrite rules. Establish `hL1 : leviForm u z η ξ = 0`. Rewrite using `[leviForm_eq_del_dbar hu, hdbar, del_const]`. Both sides reduce to the same expression.

Establish `hL2 : leviForm u z ξ η = 0`. Rewrite using `[← leviForm_conj_symm hu, hL1, map_zero]`. Establish `e : ∀ a b, ddc u z a b = kappa * leviForm u z a b` using `fun a b => rfl`. Conclude with `⟨by rw [e, hL2, mul_zero], by rw [e, hL1, mul_zero]⟩`.
-/
theorem ddc_eq_zero_of_invariant : ∀ (n : ℕ) (u : V n → ℝ) (z ξ η : V n), ContDiffAt ℝ 2 u z → (∀ (x : V n) (c : ℂ), u (x + c • ξ) = u x) → ddc u z ξ η = 0 ∧ ddc u z η ξ = 0 := by
  intro n u z ξ η hu hinv
  have hinv' : ∀ (x : V n) (c : ℂ), (fun y => ((u y : ℝ) : ℂ)) (x + c • ξ) = (fun y => ((u y : ℝ) : ℂ)) x := by
    intro x c; simp only [hinv x c]
  have hdbar : (fun x => dbar (fun y => ((u y : ℝ) : ℂ)) x ξ) = fun _ => 0 := by
    funext x
    rw [dbar_apply]
    have h1 := fderiv_smul_eq_zero_of_invariant (fun y => ((u y : ℝ) : ℂ)) ξ hinv' x 1
    have h2 := fderiv_smul_eq_zero_of_invariant (fun y => ((u y : ℝ) : ℂ)) ξ hinv' x Complex.I
    rw [one_smul] at h1
    rw [h1, h2]; simp
  have hL1 : leviForm u z η ξ = 0 := by
    rw [leviForm_eq_del_dbar hu, hdbar, del_const]; rfl
  have hL2 : leviForm u z ξ η = 0 := by
    rw [← leviForm_conj_symm hu, hL1, map_zero]
  have e : ∀ a b, ddc u z a b = kappa * leviForm u z a b := fun a b => rfl
  exact ⟨by rw [e, hL2, mul_zero], by rw [e, hL1, mul_zero]⟩

end GlobalTheory
