import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffSlotLinearStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

/- English proof (translation)
Introduce `n r _ _ ι _ ρ G₀ G₁ v hd h1`. Establish `hsum : ∀ w, ∑ i, dbar (fun x => (ρ i x : ℂ)) v w = 0`. Introduce `w`. Establish `e : (fun x => ∑ i, (ρ i x : ℂ)) = fun _ => (1 : ℂ)`. Use function extensionality and compare the values at `x`.

Rewrite using `[← Complex.ofReal_sum, h1]`. Simplify using the standard rewrite rules. Establish `hs` using `dbar_sum (t := Finset.univ) (A := fun i x => (ρ i x : ℂ)) (z := v) (fun i _ => Complex.ofRealCLM.differentiableAt.comp v (hd i))`. Rewrite `hs` using `[e, dbar_const]`. Rewrite using `[← ContinuousLinearMap.sum_apply, ← hs]`.

Both sides reduce to the same expression. Establish `hadd : ∀ (K₁ K₀ : EndValuedForm11Coeffs n r) (j : Fin n) (L L' : EndValuedForm11Coeffs n r), mixTop (intersection_update_fsHerm_neg_one K₁ (L + L') K₀ j) = mixTop (intersection_update_fsHerm_neg_one K₁ L K₀ j) + mixTop (intersection_update_fsHerm_neg_one K₁ L' K₀ j)`. Introduce `K₁ K₀ j L L'`. Simplify using `using GlobalTheory.T.polarisedTopChernCoeff_position_linear K₁ K₀ L L' 1 1 j`. Establish `hzero : ∀ (K₁ K₀ : EndValuedForm11Coeffs n r) (j : Fin n), mixTop (intersection_update_fsHerm_neg_one K₁ (0 : EndValuedForm11Coeffs n r) K₀ j) = 0`.

Introduce `K₁ K₀ j`. Simplify using `using GlobalTheory.T.polarisedTopChernCoeff_position_linear K₁ K₀ 0 0 0 0 j`. Establish `hc : ∑ i, cutForm (ρ i) G₀ G₁ v = 0`. Use function extensionality and compare the values at `a b`. Simplify using `only [Finset.sum_apply, cutForm, ← Finset.sum_smul, hsum, zero_smul]`.

Both sides reduce to the same expression. Unfold `corrC`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Set `F : EndValuedForm11Coeffs n r →+ ℂ` to `{ toFun := fun L => mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) L (curvAt G₀ v) j) map_zero' := hzero _ _ _ map_add' := fun L L' => hadd _ _ _ L L' }`.

Establish `hF : ∑ i, mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm (ρ i) G₀ G₁ v) (curvAt G₀ v) j) = F (∑ i, cutForm (ρ i) G₀ G₁ v)`. Rewrite using `[map_sum]`. Both sides reduce to the same expression. Rewrite using `[hF, hc, map_zero]`.
-/
theorem corrC_sum_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ι : Type} [Fintype ι]
    (ρ : ι → V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n), (∀ i, DifferentiableAt ℝ (ρ i) v) →
    (∀ x, ∑ i, ρ i x = 1) → ∑ i, corrC (ρ i) G₀ G₁ v = 0 := by
  intro n r _ _ ι _ ρ G₀ G₁ v hd h1
  have hsum : ∀ w, ∑ i, dbar (fun x => (ρ i x : ℂ)) v w = 0 := by
    intro w
    have e : (fun x => ∑ i, (ρ i x : ℂ)) = fun _ => (1 : ℂ) := by
      funext x; rw [← Complex.ofReal_sum, h1]; simp
    have hs := dbar_sum (t := Finset.univ) (A := fun i x => (ρ i x : ℂ)) (z := v)
      (fun i _ => Complex.ofRealCLM.differentiableAt.comp v (hd i))
    rw [e, dbar_const] at hs
    rw [← ContinuousLinearMap.sum_apply, ← hs]; rfl
  have hadd : ∀ (K₁ K₀ : EndValuedForm11Coeffs n r) (j : Fin n) (L L' : EndValuedForm11Coeffs n r),
      mixTop (intersection_update_fsHerm_neg_one K₁ (L + L') K₀ j) = mixTop (intersection_update_fsHerm_neg_one K₁ L K₀ j) + mixTop (intersection_update_fsHerm_neg_one K₁ L' K₀ j) := by
    intro K₁ K₀ j L L'; simpa using GlobalTheory.T.polarisedTopChernCoeff_position_linear K₁ K₀ L L' 1 1 j
  have hzero : ∀ (K₁ K₀ : EndValuedForm11Coeffs n r) (j : Fin n), mixTop (intersection_update_fsHerm_neg_one K₁ (0 : EndValuedForm11Coeffs n r) K₀ j) = 0 := by
    intro K₁ K₀ j; simpa using GlobalTheory.T.polarisedTopChernCoeff_position_linear K₁ K₀ 0 0 0 0 j
  have hc : ∑ i, cutForm (ρ i) G₀ G₁ v = 0 := by
    funext a b
    simp only [Finset.sum_apply, cutForm, ← Finset.sum_smul, hsum, zero_smul]
    rfl
  unfold corrC
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  let F : EndValuedForm11Coeffs n r →+ ℂ :=
    { toFun := fun L => mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) L (curvAt G₀ v) j)
      map_zero' := hzero _ _ _
      map_add' := fun L L' => hadd _ _ _ L L' }
  have hF : ∑ i, mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm (ρ i) G₀ G₁ v) (curvAt G₀ v) j) =
      F (∑ i, cutForm (ρ i) G₀ G₁ v) := by
    rw [map_sum]; rfl
  rw [hF, hc, map_zero]

end GlobalTheory.GoodTop
