import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffSlotLinearStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

/- English proof (translation)
Use `set T : ℕ → ℂ := fun k => mixTop (fun i : Fin n => if (i : ℕ) < k then K₁ else K₀) with hT`. Establish `hterm : ∀ j : Fin n, mixTop (intersection_update_fsHerm_neg_one K₁ (K₁ - K₀) K₀ j) = T ((j : ℕ) + 1) - T j`. Introduce `j`. Establish `hK : K₁ - K₀ = (1 : ℂ) • K₁ + (-1 : ℂ) • K₀`. Rewrite using `[one_smul, neg_one_smul, sub_eq_add_neg]`.

Rewrite using `[hK, GlobalTheory.T.polarisedTopChernCoeff_position_linear K₁ K₀ K₁ K₀ 1 (-1) j, one_mul, neg_one_mul, ← sub_eq_add_neg]`. Use `congr 1`. Simplify using `only [hT]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Unfold `intersection_update_fsHerm_neg_one`. Distinguish the cases in `h1 : i < j`. Establish `: (i : ℕ) < j + 1` using `by have := Fin.lt_def.mp h1; omega`. Simplify using `[h1, this]`. Distinguish the cases in `h2 : i = j`.

Substitute `h2` using the available equality. Simplify using the standard rewrite rules. Establish `h3 : ¬ ((i : ℕ) < j + 1)`. Establish `: j < i` using `lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)`. Use `Fin.lt_def.mp this` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Simplify using `[h1, h2, h3]`. Simplify using `only [hT]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Unfold `intersection_update_fsHerm_neg_one`. Distinguish the cases in `h1 : i < j`. Establish `: (i : ℕ) < j` using `Fin.lt_def.mp h1`. Simplify using `[h1, this]`. Establish `: ¬ ((i : ℕ) < j)` using `fun h => h1 (Fin.lt_def.mpr h)`.

Distinguish the cases in `h2 : i = j`. Simplify using `[h1, h2, this]`. Simplify using `[h1, h2, this]`. Rewrite using `[Finset.sum_congr rfl (fun j _ => hterm j)]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun k => T (k + 1) - T k) n, Finset.sum_range_sub]`.

Establish `e1 : (fun i : Fin n => if (i : ℕ) < n then K₁ else K₀) = fun _ => K₁`. Use function extensionality and compare the values at `i`. Simplify using `[i.isLt]`. Establish `e0 : (fun i : Fin n => if (i : ℕ) < 0 then K₁ else K₀) = fun _ => K₀`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Use `show mixTop _ - mixTop _ = _`. Rewrite using `[e1, e0]`.
-/
theorem sum_mixTop_position_sub {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K₁ K₀ : EndValuedForm11Coeffs n r) :
    ∑ j : Fin n, mixTop (intersection_update_fsHerm_neg_one K₁ (K₁ - K₀) K₀ j) = mixTop (fun _ => K₁) - mixTop fun _ => K₀ := by
  classical
  set T : ℕ → ℂ := fun k => mixTop (fun i : Fin n => if (i : ℕ) < k then K₁ else K₀) with hT
  have hterm : ∀ j : Fin n, mixTop (intersection_update_fsHerm_neg_one K₁ (K₁ - K₀) K₀ j) = T ((j : ℕ) + 1) - T j := by
    intro j
    have hK : K₁ - K₀ = (1 : ℂ) • K₁ + (-1 : ℂ) • K₀ := by
      rw [one_smul, neg_one_smul, sub_eq_add_neg]
    rw [hK, GlobalTheory.T.polarisedTopChernCoeff_position_linear K₁ K₀ K₁ K₀ 1 (-1) j, one_mul, neg_one_mul, ← sub_eq_add_neg]
    congr 1
    · simp only [hT]
      congr 1
      funext i
      unfold intersection_update_fsHerm_neg_one
      by_cases h1 : i < j
      · have : (i : ℕ) < j + 1 := by have := Fin.lt_def.mp h1; omega
        simp [h1, this]
      · by_cases h2 : i = j
        · subst h2; simp
        · have h3 : ¬ ((i : ℕ) < j + 1) := by
            have : j < i := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
            have := Fin.lt_def.mp this; omega
          simp [h1, h2, h3]
    · simp only [hT]
      congr 1
      funext i
      unfold intersection_update_fsHerm_neg_one
      by_cases h1 : i < j
      · have : (i : ℕ) < j := Fin.lt_def.mp h1
        simp [h1, this]
      · have : ¬ ((i : ℕ) < j) := fun h => h1 (Fin.lt_def.mpr h)
        by_cases h2 : i = j
        · simp [h1, h2, this]
        · simp [h1, h2, this]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Fin.sum_univ_eq_sum_range (fun k => T (k + 1) - T k) n, Finset.sum_range_sub]
  have e1 : (fun i : Fin n => if (i : ℕ) < n then K₁ else K₀) = fun _ => K₁ := by
    funext i; simp [i.isLt]
  have e0 : (fun i : Fin n => if (i : ℕ) < 0 then K₁ else K₀) = fun _ => K₀ := by
    funext i; simp
  show mixTop _ - mixTop _ = _
  rw [e1, e0]

end GlobalTheory.GoodTop
