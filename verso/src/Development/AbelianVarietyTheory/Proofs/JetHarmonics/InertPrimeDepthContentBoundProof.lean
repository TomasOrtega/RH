import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.OddLevelBlockBoundAttainedStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSumsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FlowProgrammeBoundsAndLowLevelOptimumStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodIntegerPlanLowLevelsBoundStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeValueLePlanBlocksStatement

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators

namespace GlobalTheory.InertContent

/- English proof (translation)
Rewrite using `[← Finset.sum_product' (s := Z) (t := Finset.univ) (f := fun z (a : ZMod P.d) => g (P.pos z a.val))]`. Use `Finset.sum_bij (fun p _ => P.pos p.1 p.2.val) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `p hp q hq h`. Take `⟨r, -, hr⟩` from `hZ (P.pos q.1 q.2.val)`. Rewrite using `[hr p ⟨(Finset.mem_product.1 hp).1, h⟩, hr q ⟨(Finset.mem_product.1 hq).1, rfl⟩]`.

Introduce `z _`. Take `⟨r, hr, -⟩` from `hZ z`. Conclude with `⟨r, Finset.mem_product.2 ⟨hr.1, Finset.mem_univ _⟩, hr.2⟩`.
-/
theorem sum_reps (P : RF.Par) (Z : Finset P.Pl) (hZ : RF.IsReps P Z) (g : P.Pl → ℝ) :
    ∑ z ∈ Z, ∑ a : ZMod P.d, g (P.pos z a.val) = ∑ z, g z := by
  classical
  rw [← Finset.sum_product' (s := Z) (t := Finset.univ) (f := fun z (a : ZMod P.d) => g (P.pos z a.val))]
  refine Finset.sum_bij (fun p _ => P.pos p.1 p.2.val) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro p hp q hq h
    obtain ⟨r, -, hr⟩ := hZ (P.pos q.1 q.2.val)
    rw [hr p ⟨(Finset.mem_product.1 hp).1, h⟩, hr q ⟨(Finset.mem_product.1 hq).1, rfl⟩]
  · intro z _
    obtain ⟨r, hr, -⟩ := hZ z
    exact ⟨r, Finset.mem_product.2 ⟨hr.1, Finset.mem_univ _⟩, hr.2⟩

/- English proof (translation)
Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_log {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/- English proof (translation)
Establish `h5 : (5 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `h1 : 1 ≤ Real.log l` using `one_le_log (by linarith)`. Establish `h2 : 0 ≤ Real.log x` using `Real.log_nonneg hx`. Establish `h3 : Real.log x ≤ Real.log y` using `Real.log_le_log (by linarith) hxy`. Unfold `Real.logb`.

Conclude with `(div_le_self h2 h1).trans h3`.
-/
theorem logb_le {l : ℕ} (hl : 5 ≤ l) {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) : Real.logb l x ≤ Real.log y := by
  have h5 : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : 1 ≤ Real.log l := one_le_log (by linarith)
  have h2 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h3 : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hxy
  unfold Real.logb
  exact (div_le_self h2 h1).trans h3

/- English proof (translation)
Unfold `S0`. Apply `Nat.ceil_mono` to reduce the goal to its premises. Establish `: (i : ℝ) ≤ j` using `by exact_mod_cast h`. Use `gcongr`.
-/
theorem mono_resι_var (l n : ℕ) {i j : ℕ} (h : i ≤ j) : S0 l i n ≤ S0 l j n := by
  unfold S0
  apply Nat.ceil_mono
  have : (i : ℝ) ≤ j := by exact_mod_cast h
  gcongr

/- English proof (translation)
Establish `hk' : (4 : ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hn : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1`. Rewrite using `[Nat.cast_sub (by omega)]; simp`. Establish `hL : 1 ≤ Real.log k` using `one_le_log (by linarith)`. Establish `h1 : Real.logb l ((k : ℝ) - 1) ≤ Real.log k` using `logb_le hl (by linarith) (by linarith)`.

Establish `h2 : Real.logb l ((k : ℝ) - 1 + 1) ≤ Real.log k` using `logb_le hl (by linarith) (by linarith)`. Establish `h5 : (1 : ℝ) < l` using `by exact_mod_cast (by omega : 1 < l)`. Establish `h3 : 0 ≤ Real.logb l ((k : ℝ) - 1 + 1)` using `Real.logb_nonneg h5 (by linarith)`. Establish `h4 : (S0 l i (k - 1) : ℝ) ≤ 64 * ((k : ℝ) - 1) ^ 2 * ((i : ℝ) + 3 + 3 * Real.logb l ((k : ℝ) - 1 + 1)) + 1`. Unfold `S0`.

Rewrite using `[hn]`. Conclude with `(Nat.ceil_lt_add_one (by positivity)).le`. Rewrite using `[hn]`. Establish `h6 : 1 ≤ ((k : ℝ) - 1) ^ 2` using `by nlinarith`. Establish `h7 : 64 * ((k : ℝ) - 1) ^ 2 * ((i : ℝ) + 3 + 3 * Real.logb l ((k : ℝ) - 1 + 1)) ≤ 64 * ((k : ℝ) - 1) ^ 2 * (11 * Real.log k)` using `mul_le_mul_of_nonneg_left (by linarith) (by positivity)`.

Establish `h8 : Real.log k ≤ ((k : ℝ) - 1) ^ 2 * Real.log k` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem add_le (l k i : ℕ) (hl : 5 ≤ l) (hk : 4 ≤ k) (hi : (i : ℝ) ≤ 5 * Real.log k) :
    (S0 l i (k - 1) : ℝ) + Real.logb l ((k - 1 : ℕ) : ℝ) + 1 ≤ 707 * ((k : ℝ) - 1) ^ 2 * Real.log k := by
  have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hn : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hL : 1 ≤ Real.log k := one_le_log (by linarith)
  have h1 : Real.logb l ((k : ℝ) - 1) ≤ Real.log k := logb_le hl (by linarith) (by linarith)
  have h2 : Real.logb l ((k : ℝ) - 1 + 1) ≤ Real.log k := logb_le hl (by linarith) (by linarith)
  have h5 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have h3 : 0 ≤ Real.logb l ((k : ℝ) - 1 + 1) := Real.logb_nonneg h5 (by linarith)
  have h4 : (S0 l i (k - 1) : ℝ) ≤
      64 * ((k : ℝ) - 1) ^ 2 * ((i : ℝ) + 3 + 3 * Real.logb l ((k : ℝ) - 1 + 1)) + 1 := by
    unfold S0
    rw [hn]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  rw [hn]
  have h6 : 1 ≤ ((k : ℝ) - 1) ^ 2 := by nlinarith
  have h7 : 64 * ((k : ℝ) - 1) ^ 2 * ((i : ℝ) + 3 + 3 * Real.logb l ((k : ℝ) - 1 + 1)) ≤
      64 * ((k : ℝ) - 1) ^ 2 * (11 * Real.log k) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h8 : Real.log k ≤ ((k : ℝ) - 1) ^ 2 * Real.log k := by nlinarith
  nlinarith

/- English proof (translation)
Establish `h5 : (5 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `h1 : 0 < (l : ℝ) ^ 2 - 1` using `by nlinarith`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by linarith) (by linarith)]; linarith`. Unfold `gam`.

Rewrite using `[← div_eq_mul_inv, div_le_div_iff₀ h1 (by linarith)]; nlinarith`. Unfold `gam`. Check the signs of the components of the expression. Unfold `rho`. Check the signs of the components of the expression.
-/
theorem inv_le {l : ℕ} (hl : 5 ≤ l) : ((l : ℝ) - 1)⁻¹ ≤ 2 * (l : ℝ)⁻¹ ∧ gam l ≤ 2 * (l : ℝ)⁻¹ ∧ 0 ≤ gam l ∧ 0 ≤ rho l := by
  have h5 : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : 0 < (l : ℝ) ^ 2 - 1 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by linarith) (by linarith)]; linarith
  · unfold gam
    rw [← div_eq_mul_inv, div_le_div_iff₀ h1 (by linarith)]; nlinarith
  · unfold gam; positivity
  · unfold rho; positivity

set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `hT0 : 0 < T` using `by linarith`. Establish `hk' : (m : ℝ) + 3 ≤ k` using `by exact_mod_cast hmk`. Establish `hm' : (1 : ℝ) ≤ m` using `by exact_mod_cast hm`. Establish `hn : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1`. Rewrite using `[Nat.cast_sub (by omega)]; simp`.

Establish `hL : 1 ≤ Real.log k` using `one_le_log (by linarith)`. Establish `hi : (i0 k l : ℝ) ≤ 5 * Real.log k`. Use `GlobalTheory.T.levelsUsed_balancedValue_orbitSums.2.1 k l (by omega) hl` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hth : 0 ≤ thl k l`.

Rewrite using `[(GlobalTheory.T.levelsUsed_balancedValue_orbitSums.1 k l (by omega) (by omega)).2.2.2]; positivity`. Establish `hθ1 : 0 ≤ 1 - θ` using `by linarith [hθ.2]`. Take `⟨p, h1, h2, h3⟩` from `GlobalTheory.T.exists_goodIntegerPlan_low_levels_bound l d hl (k - 1) m k (S0 l (i0 k l) (k - 1)) (by omega) (by omega) W (fun a => (1 - θ) * w a / T) Good (fun a => ⟨div_nonneg (mul_nonneg hθ1 (hw a).le) hT0.le, by`. Rewrite using `[div_le_iff₀ hT0]`. Combine the linear relations using `[hlo a]⟩) hG`.

Use `⟨p, h1, h2, ?_⟩` and prove the remaining obligations. Establish `hadd` using `add_le l k (i0 k l) hl (by omega) hi`. Take `⟨g1, g2, g3, g4⟩` from `inv_le hl`. Establish `hD : ∀ a, 0 ≤ ((k : ℝ) - 1) * w a` using `fun a => mul_nonneg (by linarith) (hw a).le`. Take `⟨f1, f2, -⟩` from `GlobalTheory.T.flow_programme_bounds_and_low_level_optimum l d (fun a => ((k : ℝ) - 1) * w a) (by omega) hD`.

Establish `hF0 : 0 ≤ Fnum l d (fun a => ((k : ℝ) - 1) * w a)` using `le_trans (mul_nonneg g4 (Finset.sum_nonneg fun a _ => hD a)) f1`. Establish `hF : Fnum l d (fun a => ((k - 1 : ℕ) : ℝ) * ((1 - θ) * w a / T)) = (1 - θ) / T * Fnum l d (fun a => ((k : ℝ) - 1) * w a)`. Rewrite using `[← f2 _ (div_nonneg hθ1 hT0.le), hn]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Expand and normalize the polynomial expressions, which then agree. Establish `hA : ∑ a, (1 - θ) * w a / T = (1 - θ) * (∑ a, w a) / T`. Rewrite using `[Finset.mul_sum, Finset.sum_div]`. Establish `hB : T * ∑ a, (W a : ℝ) ≤ (∑ a, w a) + d * E`. Rewrite using `[Finset.mul_sum]`.

Use `(Finset.sum_le_sum fun a _ => hhi a).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_add_distrib]`. Simplify using `[ZMod.card]`. Establish `hA0 : 0 ≤ ∑ a, w a` using `Finset.sum_nonneg fun a _ => (hw a).le`. Rewrite `h3` using `[hF, Finset.sum_sub_distrib, hA]`.

Generalize the expression as in `(S0 l (i0 k l) (k - 1) : ℝ) + Real.logb l ((k - 1 : ℕ) : ℝ) + 1 = Q at h3 hadd`. Rewrite `h3` using `[hn]`. Generalize the expression as in `Fnum l d (fun a => ((k : ℝ) - 1) * w a) = F at *`. Generalize the expression as in `∑ a, w a = A at *`. Generalize the expression as in `∑ a, (W a : ℝ) = B at *`.

Generalize the expression as in `Real.log k = L at *`. Generalize the expression as in `thl k l = t at *`. Generalize the expression as in `gam l = γ at *`. Establish `hI : (0 : ℝ) ≤ i0 k l` using `Nat.cast_nonneg _`. Generalize the expression as in `(i0 k l : ℝ) = I at h3 hi hI`.

Establish `h5 : (5 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hu : 0 ≤ ((l : ℝ) - 1)⁻¹` using `inv_nonneg.2 (by linarith)`. Establish `hv : 0 ≤ (l : ℝ)⁻¹` using `inv_nonneg.2 (by linarith)`. Establish `hd : (0 : ℝ) ≤ d` using `Nat.cast_nonneg _`. Establish `h4` using `mul_le_mul_of_nonneg_left h3 hT0.le`.

Establish `e : T * ((1 - θ) / T * F + t * ((k : ℝ) - 1) * ((1 - θ) * A / T) + ((k : ℝ) - 1) * γ * (B - (1 - θ) * A / T) + m * B / ((l : ℝ) - 1) + 2 * I * m * ((1 - θ) * A / T) / ((l : ℝ) - 1) + d * I * (((k : ℝ) - 1) * Q)) = (1 - θ) * F + t * ((k : ℝ) - 1) * ((1 - θ) * A) + ((k : ℝ) - 1) * …`. Generalize the expression as in `((l : ℝ) - 1) = x`. Clear the denominators using the available nonvanishing facts. Rewrite `h4` using `[e]`. Use `h4.trans ?_` and prove the remaining obligations.

Simplify using `only [div_eq_mul_inv]`. Generalize the expression as in `((l : ℝ) - 1)⁻¹ = u at *`. Generalize the expression as in `(l : ℝ)⁻¹ = v at *`. Establish `hN : 0 ≤ (k : ℝ) - 1` using `by linarith`. Establish `hθA : (1 - θ) * A ≤ A` using `mul_le_of_le_one_left hA0 (by linarith only [hθ.1])`.

Establish `hθA0 : 0 ≤ (1 - θ) * A` using `mul_nonneg hθ1 hA0`. Establish `hdE : 0 ≤ d * E` using `mul_nonneg hd hE`. Establish `hmA : 0 ≤ m * A * v` using `by positivity`. Establish `t1 : (1 - θ) * F ≤ F` using `mul_le_of_le_one_left hF0 (by linarith only [hθ.1])`. Establish `t2 : t * ((k : ℝ) - 1) * ((1 - θ) * A) ≤ k * t * A`.

Combine the equalities or inequalities in the displayed calculation. Establish `t3 : ((k : ℝ) - 1) * γ * (T * B - (1 - θ) * A) ≤ 10 * (m * A * v) + 2 * (k * (d * E) * v)`. Combine the equalities or inequalities in the displayed calculation. Use `hθ.1` as an intermediate fact. Use `gcongr`.

Use `_ = 2 * v * ((((k : ℝ) - 1) * θ) * A + ((k : ℝ) - 1) * (d * E)) := by ring`. Use `_ ≤ 2 * v * ((5 * m) * A + k * (d * E)) := by gcongr; linarith`. Use `_ = _ := by ring`. Establish `t4 : m * (T * B) * u ≤ 2 * (m * A * v) + 2 * (k * (d * E) * v)`. Combine the equalities or inequalities in the displayed calculation.

Establish `t5 : 2 * I * m * ((1 - θ) * A) * u ≤ 20 * (L * (m * A * v))`. Combine the equalities or inequalities in the displayed calculation. Establish `t6 : d * (T * I * (((k : ℝ) - 1) * Q)) ≤ d * (3535 * T * ((k : ℝ) - 1) ^ 3 * L ^ 2)`. Use `mul_le_mul_of_nonneg_left ?_ hd` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Establish `t7 : m * A * v ≤ L * (m * A * v)` using `le_mul_of_one_le_left hmA hL`. Combine the linear relations using `only [t1, t2, t3, t4, t5, t6, t7]`.
-/
theorem orbit (l d : ℕ) [NeZero d] (hl : 5 ≤ l) (m k : ℕ) (hmk : m + 3 ≤ k) (hm : 1 ≤ m) (W : ZMod d → ℕ) (w : ZMod d → ℝ)
    (T θ E : ℝ) (hT : 1 ≤ T) (hw : ∀ a, 0 < w a) (hlo : ∀ a, (1 - θ) * w a ≤ T * W a) (hhi : ∀ a, T * W a ≤ w a + E)
    (hE : 0 ≤ E) (hθ : 0 ≤ θ ∧ θ ≤ 1) (hθm : ((k : ℝ) - 1) * θ ≤ 5 * m) (Good : ZMod d → ℕ → Set ℕ)
    (hG : ∀ a, ∀ i ∈ oddLevels d, i < i0 k l → Windows (S0 l (i0 k l) (k - 1)) (Good a i)) :
    ∃ p : Plan l d W, (∀ a i, i0 k l ≤ i → p.y a i = 0) ∧ (∀ a i, p.y a i ≠ 0 → p.y a i ∈ Good a i) ∧
      T * p.bound (k - 1) m ≤ Fnum l d (fun a => ((k : ℝ) - 1) * w a) +
        (32 * Real.log k * m / l + k * thl k l) * (∑ a, w a) +
        d * (4 * k * E / l + 3535 * T * ((k : ℝ) - 1) ^ 3 * Real.log k ^ 2) := by
  have hT0 : 0 < T := by linarith
  have hk' : (m : ℝ) + 3 ≤ k := by exact_mod_cast hmk
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hL : 1 ≤ Real.log k := one_le_log (by linarith)
  have hi : (i0 k l : ℝ) ≤ 5 * Real.log k := by
    have := GlobalTheory.T.levelsUsed_balancedValue_orbitSums.2.1 k l (by omega) hl
    linarith
  have hth : 0 ≤ thl k l := by
    rw [(GlobalTheory.T.levelsUsed_balancedValue_orbitSums.1 k l (by omega) (by omega)).2.2.2]; positivity
  have hθ1 : 0 ≤ 1 - θ := by linarith [hθ.2]
  obtain ⟨p, h1, h2, h3⟩ := GlobalTheory.T.exists_goodIntegerPlan_low_levels_bound l d hl (k - 1) m k (S0 l (i0 k l) (k - 1)) (by omega) (by omega) W
    (fun a => (1 - θ) * w a / T) Good
    (fun a => ⟨div_nonneg (mul_nonneg hθ1 (hw a).le) hT0.le, by
      rw [div_le_iff₀ hT0]; linarith [hlo a]⟩) hG
  refine ⟨p, h1, h2, ?_⟩
  have hadd := add_le l k (i0 k l) hl (by omega) hi
  obtain ⟨g1, g2, g3, g4⟩ := inv_le hl
  have hD : ∀ a, 0 ≤ ((k : ℝ) - 1) * w a := fun a => mul_nonneg (by linarith) (hw a).le
  obtain ⟨f1, f2, -⟩ := GlobalTheory.T.flow_programme_bounds_and_low_level_optimum l d (fun a => ((k : ℝ) - 1) * w a) (by omega) hD
  have hF0 : 0 ≤ Fnum l d (fun a => ((k : ℝ) - 1) * w a) :=
    le_trans (mul_nonneg g4 (Finset.sum_nonneg fun a _ => hD a)) f1
  have hF : Fnum l d (fun a => ((k - 1 : ℕ) : ℝ) * ((1 - θ) * w a / T)) =
      (1 - θ) / T * Fnum l d (fun a => ((k : ℝ) - 1) * w a) := by
    rw [← f2 _ (div_nonneg hθ1 hT0.le), hn]
    congr 1; funext a; ring
  have hA : ∑ a, (1 - θ) * w a / T = (1 - θ) * (∑ a, w a) / T := by
    rw [Finset.mul_sum, Finset.sum_div]
  have hB : T * ∑ a, (W a : ℝ) ≤ (∑ a, w a) + d * E := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun a _ => hhi a).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib]; simp [ZMod.card]
  have hA0 : 0 ≤ ∑ a, w a := Finset.sum_nonneg fun a _ => (hw a).le
  rw [hF, Finset.sum_sub_distrib, hA] at h3
  generalize (S0 l (i0 k l) (k - 1) : ℝ) + Real.logb l ((k - 1 : ℕ) : ℝ) + 1 = Q at h3 hadd
  rw [hn] at h3
  generalize Fnum l d (fun a => ((k : ℝ) - 1) * w a) = F at *
  generalize ∑ a, w a = A at *
  generalize ∑ a, (W a : ℝ) = B at *
  generalize Real.log k = L at *
  generalize thl k l = t at *
  generalize gam l = γ at *
  have hI : (0 : ℝ) ≤ i0 k l := Nat.cast_nonneg _
  generalize (i0 k l : ℝ) = I at h3 hi hI
  have h5 : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hu : 0 ≤ ((l : ℝ) - 1)⁻¹ := inv_nonneg.2 (by linarith)
  have hv : 0 ≤ (l : ℝ)⁻¹ := inv_nonneg.2 (by linarith)
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have h4 := mul_le_mul_of_nonneg_left h3 hT0.le
  have e : T * ((1 - θ) / T * F + t * ((k : ℝ) - 1) * ((1 - θ) * A / T) +
      ((k : ℝ) - 1) * γ * (B - (1 - θ) * A / T) + m * B / ((l : ℝ) - 1) +
      2 * I * m * ((1 - θ) * A / T) / ((l : ℝ) - 1) + d * I * (((k : ℝ) - 1) * Q)) =
      (1 - θ) * F + t * ((k : ℝ) - 1) * ((1 - θ) * A) + ((k : ℝ) - 1) * γ * (T * B - (1 - θ) * A) +
      m * (T * B) * ((l : ℝ) - 1)⁻¹ + 2 * I * m * ((1 - θ) * A) * ((l : ℝ) - 1)⁻¹ + d * (T * I * (((k : ℝ) - 1) * Q)) := by
    generalize ((l : ℝ) - 1) = x
    field_simp
  rw [e] at h4
  refine h4.trans ?_
  simp only [div_eq_mul_inv]
  generalize ((l : ℝ) - 1)⁻¹ = u at *
  generalize (l : ℝ)⁻¹ = v at *
  have hN : 0 ≤ (k : ℝ) - 1 := by linarith
  have hθA : (1 - θ) * A ≤ A := mul_le_of_le_one_left hA0 (by linarith only [hθ.1])
  have hθA0 : 0 ≤ (1 - θ) * A := mul_nonneg hθ1 hA0
  have hdE : 0 ≤ d * E := mul_nonneg hd hE
  have hmA : 0 ≤ m * A * v := by positivity
  have t1 : (1 - θ) * F ≤ F := mul_le_of_le_one_left hF0 (by linarith only [hθ.1])
  have t2 : t * ((k : ℝ) - 1) * ((1 - θ) * A) ≤ k * t * A := by
    calc t * ((k : ℝ) - 1) * ((1 - θ) * A) ≤ t * k * A := by gcongr; linarith
      _ = _ := by ring
  have t3 : ((k : ℝ) - 1) * γ * (T * B - (1 - θ) * A) ≤ 10 * (m * A * v) + 2 * (k * (d * E) * v) := by
    calc ((k : ℝ) - 1) * γ * (T * B - (1 - θ) * A) ≤ ((k : ℝ) - 1) * γ * (θ * A + d * E) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ ((k : ℝ) - 1) * (2 * v) * (θ * A + d * E) := by
          have := hθ.1
          gcongr
      _ = 2 * v * ((((k : ℝ) - 1) * θ) * A + ((k : ℝ) - 1) * (d * E)) := by ring
      _ ≤ 2 * v * ((5 * m) * A + k * (d * E)) := by gcongr; linarith
      _ = _ := by ring
  have t4 : m * (T * B) * u ≤ 2 * (m * A * v) + 2 * (k * (d * E) * v) := by
    calc m * (T * B) * u ≤ m * (A + d * E) * (2 * v) := by gcongr
      _ = 2 * (m * A * v) + 2 * (m * (d * E) * v) := by ring
      _ ≤ _ := by gcongr; linarith
  have t5 : 2 * I * m * ((1 - θ) * A) * u ≤ 20 * (L * (m * A * v)) := by
    calc 2 * I * m * ((1 - θ) * A) * u ≤ 2 * (5 * L) * m * A * (2 * v) := by gcongr
      _ = _ := by ring
  have t6 : d * (T * I * (((k : ℝ) - 1) * Q)) ≤ d * (3535 * T * ((k : ℝ) - 1) ^ 3 * L ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ hd
    calc T * I * (((k : ℝ) - 1) * Q) ≤ T * I * (((k : ℝ) - 1) * (707 * ((k : ℝ) - 1) ^ 2 * L)) := by gcongr
      _ ≤ T * (5 * L) * (((k : ℝ) - 1) * (707 * ((k : ℝ) - 1) ^ 2 * L)) := by gcongr
      _ = _ := by ring
  have t7 : m * A * v ≤ L * (m * A * v) := le_mul_of_one_le_left hmA hL
  linarith only [t1, t2, t3, t4, t5, t6, t7]

/- English proof (translation)
Introduce `C1 hC1`. Use `⟨3535 + 6 * C1, by positivity, ?_⟩` and prove the remaining obligations. Introduce `P l hP _ hl Pk`. Establish `hk : P.m + 3 ≤ P.k` using `hP.mk_le`. Establish `hm` using `hP.m_pos`.

Establish `dg` using `Pk.deg`. Establish `hE : 0 ≤ C1 * P.SE` using `mul_nonneg hC1 hP.SE_nonneg`. Establish `key : ∀ z, ∃ p : Plan l P.d (RF.alongOrb P z Pk.W), z ∈ Pk.Z → (∀ a i, i0 P.k l ≤ i → p.y a i = 0) ∧ (∀ a i, p.y a i ≠ 0 → (RF.GlobalTheory.bi (RF.bg a) a i (p.y a i)).Attains (Pk.R.X z) (Pk.R.F z) (RF.blockBd l (P.k - 1) P.m i (p.y a i))) ∧ Pk.T * p.bound (P.k - 1) P.m ≤ Fnum l …`. Introduce `z`. Distinguish the cases in `hz : z ∈ Pk.Z`.

Establish `hG : ∀ a, ∀ i ∈ oddLevels P.d, i < i0 P.k l → Windows (S0 l (i0 P.k l) (P.k - 1)) {y | (RF.GlobalTheory.bi (RF.bg a) a i y).Attains (Pk.R.X z) (Pk.R.F z) (RF.blockBd l (P.k - 1) P.m i y)}`. Introduce `a i hi hi0`. Establish `halt` using `Pk.alt z hz`. Take `⟨hi1, hi2⟩` from `Finset.mem_filter.1 hi`. Establish `hbig : (Pk.R.X z).big (RF.bg a) a`.

Unfold `RF.bg`. Use `split_ifs with h`. Conclude with `(halt.2 a).2 h`. Use `((Pk.R.X z).big_compl 0 a).2 (fun hb => h ((halt.2 a).1 hb))` as an intermediate fact. Simplify using `using this`.

Establish `hW` using `GlobalTheory.T.oddLevelBlock_bound_attained.2 Pk.R.C Pk.R.V P.d (Pk.R.I z) (Pk.R.J z) (Pk.R.X z) (Pk.R.F z) halt (by rw [Pk.R.hVl]; exact hl) (by rw [(Pk.R.hn z).1]; omega) (RF.bg a) a hbig i hi2 (Finset.mem_range.1 hi1)`. Rewrite `hW` using `[Pk.R.hVl, (Pk.R.hn z).1, (Pk.R.hn z).2]`. Use `⟨hW.1, fun Y0 => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, h1, h2⟩` from `hW.2 Y0`. Use `mono_resι_var l (P.k - 1) hi0.le` as an intermediate fact.

Conclude with `⟨y, hy, h1, by omega⟩`. Take `⟨p, hp⟩` from `orbit l P.d hl P.m P.k hk hm (RF.alongOrb P z Pk.W) (RF.alongOrb P z P.w) Pk.T Pk.θ0 (C1 * P.SE) dg.T_one (fun a => dg.w_pos _) (fun a => dg.TW_lo _) (fun a => dg.TW_hi _) hE dg.th_rng dg.th_m _ hG`. Conclude with `⟨p, fun _ => hp⟩`. Conclude with `⟨Plan.triv _ _ _, fun h => absurd h hz⟩`. Use `choose p hp using key`.

Establish `hν` using `GlobalTheory.T.inertPrime_value_le_planBlocks P l C1 hP hl Pk p (fun z hz => (hp z hz).1) (fun z hz => (hp z hz).2.1)`. Establish `hT0 : 0 < Pk.T` using `by linarith [dg.T_one]`. Establish `h1` using `mul_le_mul_of_nonneg_left hν hT0.le`. Rewrite `h1` using `[mul_add, Finset.mul_sum]`. Establish `h2` using `Finset.sum_le_sum fun z hz => (hp z hz).2.2`.

Establish `s1 : ∑ z ∈ Pk.Z, ∑ a, RF.alongOrb P z P.w a = ∑ z, P.w z` using `sum_reps P Pk.Z Pk.hZ P.w`. Establish `s2 : ∑ z ∈ Pk.Z, (P.d : ℝ) = P.f`. Use `sum_reps P Pk.Z Pk.hZ (fun _ => 1)` as an intermediate fact. Simplify `this` using `[ZMod.card, hP.card]`. Rewrite `h2` using `[Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum Pk.Z (fun z => ∑ a, RF.alongOrb P z P.w a), ← Finset.sum_mul, s1, s2]`.

Establish `hk' : (P.m : ℝ) + 3 ≤ P.k` using `by exact_mod_cast hk`. Establish `hm' : (1 : ℝ) ≤ P.m` using `by exact_mod_cast hm`. Establish `hL : 1 ≤ Real.log P.k` using `one_le_log (by linarith)`. Establish `hth : 0 ≤ thl P.k l`. Rewrite using `[(GlobalTheory.T.levelsUsed_balancedValue_orbitSums.1 P.k l (by omega) (by omega)).2.2.2]; positivity`.

Establish `hA0 : 0 ≤ ∑ z, P.w z` using `Finset.sum_nonneg fun z _ => (dg.w_pos z).le`. Establish `hSE` using `hP.SE_nonneg`. Establish `hN : 0 ≤ (P.k : ℝ) - 1` using `by linarith`. Establish `hr : Pk.T * (Pk.rest / ((l : ℝ) - 1)) ≤ 2 * C1 * (P.f * P.k * P.SE / l)`. Combine the equalities or inequalities in the displayed calculation.

Establish `h5 : (5 : ℝ) ≤ l` using `by exact_mod_cast hl`. Conclude with `mul_le_mul dg.rest_le (inv_le hl).1 (inv_nonneg.2 (by linarith)) (by positivity)`. Use `_ = _ := by ring`. Establish `a1 : 0 ≤ Real.log P.k * P.m * (∑ z, P.w z) / l` using `by positivity`. Establish `a2 : 0 ≤ P.f * P.k * P.SE / l` using `by positivity`.

Establish `a3 : 0 ≤ P.k * thl P.k l * (∑ z, P.w z)` using `by positivity`. Establish `a4 : 0 ≤ Pk.T * P.f * ((P.k : ℝ) - 1) ^ 3 * Real.log P.k ^ 2` using `by positivity`. Establish `e : (32 * Real.log P.k * P.m / l + P.k * thl P.k l) * (∑ z, P.w z) + P.f * (4 * P.k * (C1 * P.SE) / l + 3535 * Pk.T * ((P.k : ℝ) - 1) ^ 3 * Real.log P.k ^ 2) = 32 * (Real.log P.k * P.m * (∑ z, P.w z) / l) + P.k * thl P.k l * (∑ z, P.w z) + 4 * C1 * (P.f * P.k * P.SE / l) + 3535 * …` using `by ring`. Rewrite `h2` using `[add_assoc, e]`. Unfold `errB`.

Establish `b1` using `mul_nonneg hC1 a1`. Establish `b3` using `mul_nonneg hC1 a3`. Establish `b4` using `mul_nonneg hC1 a4`. Establish `b2` using `mul_nonneg hC1 a2`. Combine the linear relations using `only [h1, h2, hr, a1, a2, a3, a4, b1, b2, b3, b4]`.
-/
theorem main : InertBd := by
  intro C1 hC1
  refine ⟨3535 + 6 * C1, by positivity, ?_⟩
  intro P l hP _ hl Pk
  classical
  have hk : P.m + 3 ≤ P.k := hP.mk_le
  have hm := hP.m_pos
  have dg := Pk.deg
  have hE : 0 ≤ C1 * P.SE := mul_nonneg hC1 hP.SE_nonneg
  have key : ∀ z, ∃ p : Plan l P.d (RF.alongOrb P z Pk.W), z ∈ Pk.Z →
      (∀ a i, i0 P.k l ≤ i → p.y a i = 0) ∧
      (∀ a i, p.y a i ≠ 0 → (RF.GlobalTheory.bi (RF.bg a) a i (p.y a i)).Attains (Pk.R.X z) (Pk.R.F z)
        (RF.blockBd l (P.k - 1) P.m i (p.y a i))) ∧
      Pk.T * p.bound (P.k - 1) P.m ≤ Fnum l P.d (fun a => ((P.k : ℝ) - 1) * RF.alongOrb P z P.w a) +
        (32 * Real.log P.k * P.m / l + P.k * thl P.k l) * (∑ a, RF.alongOrb P z P.w a) +
        P.d * (4 * P.k * (C1 * P.SE) / l + 3535 * Pk.T * ((P.k : ℝ) - 1) ^ 3 * Real.log P.k ^ 2) := by
    intro z
    by_cases hz : z ∈ Pk.Z
    · have hG : ∀ a, ∀ i ∈ oddLevels P.d, i < i0 P.k l → Windows (S0 l (i0 P.k l) (P.k - 1))
          {y | (RF.GlobalTheory.bi (RF.bg a) a i y).Attains (Pk.R.X z) (Pk.R.F z) (RF.blockBd l (P.k - 1) P.m i y)} := by
        intro a i hi hi0
        have halt := Pk.alt z hz
        obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
        have hbig : (Pk.R.X z).big (RF.bg a) a := by
          unfold RF.bg
          split_ifs with h
          · exact (halt.2 a).2 h
          · have := ((Pk.R.X z).big_compl 0 a).2 (fun hb => h ((halt.2 a).1 hb))
            simpa using this
        have hW := GlobalTheory.T.oddLevelBlock_bound_attained.2 Pk.R.C Pk.R.V P.d (Pk.R.I z) (Pk.R.J z) (Pk.R.X z) (Pk.R.F z) halt
          (by rw [Pk.R.hVl]; exact hl) (by rw [(Pk.R.hn z).1]; omega) (RF.bg a) a hbig i hi2 (Finset.mem_range.1 hi1)
        rw [Pk.R.hVl, (Pk.R.hn z).1, (Pk.R.hn z).2] at hW
        refine ⟨hW.1, fun Y0 => ?_⟩
        obtain ⟨y, hy, h1, h2⟩ := hW.2 Y0
        have := mono_resι_var l (P.k - 1) hi0.le
        exact ⟨y, hy, h1, by omega⟩
      obtain ⟨p, hp⟩ := orbit l P.d hl P.m P.k hk hm (RF.alongOrb P z Pk.W) (RF.alongOrb P z P.w) Pk.T Pk.θ0 (C1 * P.SE)
        dg.T_one (fun a => dg.w_pos _) (fun a => dg.TW_lo _) (fun a => dg.TW_hi _) hE dg.th_rng dg.th_m _ hG
      exact ⟨p, fun _ => hp⟩
    · exact ⟨Plan.triv _ _ _, fun h => absurd h hz⟩
  choose p hp using key
  have hν := GlobalTheory.T.inertPrime_value_le_planBlocks P l C1 hP hl Pk p (fun z hz => (hp z hz).1) (fun z hz => (hp z hz).2.1)
  have hT0 : 0 < Pk.T := by linarith [dg.T_one]
  have h1 := mul_le_mul_of_nonneg_left hν hT0.le
  rw [mul_add, Finset.mul_sum] at h1
  have h2 := Finset.sum_le_sum fun z hz => (hp z hz).2.2
  have s1 : ∑ z ∈ Pk.Z, ∑ a, RF.alongOrb P z P.w a = ∑ z, P.w z := sum_reps P Pk.Z Pk.hZ P.w
  have s2 : ∑ z ∈ Pk.Z, (P.d : ℝ) = P.f := by
    have := sum_reps P Pk.Z Pk.hZ (fun _ => 1)
    simpa [ZMod.card, hP.card] using this
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum Pk.Z (fun z => ∑ a, RF.alongOrb P z P.w a),
    ← Finset.sum_mul, s1, s2] at h2
  have hk' : (P.m : ℝ) + 3 ≤ P.k := by exact_mod_cast hk
  have hm' : (1 : ℝ) ≤ P.m := by exact_mod_cast hm
  have hL : 1 ≤ Real.log P.k := one_le_log (by linarith)
  have hth : 0 ≤ thl P.k l := by
    rw [(GlobalTheory.T.levelsUsed_balancedValue_orbitSums.1 P.k l (by omega) (by omega)).2.2.2]; positivity
  have hA0 : 0 ≤ ∑ z, P.w z := Finset.sum_nonneg fun z _ => (dg.w_pos z).le
  have hSE := hP.SE_nonneg
  have hN : 0 ≤ (P.k : ℝ) - 1 := by linarith
  have hr : Pk.T * (Pk.rest / ((l : ℝ) - 1)) ≤ 2 * C1 * (P.f * P.k * P.SE / l) := by
    calc Pk.T * (Pk.rest / ((l : ℝ) - 1)) = Pk.T * Pk.rest * ((l : ℝ) - 1)⁻¹ := by ring
      _ ≤ C1 * (P.f * P.k * P.SE) * (2 * (l : ℝ)⁻¹) := by
        have h5 : (5 : ℝ) ≤ l := by exact_mod_cast hl
        exact mul_le_mul dg.rest_le (inv_le hl).1 (inv_nonneg.2 (by linarith)) (by positivity)
      _ = _ := by ring
  have a1 : 0 ≤ Real.log P.k * P.m * (∑ z, P.w z) / l := by positivity
  have a2 : 0 ≤ P.f * P.k * P.SE / l := by positivity
  have a3 : 0 ≤ P.k * thl P.k l * (∑ z, P.w z) := by positivity
  have a4 : 0 ≤ Pk.T * P.f * ((P.k : ℝ) - 1) ^ 3 * Real.log P.k ^ 2 := by positivity
  have e : (32 * Real.log P.k * P.m / l + P.k * thl P.k l) * (∑ z, P.w z) +
      P.f * (4 * P.k * (C1 * P.SE) / l + 3535 * Pk.T * ((P.k : ℝ) - 1) ^ 3 * Real.log P.k ^ 2) =
      32 * (Real.log P.k * P.m * (∑ z, P.w z) / l) + P.k * thl P.k l * (∑ z, P.w z) +
      4 * C1 * (P.f * P.k * P.SE / l) + 3535 * (Pk.T * P.f * ((P.k : ℝ) - 1) ^ 3 * Real.log P.k ^ 2) := by ring
  rw [add_assoc, e] at h2
  unfold errB
  have b1 := mul_nonneg hC1 a1
  have b3 := mul_nonneg hC1 a3
  have b4 := mul_nonneg hC1 a4
  have b2 := mul_nonneg hC1 a2
  linarith only [h1, h2, hr, a1, a2, a3, a4, b1, b2, b3, b4]

end GlobalTheory.InertContent
