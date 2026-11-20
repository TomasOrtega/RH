import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY.LinComb

open Polynomial in

/- English proof (translation)
Set `q : Y → ℂ[X]` to `fun P => ∑ k : Fin N, C (v P k) * X ^ (k : ℕ)`. Establish `hcoeff : ∀ P (k : Fin N), (q P).coeff k = v P k`. Introduce `P k`. Simplify using `only [q, finset_sum_coeff, coeff_C_mul_X_pow, Fin.val_inj]`. Simplify using the standard rewrite rules.

Establish `hq : ∀ P ∈ T, q P ≠ 0`. Introduce `P hP h0`. Apply `hv P hP` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Use `hcoeff P k` as an intermediate fact.

Rewrite `this` using `[h0, coeff_zero]`. Simplify using `using this.symm`. Take `⟨x, hx⟩` from `Infinite.exists_notMem_finset (T.biUnion fun P => (q P).roots.toFinset)`. Use `⟨x, fun P hP h => hx ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_biUnion]`.

Use `⟨P, hP, ?_⟩` and prove the remaining obligations. Rewrite using `[Multiset.mem_toFinset, mem_roots (hq P hP), IsRoot.def]`. Simplify using `only [q, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]`. Rewrite using `[← h]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`.
-/
theorem exists_pow_ne_zero {Y : Type} (N : ℕ) (T : Finset Y) (v : Y → Fin N → ℂ)
    (hv : ∀ P ∈ T, v P ≠ 0) : ∃ x : ℂ, ∀ P ∈ T, ∑ k : Fin N, x ^ (k : ℕ) * v P k ≠ 0 := by
  classical
  let q : Y → ℂ[X] := fun P => ∑ k : Fin N, C (v P k) * X ^ (k : ℕ)
  have hcoeff : ∀ P (k : Fin N), (q P).coeff k = v P k := by
    intro P k
    simp only [q, finset_sum_coeff, coeff_C_mul_X_pow, Fin.val_inj]
    simp
  have hq : ∀ P ∈ T, q P ≠ 0 := by
    intro P hP h0
    apply hv P hP
    funext k
    have := hcoeff P k
    rw [h0, coeff_zero] at this
    simpa using this.symm
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (T.biUnion fun P => (q P).roots.toFinset)
  refine ⟨x, fun P hP h => hx ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨P, hP, ?_⟩
  rw [Multiset.mem_toFinset, mem_roots (hq P hP), IsRoot.def]
  simp only [q, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end GlobalTheory.OTY.LinComb

/- English proof (translation)
Introduce `n Y _ _ _ _ _ ι La _ A L N s T hs hT`. Take `⟨x, hx⟩` from `GlobalTheory.OTY.LinComb.exists_pow_ne_zero N T (fun P k => s k (A.pick P) P) (by`. Introduce `P hP h0`. Apply `hT P hP` to reduce the goal to its premises. Introduce `k`.

Conclude with `congrFun h0 k)`. Use `⟨fun i y => ∑ k : Fin N, x ^ (k : ℕ) * s k i y, ⟨?_, ?_⟩, fun P hP => hx P hP, ?_⟩` and prove the remaining obligations. Introduce `i`. Establish `: ((fun y => ∑ k : Fin N, x ^ (k : ℕ) * s k i y) ∘ (A.chart i).symm) = ∑ k : Fin N, (fun v => x ^ (k : ℕ) * (s k i ∘ (A.chart i).symm) v)`. Use function extensionality and compare the values at `v`.

Simplify using `[Finset.sum_apply]`. Rewrite using `[this]`. Conclude with `DifferentiableOn.sum fun k _ => ((hs k).1 i).const_mul _`. Introduce `i j y hy hi hj`. Simplify using `only`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[(hs k).2 i j y hy hi hj]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨1 + ∑ k : Fin N, ‖x ^ (k : ℕ)‖ ^ 2, by positivity, fun y => ?_⟩` and prove the remaining obligations.

Simplify using `only [WeightedAtlas.nsq, WeightedAtlas.sqn]`. Rewrite using `[← Finset.sum_mul, ← mul_assoc]`. Apply `mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le` to reduce the goal to its premises. Establish `h1 : ‖∑ k : Fin N, x ^ (k : ℕ) * s k (A.pick y) y‖ ≤ ∑ k : Fin N, ‖x ^ (k : ℕ)‖ * ‖s k (A.pick y) y‖`. Use `(norm_sum_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations.

Conclude with `Finset.sum_congr rfl fun k _ => norm_mul _ _`. Establish `h2` using `Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k : Fin N => ‖x ^ (k : ℕ)‖) (fun k => ‖s k (A.pick y) y‖)`. Establish `h3 : 0 ≤ ∑ k : Fin N, ‖s k (A.pick y) y‖ ^ 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem GlobalTheory.OTY.exists_linComb_ne_zero_on_finset : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (L : La) (N : ℕ) (s : Fin N → ι → Y → ℂ) (T : Finset Y), (∀ k, A.IsSec L (s k)) → (∀ P ∈ T, P ∉ A.zeroSet s) → ∃ s' : ι → Y → ℂ, A.IsSec L s' ∧ (∀ P ∈ T, s' (A.pick P) P ≠ 0) ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, A.nsq L s' y ≤ C * A.sqn L s y := by
  intro n Y _ _ _ _ _ ι La _ A L N s T hs hT
  classical
  obtain ⟨x, hx⟩ := GlobalTheory.OTY.LinComb.exists_pow_ne_zero N T (fun P k => s k (A.pick P) P) (by
    intro P hP h0
    apply hT P hP
    intro k
    exact congrFun h0 k)
  refine ⟨fun i y => ∑ k : Fin N, x ^ (k : ℕ) * s k i y, ⟨?_, ?_⟩, fun P hP => hx P hP, ?_⟩
  · intro i
    have : ((fun y => ∑ k : Fin N, x ^ (k : ℕ) * s k i y) ∘ (A.chart i).symm)
        = ∑ k : Fin N, (fun v => x ^ (k : ℕ) * (s k i ∘ (A.chart i).symm) v) := by
      funext v; simp [Finset.sum_apply]
    rw [this]
    exact DifferentiableOn.sum fun k _ => ((hs k).1 i).const_mul _
  · intro i j y hy hi hj
    simp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hs k).2 i j y hy hi hj]
    ring
  · refine ⟨1 + ∑ k : Fin N, ‖x ^ (k : ℕ)‖ ^ 2, by positivity, fun y => ?_⟩
    simp only [WeightedAtlas.nsq, WeightedAtlas.sqn]
    rw [← Finset.sum_mul, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have h1 : ‖∑ k : Fin N, x ^ (k : ℕ) * s k (A.pick y) y‖ ≤ ∑ k : Fin N, ‖x ^ (k : ℕ)‖ * ‖s k (A.pick y) y‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun k _ => norm_mul _ _
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k : Fin N => ‖x ^ (k : ℕ)‖)
      (fun k => ‖s k (A.pick y) y‖)
    have h3 : 0 ≤ ∑ k : Fin N, ‖s k (A.pick y) y‖ ^ 2 := by positivity
    calc ‖∑ k : Fin N, x ^ (k : ℕ) * s k (A.pick y) y‖ ^ 2
        ≤ (∑ k : Fin N, ‖x ^ (k : ℕ)‖ * ‖s k (A.pick y) y‖) ^ 2 := by gcongr
      _ ≤ (∑ k : Fin N, ‖x ^ (k : ℕ)‖ ^ 2) * ∑ k : Fin N, ‖s k (A.pick y) y‖ ^ 2 := h2
      _ ≤ (1 + ∑ k : Fin N, ‖x ^ (k : ℕ)‖ ^ 2) * ∑ k : Fin N, ‖s k (A.pick y) y‖ ^ 2 := by
        gcongr; linarith
