import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelChartPoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RelChartPoly

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

/- English proof (translation)
Establish `h` using `monomial_mem_relSecM R y (b := e) (fun q : Σ k, ι k => if q.2 = c q.1 then e q.1 else 0) (fun k => by simp)`. Use `h using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `[pow_ite]`.
-/
theorem chartMonomial_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ e k ∈ relSecM R y e := by
  classical
  have h := monomial_mem_relSecM R y (b := e) (fun q : Σ k, ι k => if q.2 = c q.1 then e q.1 else 0)
    (fun k => by simp)
  convert h using 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp [pow_ite]

/- English proof (translation)
Establish `h` using `chartMonomial_mem R y (Function.update c p.1 p.2) (Pi.single p.1 1)`. Use `h using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Finset.prod_eq_single p.1]`. Simplify using the standard rewrite rules. Introduce `k _ hk`.

Simplify using `[hk]`. Simplify using the standard rewrite rules.
-/
theorem coord_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) [DecidableEq K] :
    y p ∈ relSecM R y (Pi.single p.1 1) := by
  have h := chartMonomial_mem R y (Function.update c p.1 p.2) (Pi.single p.1 1)
  convert h using 1
  rw [Finset.prod_eq_single p.1]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

/- English proof (translation)
Distinguish the cases in `h0 : y ⟨p.1, c p.1⟩ = 0`. Simplify using `[h0]`. Establish `hW : ∏ k, y ⟨k, c k⟩ = (∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 (1 : ℕ) : K → ℕ) k) * ∏ k, y ⟨k, c k⟩ ^ (if k = p.1 then 0 else 1)`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[← pow_add]`. Distinguish the cases in `hk : k = p.1`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hk]`.

Establish `h1 : ∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 (1 : ℕ) : K → ℕ) k = y ⟨p.1, c p.1⟩`. Rewrite using `[Finset.prod_eq_single p.1]`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Simplify using `[hk]`.

Simplify using the standard rewrite rules. Establish `hmem` using `mul_mem_relSecM R y (coord_mem R y c p) (chartMonomial_mem R y c (fun k => if k = p.1 then 0 else 1))`. Establish `hb : (Pi.single p.1 1 + fun k => if k = p.1 then 0 else 1 : K → ℕ) = fun _ => 1`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = p.1`.

Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hk]`. Rewrite `hmem` using `[hb]`. Rewrite using `[hW, h1, ← mul_assoc, div_mul_cancel₀ _ h0]`.

Conclude with `hmem`.
-/
theorem generator_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) :
    y p / y ⟨p.1, c p.1⟩ * ∏ k, y ⟨k, c k⟩ ∈ relSecM R y (fun _ => 1) := by
  classical
  by_cases h0 : y ⟨p.1, c p.1⟩ = 0
  · simp [h0]
  have hW : ∏ k, y ⟨k, c k⟩ = (∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 (1 : ℕ) : K → ℕ) k) *
      ∏ k, y ⟨k, c k⟩ ^ (if k = p.1 then 0 else 1) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_add]
    by_cases hk : k = p.1
    · subst hk; simp
    · simp [hk]
  have h1 : ∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 (1 : ℕ) : K → ℕ) k = y ⟨p.1, c p.1⟩ := by
    rw [Finset.prod_eq_single p.1]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have hmem := mul_mem_relSecM R y (coord_mem R y c p)
    (chartMonomial_mem R y c (fun k => if k = p.1 then 0 else 1))
  have hb : (Pi.single p.1 1 + fun k => if k = p.1 then 0 else 1 : K → ℕ) = fun _ => 1 := by
    funext k
    by_cases hk : k = p.1
    · subst hk; simp
    · simp [hk]
  rw [hb] at hmem
  rw [hW, h1, ← mul_assoc, div_mul_cancel₀ _ h0]
  exact hmem

end RelChartPoly

/- English proof (translation)
Introduce `K _ ι _ Ω _ R y c σ hσ`. Establish `hW : ∀ M : ℕ, (∏ k, y ⟨k, c k⟩) ^ M ∈ relSecM R y (fun _ => M)`. Introduce `M`. Rewrite using `[← Finset.prod_pow]`. Conclude with `RelChartPoly.chartMonomial_mem R y c (fun _ => M)`.

Establish `hmul : ∀ {a b : ℕ} {x x' : Ω}, x ∈ relSecM R y (fun _ => a) → x' ∈ relSecM R y (fun _ => b) → x * x' ∈ relSecM R y (fun _ => a + b)` using `fun hx hx' => mul_mem_relSecM R y hx hx'`. Proceed by induction on `hσ using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨p, rfl⟩` from `hx`. Conclude with `⟨1, by simpa using RelChartPoly.generator_mem R y c p⟩`.

Consider the case `algebraMap r`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, mul_one, Algebra.algebraMap_eq_smul_one]`. Use `Submodule.smul_mem _ r ?_` and prove the remaining obligations. Simplify using `using hW 0`.

Consider the case `add x x' _ _ hx hx'`. Take `⟨N, hN⟩` from `hx`. Take `⟨M, hM⟩` from `hx'`. Use `⟨N + M, ?_⟩` and prove the remaining obligations. Rewrite using `[add_mul]`.

Use `add_mem ?_ ?_` and prove the remaining obligations. Use `hmul hN (hW M)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `hmul hM (hW N)` as an intermediate fact.

Rewrite using `[add_comm N M]`. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul x x' _ _ hx hx'`. Take `⟨N, hN⟩` from `hx`.

Take `⟨M, hM⟩` from `hx'`. Use `⟨N + M, ?_⟩` and prove the remaining obligations. Use `hmul hN hM` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem RelChartPoly.proof : RelChartPoly.Statement := by
  intro K _ ι _ Ω _ R y c σ hσ
  have hW : ∀ M : ℕ, (∏ k, y ⟨k, c k⟩) ^ M ∈ relSecM R y (fun _ => M) := by
    intro M
    rw [← Finset.prod_pow]
    exact RelChartPoly.chartMonomial_mem R y c (fun _ => M)
  have hmul : ∀ {a b : ℕ} {x x' : Ω}, x ∈ relSecM R y (fun _ => a) → x' ∈ relSecM R y (fun _ => b) →
      x * x' ∈ relSecM R y (fun _ => a + b) := fun hx hx' => mul_mem_relSecM R y hx hx'
  induction hσ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨1, by simpa using RelChartPoly.generator_mem R y c p⟩
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [pow_zero, mul_one, Algebra.algebraMap_eq_smul_one]
    refine Submodule.smul_mem _ r ?_
    simpa using hW 0
  | add x x' _ _ hx hx' =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hx'
    refine ⟨N + M, ?_⟩
    rw [add_mul]
    refine add_mem ?_ ?_
    · have := hmul hN (hW M)
      convert this using 1
      ring
    · have := hmul hM (hW N)
      rw [add_comm N M]
      convert this using 1
      ring
  | mul x x' _ _ hx hx' =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hx'
    refine ⟨N + M, ?_⟩
    have := hmul hN hM
    convert this using 1
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
