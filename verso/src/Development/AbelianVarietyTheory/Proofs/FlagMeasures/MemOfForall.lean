import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocalizedModuleSubtype
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open scoped nonZeroDivisors

namespace GlobalTheory.DegCnt.IdealPow

variable {K : Type} [Field K] [NumberField K] {𝔡 : Ideal (𝓞 K)}

/- English proof (translation)
Simplify using `[ipow]`.
-/
theorem ipow_zero (𝔡 : Ideal (𝓞 K)) : ipow 𝔡 0 = 1 := by
  simp [ipow]

/- English proof (translation)
Establish `h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 h`. Unfold `ipow`. Rewrite using `[zpow_add₀ h0, FractionalIdeal.coe_mul]`.
-/
theorem ipow_mul (h : 𝔡 ≠ ⊥) (m n : ℤ) : ipow 𝔡 m * ipow 𝔡 n = ipow 𝔡 (m + n) := by
  have h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h
  unfold ipow
  rw [zpow_add₀ h0, FractionalIdeal.coe_mul]

/- English proof (translation)
Rewrite using `[← hk, ← ipow_mul h]`. Conclude with `Submodule.mul_mem_mul hx hy`.
-/
theorem mul_mem (h : 𝔡 ≠ ⊥) {m n k : ℤ} (hk : m + n = k) {x y : K} (hx : x ∈ ipow 𝔡 m) (hy : y ∈ ipow 𝔡 n) :
    x * y ∈ ipow 𝔡 k := by
  rw [← hk, ← ipow_mul h]
  exact Submodule.mul_mem_mul hx hy

/- English proof (translation)
Rewrite using `[← ipow_zero 𝔡]`. Conclude with `mul_mem h hk hx hy`.
-/
theorem mul_mem_one (h : 𝔡 ≠ ⊥) {m n : ℤ} (hk : m + n = 0) {x y : K} (hx : x ∈ ipow 𝔡 m) (hy : y ∈ ipow 𝔡 n) :
    x * y ∈ (1 : Submodule (𝓞 K) K) := by
  rw [← ipow_zero 𝔡]
  exact mul_mem h hk hx hy

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero => simp only [pow_zero, Nat.cast_zero, zero_mul, ipow_zero]`. Conclude with `Submodule.mem_one.2 ⟨1, map_one _⟩`. Consider the case `succ s ih => rw [pow_succ]; exact mul_mem h (by push_cast; ring) ih hx`.
-/
theorem pow_mem (h : 𝔡 ≠ ⊥) {m : ℤ} {x : K} (hx : x ∈ ipow 𝔡 m) (s : ℕ) : x ^ s ∈ ipow 𝔡 (s * m) := by
  induction s with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul, ipow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  | succ s ih => rw [pow_succ]; exact mul_mem h (by push_cast; ring) ih hx

/- English proof (translation)
Establish `h1 : (1 : K) ∈ ipow 𝔡 n * ipow 𝔡 m`. Rewrite using `[ipow_mul h, add_comm, hk, ipow_zero]`. Conclude with `Submodule.mem_one.2 ⟨1, map_one _⟩`. Establish `h2 : ∀ z ∈ ipow 𝔡 n * ipow 𝔡 m, x * z ∈ ipow 𝔡 m`. Introduce `z hz`.

Use `Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Take `⟨c, hc⟩` from `Submodule.mem_one.1 (hx a ha)`. Rewrite using `[← mul_assoc, ← hc, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ c hb`. Rewrite using `[mul_add]`.

Conclude with `add_mem ha hb`. Simplify using `using h2 1 h1`.
-/
theorem mem_of_forall (h : 𝔡 ≠ ⊥) {m n : ℤ} (hk : m + n = 0) {x : K}
    (hx : ∀ y ∈ ipow 𝔡 n, x * y ∈ (1 : Submodule (𝓞 K) K)) : x ∈ ipow 𝔡 m := by
  have h1 : (1 : K) ∈ ipow 𝔡 n * ipow 𝔡 m := by
    rw [ipow_mul h, add_comm, hk, ipow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  have h2 : ∀ z ∈ ipow 𝔡 n * ipow 𝔡 m, x * z ∈ ipow 𝔡 m := by
    intro z hz
    refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hx a ha)
      rw [← mul_assoc, ← hc, ← Algebra.smul_def]
      exact Submodule.smul_mem _ c hb
    · rw [mul_add]; exact add_mem ha hb
  simpa using h2 1 h1

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [ipow_zero]`. Consider the case `insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ipow_mul h]`.
-/
theorem prod_ipow (h : 𝔡 ≠ ⊥) {ι : Type} (s : Finset ι) (n : ι → ℤ) :
    ∏ i ∈ s, ipow 𝔡 (n i) = ipow 𝔡 (∑ i ∈ s, n i) := by
  induction s using Finset.induction_on with
  | empty => simp [ipow_zero]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ipow_mul h]

/- English proof (translation)
Rewrite using `[← prod_ipow h]`. Establish `: ∏ i, ipow 𝔡 (n i) = ∏ i, Submodule.span (𝓞 K) (ipow 𝔡 (n i) : Set K)` using `by simp`. Rewrite using `[this, Submodule.prod_span, Submodule.span_le]`. Introduce `x hx`. Take `⟨α, hα, rfl⟩` from `(Set.mem_fintype_prod _ _).1 hx`.

Conclude with `hJ α hα`.
-/
theorem ipow_sum_le (h : 𝔡 ≠ ⊥) {ι : Type} [Fintype ι] (n : ι → ℤ) (J : Submodule (𝓞 K) K)
    (hJ : ∀ α : ι → K, (∀ i, α i ∈ ipow 𝔡 (n i)) → ∏ i, α i ∈ J) : ipow 𝔡 (∑ i, n i) ≤ J := by
  rw [← prod_ipow h]
  have : ∏ i, ipow 𝔡 (n i) = ∏ i, Submodule.span (𝓞 K) (ipow 𝔡 (n i) : Set K) := by simp
  rw [this, Submodule.prod_span, Submodule.span_le]
  intro x hx
  obtain ⟨α, hα, rfl⟩ := (Set.mem_fintype_prod _ _).1 hx
  exact hJ α hα

variable [StarRing K]

/- English proof (translation)
Proceed by induction on `n generalizing x with`. Consider the case `zero`. Rewrite `hx`, the goal using `[Nat.cast_zero, ipow_zero]`. Conclude with `GlobalTheory.UnimodQuot.star_mem_one hx`. Consider the case `succ n ih`.

Rewrite `hx`, the goal using `[Nat.cast_succ, ← ipow_mul h]`. Use `Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Rewrite using `[star_mul']`. Use `Submodule.mul_mem_mul (ih ha) ?_` and prove the remaining obligations. Simplify using `only [ipow, zpow_one, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal] at hb ⊢`.

Take `⟨y, hy, rfl⟩` from `hb`. Conclude with `hs y hy`. Rewrite using `[star_add]`. Conclude with `add_mem ha hb`.
-/
theorem star_mem_nat (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℕ) {x : K}
    (hx : x ∈ ipow 𝔡 n) : star x ∈ ipow 𝔡 n := by
  induction n generalizing x with
  | zero =>
    rw [Nat.cast_zero, ipow_zero] at hx ⊢
    exact GlobalTheory.UnimodQuot.star_mem_one hx
  | succ n ih =>
    rw [Nat.cast_succ, ← ipow_mul h] at hx ⊢
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [star_mul']
      refine Submodule.mul_mem_mul (ih ha) ?_
      simp only [ipow, zpow_one, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal] at hb ⊢
      obtain ⟨y, hy, rfl⟩ := hb
      exact hs y hy
    · rw [star_add]; exact add_mem ha hb

/- English proof (translation)
Take `⟨m, rfl | rfl⟩` from `Int.eq_nat_or_neg n`. Conclude with `star_mem_nat h hs m hx`. Use `mem_of_forall h (neg_add_cancel _) fun y hy => ?_` and prove the remaining obligations. Use `GlobalTheory.UnimodQuot.star_mem_one (mul_mem_one h (neg_add_cancel _) hx (star_mem_nat h hs m hy))` as an intermediate fact. Rewrite `this` using `[star_mul', star_star]`. Then use the resulting hypothesis.
-/
theorem star_mem (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) {n : ℤ} {x : K}
    (hx : x ∈ ipow 𝔡 n) : star x ∈ ipow 𝔡 n := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact star_mem_nat h hs m hx
  · refine mem_of_forall h (neg_add_cancel _) fun y hy => ?_
    have := GlobalTheory.UnimodQuot.star_mem_one (mul_mem_one h (neg_add_cancel _) hx (star_mem_nat h hs m hy))
    rwa [star_mul', star_star] at this

end GlobalTheory.DegCnt.IdealPow
