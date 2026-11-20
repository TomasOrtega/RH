import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartDenominator
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

/- English proof (translation)
Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact ⟨1, le_rfl, by simpa using Algebra.subset_adjoin hx⟩`. Consider the case `algebraMap r`. Use `⟨r.den, r.den_pos, ?_⟩` and prove the remaining obligations. Establish `h : ((r.den : ℕ) : Ω) * algebraMap ℚ Ω r = ((r.num : ℤ) : Ω)`.

Establish `hd : ((r.den : ℕ) : Ω) ≠ 0` using `by exact_mod_cast r.den_pos.ne'`. Rewrite using `[eq_ratCast (algebraMap ℚ Ω) r, Rat.cast_def, mul_div_cancel₀ _ hd]`. Rewrite using `[h]`. Conclude with `intCast_mem _ _`. Consider the case `add x y _ _ hx hy`.

Take `⟨n, hn, hnx⟩` from `hx`. Take `⟨m, hm, hmy⟩` from `hy`. Use `⟨n * m, Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩` and prove the remaining obligations. Establish `h : ((n * m : ℕ) : Ω) * (x + y) = (m : ℤ) • ((n : Ω) * x) + (n : ℤ) • ((m : Ω) * y)`. Simplify using `only [Nat.cast_mul, zsmul_eq_mul, Int.cast_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Conclude with `add_mem (zsmul_mem hnx _) (zsmul_mem hmy _)`. Consider the case `mul x y _ _ hx hy`. Take `⟨n, hn, hnx⟩` from `hx`.

Take `⟨m, hm, hmy⟩` from `hy`. Use `⟨n * m, Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩` and prove the remaining obligations. Establish `h : ((n * m : ℕ) : Ω) * (x * y) = ((n : Ω) * x) * ((m : Ω) * y)` using `by push_cast; ring`. Rewrite using `[h]`. Conclude with `mul_mem hnx hmy`.
-/
theorem exists_nat_mul_mem_adjoin_int {Ω : Type} [Field Ω] [CharZero Ω] (S : Set Ω) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℚ S) : ∃ n : ℕ, 1 ≤ n ∧ (n : Ω) * x ∈ Algebra.adjoin ℤ S := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, le_rfl, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    refine ⟨r.den, r.den_pos, ?_⟩
    have h : ((r.den : ℕ) : Ω) * algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) := by
      have hd : ((r.den : ℕ) : Ω) ≠ 0 := by exact_mod_cast r.den_pos.ne'
      rw [eq_ratCast (algebraMap ℚ Ω) r, Rat.cast_def, mul_div_cancel₀ _ hd]
    rw [h]
    exact intCast_mem _ _
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩
    have h : ((n * m : ℕ) : Ω) * (x + y) = (m : ℤ) • ((n : Ω) * x) + (n : ℤ) • ((m : Ω) * y) := by
      simp only [Nat.cast_mul, zsmul_eq_mul, Int.cast_natCast]; ring
    rw [h]
    exact add_mem (zsmul_mem hnx _) (zsmul_mem hmy _)
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩
    have h : ((n * m : ℕ) : Ω) * (x * y) = ((n : Ω) * x) * ((m : Ω) * y) := by
      push_cast; ring
    rw [h]
    exact mul_mem hnx hmy

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y b τ s hs`. Establish `key : ∀ c : ∀ k, ι k, ∃ n : ℕ, 1 ≤ n ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) → (n : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * b k))) ∈ chartRingZ y c)`. Introduce `c`. Distinguish the cases in `hc : ∀ k, y ⟨k, c k⟩ ≠ 0`. Take `⟨n, hn, h⟩` from `exists_nat_mul_mem_adjoin_int _ (hs c hc)`.

Conclude with `⟨n, hn, fun _ => h⟩`. Conclude with `⟨1, le_rfl, fun h => absurd h hc⟩`. Use `choose N hN1 hN using key`. Use `⟨∏ c, N c, Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun c _ => by` and prove the remaining obligations. Use `hN1 c` as an intermediate fact.

Use the proof step `omega), ?_⟩`. Introduce `c hc`. Take `⟨m, hm⟩` from `Finset.dvd_prod_of_mem N (Finset.mem_univ c)`. Establish `h : ((∏ c, N c : ℕ) : Ω) * s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * b k)) = (m : ℤ) • ((N c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * b k))))`. Rewrite using `[hm]`.

Simplify using `only [Nat.cast_mul, zsmul_eq_mul, Int.cast_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Conclude with `zsmul_mem (hN c hc) _`.
-/
theorem ChartDenominator.proof : ChartDenominator.Statement := by
  intro K _ ι _ Ω _ _ y b τ s hs
  classical
  have key : ∀ c : ∀ k, ι k, ∃ n : ℕ, 1 ≤ n ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) →
      (n : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * b k))) ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_adjoin_int _ (hs c hc)
      exact ⟨n, hn, fun _ => h⟩
    · exact ⟨1, le_rfl, fun h => absurd h hc⟩
  choose N hN1 hN using key
  refine ⟨∏ c, N c, Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun c _ => by
    have := hN1 c; omega), ?_⟩
  intro c hc
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ c)
  have h : ((∏ c, N c : ℕ) : Ω) * s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * b k)) =
      (m : ℤ) • ((N c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * b k)))) := by
    rw [hm]; simp only [Nat.cast_mul, zsmul_eq_mul, Int.cast_natCast]; ring
  rw [h]
  exact zsmul_mem (hN c hc) _

end GroundTheory.Heights₂.Heights.HilbertSamuel
