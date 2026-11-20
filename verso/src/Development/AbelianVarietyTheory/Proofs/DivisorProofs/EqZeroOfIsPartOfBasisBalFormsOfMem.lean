import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM

namespace GlobalTheory.PolFan

/- English proof (translation)
Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q`. Establish `hb' : ∀ i, ∃ r : ℤ, (r : ℚ) = ((b : ℤ) : ℚ) * q i` using `fun i => by`. Take `⟨r, hr⟩` from `hb i`. Conclude with `⟨r, by simpa [Algebra.smul_def] using hr⟩`. Use `choose n hn using hb'`.

Establish `h0 : n = 0`. Rewrite `hf` using `[Fintype.linearIndependent_iff]`. Use function extensionality and compare the values at `i`. Use `hf n ?_ i` and prove the remaining obligations. Use function extensionality and compare the values at `y`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]`. Establish `: ((∑ i, n i * f i y : ℤ) : ℚ) = ((b : ℤ) : ℚ) * ∑ i, q i * (f i y : ℚ)`. Use `push_cast`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hn i]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `this` using `[hq y, mul_zero]`. Conclude with `this` after adjusting the coercions. Use function extensionality and compare the values at `i`.

Establish `hbne : ((b : ℤ) : ℚ) ≠ 0` using `by exact_mod_cast nonZeroDivisors.coe_ne_zero b`. Establish `h` using `hn i`. Rewrite `h` using `[h0]`. Simplify using `only [Pi.zero_apply, Int.cast_zero] at h`. Conclude with `(mul_eq_zero.mp h.symm).resolve_left hbne`.
-/
theorem eq_zero_of_linearIndependent_int_rat {Y ι : Type} [Fintype ι] {f : ι → Y → ℤ}
    (hf : LinearIndependent ℤ f) (q : ι → ℚ) (hq : ∀ y, ∑ i, q i * (f i y : ℚ) = 0) : q = 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
  have hb' : ∀ i, ∃ r : ℤ, (r : ℚ) = ((b : ℤ) : ℚ) * q i := fun i => by
    obtain ⟨r, hr⟩ := hb i
    exact ⟨r, by simpa [Algebra.smul_def] using hr⟩
  choose n hn using hb'
  have h0 : n = 0 := by
    rw [Fintype.linearIndependent_iff] at hf
    funext i
    refine hf n ?_ i
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have : ((∑ i, n i * f i y : ℤ) : ℚ) = ((b : ℤ) : ℚ) * ∑ i, q i * (f i y : ℚ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hn i]; ring
    rw [hq y, mul_zero] at this
    exact_mod_cast this
  funext i
  have hbne : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero b
  have h := hn i
  rw [h0] at h
  simp only [Pi.zero_apply, Int.cast_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hbne

/- English proof (translation)
Set `B` to `Module.Basis.ofVectorSpace ℚ k`. Establish `key : ∀ j, (fun i => B.coord j (a i)) = 0` using `fun j => eq_zero_of_linearIndependent_int_rat hf _ fun y => by`. Establish `h` using `congrArg (B.coord j) (ha y)`. Rewrite `h` using `[map_sum, map_zero]`. Rewrite using `[← h]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm (a i), ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]`. Use function extensionality and compare the values at `i`. Apply `B.repr.injective` to reduce the goal to its premises. Use extensionality with `j`.

Use `congrFun (key j) i` as an intermediate fact. Simplify `this` using `[Module.Basis.coord_apply]`.
-/
theorem eq_zero_of_linearIndependent_int {Y ι : Type} [Fintype ι] {f : ι → Y → ℤ}
    (hf : LinearIndependent ℤ f) (k : Type) [Field k] [CharZero k] (a : ι → k)
    (ha : ∀ y, ∑ i, a i * (f i y : k) = 0) : a = 0 := by
  classical
  let B := Module.Basis.ofVectorSpace ℚ k
  have key : ∀ j, (fun i => B.coord j (a i)) = 0 := fun j =>
    eq_zero_of_linearIndependent_int_rat hf _ fun y => by
      have h := congrArg (B.coord j) (ha y)
      rw [map_sum, map_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm (a i), ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  funext i
  apply B.repr.injective
  ext j
  have := congrFun (key j) i
  simpa [Module.Basis.coord_apply] using this

end GlobalTheory.PolFan

namespace GlobalTheory.PolFan

end GlobalTheory.PolFan
