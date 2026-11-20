import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHostNormModCoprimeLevelHalfStatement

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.NormTower

/- English proof (translation)
Establish `hI : Ideal.span {(n : 𝓞 E)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hn.ne'` after adjusting the coercions. Use `haveI : Finite (𝓞 E ⧸ Ideal.span {(n : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI`. Take `⟨c, hc⟩` from `Ultrafilter.eq_pure_of_finite (U.map fun j => Ideal.Quotient.mk (Ideal.span {(n : 𝓞 E)}) (s j))`.

Take `⟨t, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Use `⟨t, ?_⟩` and prove the remaining obligations. Establish `h : {Ideal.Quotient.mk (Ideal.span {(n : 𝓞 E)}) t} ∈ U.map fun j => Ideal.Quotient.mk (Ideal.span {(n : 𝓞 E)}) (s j)`. Rewrite using `[hc]`. Conclude with `Ultrafilter.mem_pure.2 rfl`.

Rewrite `h` using `[Ultrafilter.mem_map]`. Use `filter_upwards [h] with j hj`. Conclude with `Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hj)`.
-/
theorem exists_eventually_dvd_sub {E : Type} [Field E] [NumberField E] (U : Ultrafilter ℕ) (s : ℕ → 𝓞 E)
    (n : ℕ) (hn : 0 < n) : ∃ t : 𝓞 E, ∀ᶠ j in (U : Filter ℕ), (n : 𝓞 E) ∣ s j - t := by
  have hI : Ideal.span {(n : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn.ne'
  haveI : Finite (𝓞 E ⧸ Ideal.span {(n : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  obtain ⟨c, hc⟩ := Ultrafilter.eq_pure_of_finite
    (U.map fun j => Ideal.Quotient.mk (Ideal.span {(n : 𝓞 E)}) (s j))
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨t, ?_⟩
  have h : {Ideal.Quotient.mk (Ideal.span {(n : 𝓞 E)}) t} ∈
      U.map fun j => Ideal.Quotient.mk (Ideal.span {(n : 𝓞 E)}) (s j) := by
    rw [hc]; exact Ultrafilter.mem_pure.2 rfl
  rw [Ultrafilter.mem_map] at h
  filter_upwards [h] with j hj
  exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hj)

/- English proof (translation)
Introduce `E _ _ _ H l ν hcop hcomp`. Establish `hM : 0 < l.M` using `lt_of_lt_of_le (by norm_num) l.three_le`. Establish `hs : ∀ j : ℕ, ∃ t : 𝓞 E, ((j.factorial : ℕ) : 𝓞 E) ∣ t * H.bar t - (ν j.factorial : 𝓞 E) ∧ (l.M ∣ j.factorial → t - 1 ∈ l.Mb)` using `fun j => GlobalTheory.T.exists_hostNorm_mod_coprime_level_half E H l j.factorial (ν j.factorial) j.factorial_pos (hcop _ j.factorial_pos)`. Use `choose s hs1 hs2 using hs`. Set `U : Ultrafilter ℕ` to `Filter.hyperfilter ℕ`.

Establish `hU : ∀ n : ℕ, 0 < n → ∀ᶠ j in (U : Filter ℕ), n ∣ j.factorial`. Introduce `n hn`. Establish `h : ∀ᶠ j : ℕ in Filter.cofinite, n ∣ j.factorial`. Rewrite using `[Nat.cofinite_eq_atTop]`. Use `filter_upwards [Filter.eventually_ge_atTop n] with j hj`.

Conclude with `Nat.dvd_factorial hn hj`. Conclude with `h.filter_mono Filter.hyperfilter_le_cofinite`. Establish `ht : ∀ n : ℕ, ∃ t : 𝓞 E, 0 < n → ∀ᶠ j in (U : Filter ℕ), (n : 𝓞 E) ∣ s j - t`. Introduce `n`. Distinguish the cases in `hn : 0 < n`.

Take `⟨t, h⟩` from `exists_eventually_dvd_sub U s n hn`. Conclude with `⟨t, fun _ => h⟩`. Conclude with `⟨0, fun h => absurd h hn⟩`. Use `choose t ht using ht`. Use `⟨t, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `n hn`. Take `⟨j, ⟨a, ha⟩, m, hm⟩` from `((ht n hn).and (hU n hn)).exists`. Establish `hm0 : 0 < m`. Break down `Nat.eq_zero_or_pos m with h | h` into its components or cases. Conclude with `absurd (by rw [hm, h, mul_zero]) j.factorial_ne_zero`.

Conclude with `h`. Take `⟨b, hb⟩` from `hs1 j`. Take `⟨c, hc⟩` from `hcomp n m hn hm0`. Rewrite `hb` using `[hm]`. Establish `hc' : ((ν (n * m) : ℤ) : 𝓞 E) - (ν n : 𝓞 E) = (n : 𝓞 E) * (c : 𝓞 E)` using `by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hc`.

Establish `hsj : s j = t n + n * a` using `by rw [← ha]; ring`. Rewrite `hb` using `[hsj, map_add, map_mul, map_natCast]`. Move the coercions through the operations in `at hb`. Conclude with `⟨m * b + c - (a * H.bar (t n) + t n * H.bar a + n * a * H.bar a), by linear_combination hb + hc'⟩`. Introduce `n m hn hm`.

Take `⟨j, h1, h2⟩` from `((ht n hn).and (ht (n * m) (Nat.mul_pos hn hm))).exists`. Establish `h3 : (n : 𝓞 E) ∣ s j - t (n * m)` using `dvd_trans ⟨(m : 𝓞 E), by push_cast; rfl⟩ h2`. Use `dvd_sub h1 h3` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Take `⟨j, ⟨a, ha⟩, h2⟩` from `((ht l.M hM).and (hU l.M hM)).exists`. Establish `hMb : (l.M : 𝓞 E) ∈ l.Mb`. Establish `: (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)}` using `Ideal.mem_span_singleton_self _`. Rewrite `this` using `[← l.prod]`. Conclude with `Ideal.mul_le_left this`.

Establish `h3 : (l.M : 𝓞 E) * a ∈ l.Mb` using `Ideal.mul_mem_right a _ hMb`. Establish `h4 : t l.M - 1 = (s j - 1) - (l.M : 𝓞 E) * a` using `by rw [← ha]; ring`. Rewrite using `[h4]`. Conclude with `Ideal.sub_mem _ (hs2 j h2) h3`.
-/
theorem exists_norm_tower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (ν : ℕ → ℤ), (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) → (∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) → ∃ t : ℕ → 𝓞 E, (∀ n : ℕ, 0 < n → (n : 𝓞 E) ∣ t n * H.bar (t n) - (ν n : 𝓞 E)) ∧ (∀ n m : ℕ, 0 < n → 0 < m → (n : 𝓞 E) ∣ t (n * m) - t n) ∧ t l.M - 1 ∈ l.Mb := by
  intro E _ _ _ H l ν hcop hcomp
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hs : ∀ j : ℕ, ∃ t : 𝓞 E, ((j.factorial : ℕ) : 𝓞 E) ∣ t * H.bar t - (ν j.factorial : 𝓞 E) ∧
      (l.M ∣ j.factorial → t - 1 ∈ l.Mb) := fun j =>
    GlobalTheory.T.exists_hostNorm_mod_coprime_level_half E H l j.factorial (ν j.factorial) j.factorial_pos (hcop _ j.factorial_pos)
  choose s hs1 hs2 using hs
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have hU : ∀ n : ℕ, 0 < n → ∀ᶠ j in (U : Filter ℕ), n ∣ j.factorial := by
    intro n hn
    have h : ∀ᶠ j : ℕ in Filter.cofinite, n ∣ j.factorial := by
      rw [Nat.cofinite_eq_atTop]
      filter_upwards [Filter.eventually_ge_atTop n] with j hj
      exact Nat.dvd_factorial hn hj
    exact h.filter_mono Filter.hyperfilter_le_cofinite
  have ht : ∀ n : ℕ, ∃ t : 𝓞 E, 0 < n → ∀ᶠ j in (U : Filter ℕ), (n : 𝓞 E) ∣ s j - t := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨t, h⟩ := exists_eventually_dvd_sub U s n hn
      exact ⟨t, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose t ht using ht
  refine ⟨t, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨j, ⟨a, ha⟩, m, hm⟩ := ((ht n hn).and (hU n hn)).exists
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (by rw [hm, h, mul_zero]) j.factorial_ne_zero
      · exact h
    obtain ⟨b, hb⟩ := hs1 j
    obtain ⟨c, hc⟩ := hcomp n m hn hm0
    rw [hm] at hb
    have hc' : ((ν (n * m) : ℤ) : 𝓞 E) - (ν n : 𝓞 E) = (n : 𝓞 E) * (c : 𝓞 E) := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hc
    have hsj : s j = t n + n * a := by rw [← ha]; ring
    rw [hsj, map_add, map_mul, map_natCast] at hb
    push_cast at hb
    exact ⟨m * b + c - (a * H.bar (t n) + t n * H.bar a + n * a * H.bar a), by linear_combination hb + hc'⟩
  · intro n m hn hm
    obtain ⟨j, h1, h2⟩ := ((ht n hn).and (ht (n * m) (Nat.mul_pos hn hm))).exists
    have h3 : (n : 𝓞 E) ∣ s j - t (n * m) := dvd_trans ⟨(m : 𝓞 E), by push_cast; rfl⟩ h2
    have := dvd_sub h1 h3
    convert this using 1
    ring
  · obtain ⟨j, ⟨a, ha⟩, h2⟩ := ((ht l.M hM).and (hU l.M hM)).exists
    have hMb : (l.M : 𝓞 E) ∈ l.Mb := by
      have : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.mem_span_singleton_self _
      rw [← l.prod] at this
      exact Ideal.mul_le_left this
    have h3 : (l.M : 𝓞 E) * a ∈ l.Mb := Ideal.mul_mem_right a _ hMb
    have h4 : t l.M - 1 = (s j - 1) - (l.M : 𝓞 E) * a := by rw [← ha]; ring
    rw [h4]
    exact Ideal.sub_mem _ (hs2 j h2) h3

end GlobalTheory.NormTower
