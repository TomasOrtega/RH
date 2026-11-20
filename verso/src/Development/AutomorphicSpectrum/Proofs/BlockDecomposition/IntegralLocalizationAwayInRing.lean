import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.ValIntClosed

/- English proof (translation)
Introduce `S _ ϖ hϖ hV x hx`. Take `⟨P, hm, hP⟩` from `hx`. Take `⟨N, f, hf⟩` from `IsLocalization.Away.surj ϖ x`. Use `set a := algebraMap S (Localization.Away ϖ) with ha`. Establish `hinj : Function.Injective a` using `IsLocalization.injective (Localization.Away ϖ) (Submonoid.powers_le.2 hϖ)`.

Establish `hwnz : ϖ ^ N ∈ nonZeroDivisors S` using `pow_mem hϖ N`. Establish `hwu : IsUnit (a (ϖ ^ N))`. Rewrite using `[map_pow]`. Conclude with `(IsLocalization.Away.algebraMap_isUnit ϖ).pow N`. Take `⟨e, he, ⟨b, hb⟩, ⟨h, hh⟩⟩` from `(by`.

Take `⟨e, he, h1, h2⟩` from `hV f (ϖ ^ N) ⟨N, Ideal.subset_span (by simp)⟩`. Conclude with `⟨e, he, Ideal.mem_span_singleton.1 h1, Ideal.mem_span_singleton.1 h2⟩ : ∃ e : S, IsIdempotentElem e ∧ ϖ ^ N ∣ e * f ∧ f ∣ (1 - e) * ϖ ^ N)`. Use `set u := 1 - e with hu`. Establish `hui : IsIdempotentElem u` using `he.one_sub`. Use `set d := P.natDegree with hd`.

Establish `hhx : a h * x = a u`. Apply `hwu.mul_left_cancel` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hUi : a u * a u = a u` using `by rw [← map_mul, hui.eq]`. Establish `hUp : ∀ i : ℕ, a u * a u ^ i = a u`.

Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, ← mul_assoc, ih, hUi]`. Use `set k : S := ∑ i ∈ Finset.range d, P.coeff i * h ^ (d - 1 - i) with hk`.

Establish `hrel : a (u * (1 + h * k)) = 0`. Establish `h0 : a u * a h ^ d * Polynomial.eval₂ a x P = 0`. Establish `: Polynomial.eval₂ a x P = 0` using `hP`. Rewrite using `[this, mul_zero]`. Rewrite `h0` using `[Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, mul_add, Finset.mul_sum]`.

Establish `hlead : P.coeff d = 1` using `hm`. Establish `t1 : a u * a h ^ d * (a (P.coeff d) * x ^ d) = a u`. Rewrite using `[hlead, map_one, one_mul, mul_assoc, ← mul_pow, hhx, hUp]`. Establish `t2 : ∀ i ∈ Finset.range d, a u * a h ^ d * (a (P.coeff i) * x ^ i) = a u * (a h * a (P.coeff i * h ^ (d - 1 - i)))`. Introduce `i hi`.

Establish `hi' : i < d` using `Finset.mem_range.1 hi`. Establish `hd' : d = i + (1 + (d - 1 - i))` using `by omega`. Establish `: a h ^ d = a h ^ i * (a h * a h ^ (d - 1 - i))` using `by conv_lhs => rw [hd', pow_add, pow_add, pow_one]`. Rewrite using `[this]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = a u * (a h * a (P.coeff i * h ^ (d - 1 - i))) := by`. Rewrite using `[hhx, hUp, map_mul, map_pow]`. Rewrite `h0` using `[t1, Finset.sum_congr rfl t2, ← Finset.mul_sum, ← Finset.mul_sum]`.

Rewrite using `[map_mul, map_add, map_one, map_mul, hk, map_sum]`. Rewrite using `[mul_add, mul_one, add_comm]`. Conclude with `h0`. Establish `hrel' : u * (1 + h * k) = 0` using `hinj (by rw [hrel, map_zero])`. Establish `hu' : u = - (u * h * k)` using `by linear_combination hrel'`.

Establish `hdiv : ϖ ^ N ∣ f`. Establish `hfe : f = e * f + u * f` using `by rw [hu]; ring`. Establish `huf : u * f = ϖ ^ N * (-(k * u))`. Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨b + -(k * u), by rw [hfe, hb, huf]; ring⟩`.

Take `⟨y, hy⟩` from `hdiv`. Use `⟨y, ?_⟩` and prove the remaining obligations. Apply `hwu.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[← map_mul, ← hy, ← hf, map_pow, mul_comm]`.
-/
theorem exists_eq_of_isIntegral : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ →
    ∀ x : Localization.Away ϖ, IsIntegral S x → ∃ y : S, algebraMap S (Localization.Away ϖ) y = x := by
  intro S _ ϖ hϖ hV x hx
  obtain ⟨P, hm, hP⟩ := hx
  obtain ⟨N, f, hf⟩ := IsLocalization.Away.surj ϖ x
  set a := algebraMap S (Localization.Away ϖ) with ha
  have hinj : Function.Injective a :=
    IsLocalization.injective (Localization.Away ϖ) (Submonoid.powers_le.2 hϖ)
  have hwnz : ϖ ^ N ∈ nonZeroDivisors S := pow_mem hϖ N
  have hwu : IsUnit (a (ϖ ^ N)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit ϖ).pow N
  obtain ⟨e, he, ⟨b, hb⟩, ⟨h, hh⟩⟩ := (by
    obtain ⟨e, he, h1, h2⟩ := hV f (ϖ ^ N) ⟨N, Ideal.subset_span (by simp)⟩
    exact ⟨e, he, Ideal.mem_span_singleton.1 h1, Ideal.mem_span_singleton.1 h2⟩ :
      ∃ e : S, IsIdempotentElem e ∧ ϖ ^ N ∣ e * f ∧ f ∣ (1 - e) * ϖ ^ N)
  set u := 1 - e with hu
  have hui : IsIdempotentElem u := he.one_sub
  set d := P.natDegree with hd

  have hhx : a h * x = a u := by
    apply hwu.mul_left_cancel
    calc a (ϖ ^ N) * (a h * x) = a h * (x * a (ϖ ^ N)) := by ring
      _ = a h * a f := by rw [map_pow, hf]
      _ = a u * a (ϖ ^ N) := by rw [← map_mul, ← map_mul, hh]; ring_nf
      _ = a (ϖ ^ N) * a u := by ring
  have hUi : a u * a u = a u := by rw [← map_mul, hui.eq]
  have hUp : ∀ i : ℕ, a u * a u ^ i = a u := by
    intro i
    induction i with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, hUi]
  set k : S := ∑ i ∈ Finset.range d, P.coeff i * h ^ (d - 1 - i) with hk
  have hrel : a (u * (1 + h * k)) = 0 := by
    have h0 : a u * a h ^ d * Polynomial.eval₂ a x P = 0 := by
      have : Polynomial.eval₂ a x P = 0 := hP
      rw [this, mul_zero]
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, mul_add, Finset.mul_sum] at h0
    have hlead : P.coeff d = 1 := hm
    have t1 : a u * a h ^ d * (a (P.coeff d) * x ^ d) = a u := by
      rw [hlead, map_one, one_mul, mul_assoc, ← mul_pow, hhx, hUp]
    have t2 : ∀ i ∈ Finset.range d, a u * a h ^ d * (a (P.coeff i) * x ^ i)
        = a u * (a h * a (P.coeff i * h ^ (d - 1 - i))) := by
      intro i hi
      have hi' : i < d := Finset.mem_range.1 hi
      have hd' : d = i + (1 + (d - 1 - i)) := by omega
      have : a h ^ d = a h ^ i * (a h * a h ^ (d - 1 - i)) := by
        conv_lhs => rw [hd', pow_add, pow_add, pow_one]
      rw [this]
      calc a u * (a h ^ i * (a h * a h ^ (d - 1 - i))) * (a (P.coeff i) * x ^ i)
          = (a u * (a h * x) ^ i) * (a h * (a (P.coeff i) * a h ^ (d - 1 - i))) := by
            rw [mul_pow]; ring
        _ = a u * (a h * a (P.coeff i * h ^ (d - 1 - i))) := by
            rw [hhx, hUp, map_mul, map_pow]
    rw [t1, Finset.sum_congr rfl t2, ← Finset.mul_sum, ← Finset.mul_sum] at h0
    rw [map_mul, map_add, map_one, map_mul, hk, map_sum]
    rw [mul_add, mul_one, add_comm]
    exact h0
  have hrel' : u * (1 + h * k) = 0 := hinj (by rw [hrel, map_zero])
  have hu' : u = - (u * h * k) := by linear_combination hrel'
  have hdiv : ϖ ^ N ∣ f := by
    have hfe : f = e * f + u * f := by rw [hu]; ring
    have huf : u * f = ϖ ^ N * (-(k * u)) := by
      calc u * f = - (u * h * k) * f := by rw [← hu']
        _ = - (k * u * (f * h)) := by ring
        _ = - (k * u * (u * ϖ ^ N)) := by rw [hh]
        _ = - (k * (u * u) * ϖ ^ N) := by ring
        _ = ϖ ^ N * (-(k * u)) := by rw [hui.eq]; ring
    exact ⟨b + -(k * u), by rw [hfe, hb, huf]; ring⟩
  obtain ⟨y, hy⟩ := hdiv
  refine ⟨y, ?_⟩
  apply hwu.mul_left_cancel
  rw [← map_mul, ← hy, ← hf, map_pow, mul_comm]

end GlobalTheory.CompanionTheory.ValIntClosed
