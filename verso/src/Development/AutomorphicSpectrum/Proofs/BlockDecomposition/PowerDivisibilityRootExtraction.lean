import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.ValPowDvd

/- English proof (translation)
Introduce `S _ ϖ hϖ hV z m d hd hdiv`. Take `⟨d', rfl⟩ : ∃ d', d = d' + 1` from `⟨d - 1, by omega⟩`. Take `⟨w, hw⟩` from `hdiv`. Take `⟨e, he, h1, h2⟩` from `hV (ϖ ^ m) z ⟨m, Ideal.subset_span (Set.mem_insert _ _)⟩`. Take `⟨c', hc'⟩` from `Ideal.mem_span_singleton'.mp h1`.

Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp h2`. Establish `h3 : (e * ϖ ^ m) ^ (d' + 1) = (c' * z) ^ (d' + 1)` using `by rw [hc']`. Rewrite `h3` using `[mul_pow, mul_pow, hw, he.pow_succ_eq d', ← pow_mul]`. Establish `key : (e - w * c' ^ (d' + 1)) * ϖ ^ (m * (d' + 1)) = 0` using `by linear_combination h3`. Establish `he' : e = w * c' ^ (d' + 1)` using `sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp (pow_mem hϖ (m * (d' + 1)))).2 _ key)`.

Establish `hee : e * e = e` using `he.eq`. Conclude with `⟨e * w * c' ^ d' + c, by`. Take the linear combination `(-1 : S) * hc + (-z) * hee + (z * e) * he' + (e * w * c' ^ d') * hc' + (w * c' ^ d' * ϖ ^ m) * hee⟩`.
-/
theorem dvd_of_pow_mul_dvd_pow : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ →
    ∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z := by
  intro S _ ϖ hϖ hV z m d hd hdiv
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  obtain ⟨w, hw⟩ := hdiv
  obtain ⟨e, he, h1, h2⟩ := hV (ϖ ^ m) z ⟨m, Ideal.subset_span (Set.mem_insert _ _)⟩
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h2
  have h3 : (e * ϖ ^ m) ^ (d' + 1) = (c' * z) ^ (d' + 1) := by rw [hc']
  rw [mul_pow, mul_pow, hw, he.pow_succ_eq d', ← pow_mul] at h3
  have key : (e - w * c' ^ (d' + 1)) * ϖ ^ (m * (d' + 1)) = 0 := by linear_combination h3
  have he' : e = w * c' ^ (d' + 1) :=
    sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp (pow_mem hϖ (m * (d' + 1)))).2 _ key)
  have hee : e * e = e := he.eq
  exact ⟨e * w * c' ^ d' + c, by
    linear_combination (-1 : S) * hc + (-z) * hee + (z * e) * he' + (e * w * c' ^ d') * hc' +
      (w * c' ^ d' * ϖ ^ m) * hee⟩

end GlobalTheory.CompanionTheory.ValPowDvd
