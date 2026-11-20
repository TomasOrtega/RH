import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `p hp`. Set `A : Subring ℂ` to `(Int.castRingHom ℂ).range`. Establish `hI : Ideal.span {(p : A)} ≠ ⊤`. Rewrite using `[Ne, Ideal.span_singleton_eq_top, isUnit_iff_exists_inv]`. Introduce and unpack `⟨⟨b, n, rfl⟩, hb⟩`.

Establish `h1 : ((p : ℂ)) * (n : ℂ) = 1`. Use `congrArg (Subtype.val) hb` as an intermediate fact. Simplify using `using this`. Establish `h2 : (p : ℤ) * n = 1` using `by exact_mod_cast h1`. Establish `h3 : (p : ℤ) ∣ 1` using `⟨n, h2.symm⟩`.

Establish `h4 : p ∣ 1` using `by exact_mod_cast h3`. Conclude with `hp.one_lt.ne' (Nat.dvd_one.mp h4)`. Take `⟨B, -, hB⟩` from `Ideal.image_subset_nonunits_valuationSubring _ hI`. Use `⟨B, hB ⟨(p : A), Ideal.subset_span rfl, by simp⟩⟩` and prove the remaining obligations.
-/
theorem exists_valuationSubring_complex_prime_mem_nonunits :
    ∀ p : ℕ, p.Prime → ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits := by
  intro p hp
  let A : Subring ℂ := (Int.castRingHom ℂ).range
  have hI : Ideal.span {(p : A)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top, isUnit_iff_exists_inv]
    rintro ⟨⟨b, n, rfl⟩, hb⟩
    have h1 : ((p : ℂ)) * (n : ℂ) = 1 := by
      have := congrArg (Subtype.val) hb
      simpa using this
    have h2 : (p : ℤ) * n = 1 := by exact_mod_cast h1
    have h3 : (p : ℤ) ∣ 1 := ⟨n, h2.symm⟩
    have h4 : p ∣ 1 := by exact_mod_cast h3
    exact hp.one_lt.ne' (Nat.dvd_one.mp h4)
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  refine ⟨B, hB ⟨(p : A), Ideal.subset_span rfl, by simp⟩⟩

end GlobalTheory
