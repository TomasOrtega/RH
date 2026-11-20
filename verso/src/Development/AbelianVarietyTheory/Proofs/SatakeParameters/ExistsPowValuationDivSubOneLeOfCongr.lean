import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ v c hc n`. Use `set e : ℕ := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {c})).factors with he`. Establish `hval : v.valuation E (c : E) = WithZero.exp (-(e : ℤ))`. Establish `h` using `HeightOneSpectrum.valuation_of_algebraMap (K := E) v c`. Establish `h' : v.valuation E (c : E) = v.intValuation c` using `h`.

Rewrite using `[h', v.intValuation_if_neg hc]`. Establish `hcE : (c : E) ≠ 0`. Simplify using `using hc`. Use `⟨n + e, fun k hk => ?_⟩` and prove the remaining obligations. Establish `hle : v.intValuation (k - c) ≤ WithZero.exp (-((n + e : ℕ) : ℤ))` using `(v.intValuation_le_pow_iff_mem (k - c) (n + e)).2 hk`.

Establish `hdiff : v.valuation E (((k - c : 𝓞 E)) : E) = v.intValuation (k - c)` using `HeightOneSpectrum.valuation_of_algebraMap (K := E) v (k - c)`. Establish `heq : (k : E) / (c : E) - 1 = (((k - c : 𝓞 E)) : E) / (c : E)`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[heq, map_div₀, hval, hdiff]`.

Establish `hpos : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp (-(e : ℤ))` using `WithZero.exp_pos`. Rewrite using `[div_le_iff₀ hpos, ← WithZero.exp_add]`. Establish `hexp : -(n : ℤ) + -(e : ℤ) = -((n + e : ℕ) : ℤ)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hexp]` and apply the resulting hypothesis.
-/
theorem exists_pow_valuation_div_sub_one_le :
    ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E), c ≠ 0 →
      ∀ n : ℕ, ∃ N : ℕ, ∀ k : 𝓞 E, k - c ∈ v.asIdeal ^ N →
        v.valuation E ((k : E) / (c : E) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  intro E _ _ v c hc n
  set e : ℕ := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {c})).factors with he
  have hval : v.valuation E (c : E) = WithZero.exp (-(e : ℤ)) := by
    have h := HeightOneSpectrum.valuation_of_algebraMap (K := E) v c
    have h' : v.valuation E (c : E) = v.intValuation c := h
    rw [h', v.intValuation_if_neg hc]
  have hcE : (c : E) ≠ 0 := by
    simpa using hc
  refine ⟨n + e, fun k hk => ?_⟩
  have hle : v.intValuation (k - c) ≤ WithZero.exp (-((n + e : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_mem (k - c) (n + e)).2 hk
  have hdiff : v.valuation E (((k - c : 𝓞 E)) : E) = v.intValuation (k - c) :=
    HeightOneSpectrum.valuation_of_algebraMap (K := E) v (k - c)
  have heq : (k : E) / (c : E) - 1 = (((k - c : 𝓞 E)) : E) / (c : E) := by
    push_cast
    field_simp
  rw [heq, map_div₀, hval, hdiff]
  have hpos : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp (-(e : ℤ)) := WithZero.exp_pos
  rw [div_le_iff₀ hpos, ← WithZero.exp_add]
  have hexp : -(n : ℤ) + -(e : ℤ) = -((n + e : ℕ) : ℤ) := by
    push_cast
    ring
  rwa [hexp]

end GlobalTheory
