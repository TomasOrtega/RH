import Mathlib

noncomputable section

namespace ReciprocityTheory.Aut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Establish `hint` using `Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Establish `hle : Valued.v (x : v.adicCompletion F) ≤ 1` using `x.2`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Conclude with `lt_of_le_of_ne hle (fun h => hx ((hint.isUnit_iff_valuation_eq_one (x := x)).mpr h))`. Introduce `hx hu`. Conclude with `(ne_of_lt hx) ((hint.isUnit_iff_valuation_eq_one (x := x)).mp hu)`.
-/
theorem mem_maxIdeal_iff (x : v.adicCompletionIntegers F) :
    x ∈ maximalIdeal (v.adicCompletionIntegers F) ↔ Valued.v (x : v.adicCompletion F) < 1 := by
  have hint := Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hle : Valued.v (x : v.adicCompletion F) ≤ 1 := x.2
  constructor
  · intro hx
    exact lt_of_le_of_ne hle (fun h => hx ((hint.isUnit_iff_valuation_eq_one (x := x)).mpr h))
  · intro hx hu
    exact (ne_of_lt hx) ((hint.isUnit_iff_valuation_eq_one (x := x)).mp hu)

/- English proof (translation)
Break down `eq_or_ne (Valued.v x) 0 with h0 | h0` into its components or cases. Rewrite using `[h0]`. Conclude with `zero_le'`. Take `⟨a, ha⟩` from `WithZero.ne_zero_iff_exists.mp h0`. Rewrite `h`, the goal using `[← ha]`.

Establish `h1 : a < 1` using `by exact_mod_cast h`. Establish `h2 : Multiplicative.toAdd a < 0`. Rewrite using `[← toAdd_one, Multiplicative.toAdd_lt]`. Conclude with `h1`. Establish `h3 : a ≤ Multiplicative.ofAdd (-1 : ℤ)`.

Rewrite using `[← Multiplicative.toAdd_le, toAdd_ofAdd]`. Use linear arithmetic over natural numbers and integers. Use `show (a : WithZero (Multiplicative ℤ)) ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`. Conclude with `WithZero.coe_le_coe.mpr h3`.
-/
theorem val_le_exp_neg_one_of_lt_one {x : v.adicCompletion F} (h : Valued.v x < 1) :
    Valued.v x ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne (Valued.v x) 0 with h0 | h0
  · rw [h0]
    exact zero_le'
  · obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp h0
    rw [← ha] at h ⊢
    have h1 : a < 1 := by exact_mod_cast h
    have h2 : Multiplicative.toAdd a < 0 := by
      rw [← toAdd_one, Multiplicative.toAdd_lt]
      exact h1
    have h3 : a ≤ Multiplicative.ofAdd (-1 : ℤ) := by
      rw [← Multiplicative.toAdd_le, toAdd_ofAdd]
      omega
    show (a : WithZero (Multiplicative ℤ)) ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    exact WithZero.coe_le_coe.mpr h3

/- English proof (translation)
Establish `hπ0 : (π : v.adicCompletion F) ≠ 0`. Introduce `h`. Rewrite `hπ` using `[h, map_zero]`. Conclude with `WithZero.zero_ne_coe hπ`. Establish `hexp : WithZero.exp (-1 : ℤ) < 1`.

Rewrite using `[← WithZero.exp_zero]`. Conclude with `WithZero.exp_lt_exp.mpr (by norm_num)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[mem_maxIdeal_iff]`.

Establish `hx1` using `val_le_exp_neg_one_of_lt_one v hx`. Establish `hq : Valued.v ((x : v.adicCompletion F) / π) ≤ 1`. Rewrite using `[map_div₀, hπ]`. Conclude with `(div_le_one₀ (lt_of_le_of_ne zero_le' (Ne.symm (by rw [← hπ]; exact (map_ne_zero _).mpr hπ0)))).mpr hx1`. Rewrite using `[Ideal.mem_span_singleton']`.

Use `⟨⟨(x : v.adicCompletion F) / π, hq⟩, ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using `[div_mul_cancel₀ _ hπ0]`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff] show π ∈ maximalIdeal _`. Rewrite using `[mem_maxIdeal_iff, hπ]`.

Conclude with `hexp`.
-/
theorem maxIdeal_eq_span {π : v.adicCompletionIntegers F}
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {π} := by
  have hπ0 : (π : v.adicCompletion F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  have hexp : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  apply le_antisymm
  · intro x hx
    rw [mem_maxIdeal_iff] at hx
    have hx1 := val_le_exp_neg_one_of_lt_one v hx
    have hq : Valued.v ((x : v.adicCompletion F) / π) ≤ 1 := by
      rw [map_div₀, hπ]
      exact (div_le_one₀ (lt_of_le_of_ne zero_le' (Ne.symm (by rw [← hπ]; exact (map_ne_zero _).mpr hπ0)))).mpr hx1
    rw [Ideal.mem_span_singleton']
    refine ⟨⟨(x : v.adicCompletion F) / π, hq⟩, ?_⟩
    ext
    simp [div_mul_cancel₀ _ hπ0]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show π ∈ maximalIdeal _
    rw [mem_maxIdeal_iff, hπ]
    exact hexp

end ReciprocityTheory.Aut
