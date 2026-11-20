import Mathlib

noncomputable section

open IsDedekindDomain NumberField

namespace PI.ProdFormulaE.Tr

/- English proof (translation)
Establish `hℓ : (ℓ : F) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero`. Establish `hval : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), v.valuation F ((X : F) / ℓ) ≤ 1`. Introduce `v`. Rewrite using `[map_div₀]`. Establish `hℓv : v.valuation F (ℓ : F) = v.intValuation (ℓ : 𝓞 F)`.

Rewrite using `[← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := F)]`. Simplify using the standard rewrite rules. Distinguish the cases in `hv : (ℓ : 𝓞 F) ∈ v.asIdeal`. Establish `hpos : v.valuation F (ℓ : F) ≠ 0` using `(Valuation.ne_zero_iff _).2 hℓ`. Conclude with `(div_le_one₀ (zero_lt_iff.2 hpos)).2 (h v hv)`.

Rewrite using `[hℓv, IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hv, div_one]`. Conclude with `IsDedekindDomain.HeightOneSpectrum.valuation_le_one v X`. Take `⟨Z, hZ⟩` from `IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F ((X : F) / ℓ) hval`. Use `⟨Z, ?_⟩` and prove the remaining obligations. Apply `IsFractionRing.injective (𝓞 F) F` to reduce the goal to its premises.

Establish `hZ' : algebraMap (𝓞 F) F Z = (X : F) / ℓ` using `hZ`. Establish `hc : (ℓ : F) * ((X : F) / ℓ) = X` using `by field_simp`. Rewrite using `[map_mul, hZ', map_natCast, hc]`. Apply the tactic sequence `try rfl`.
-/
theorem exists_eq_ell_mul {F : Type} [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (X : 𝓞 F)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∈ v.asIdeal →
      v.valuation F (X : F) ≤ v.valuation F (ℓ : F)) :
    ∃ Z : 𝓞 F, X = ℓ * Z := by
  have hℓ : (ℓ : F) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
  have hval : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), v.valuation F ((X : F) / ℓ) ≤ 1 := by
    intro v
    rw [map_div₀]
    have hℓv : v.valuation F (ℓ : F) = v.intValuation (ℓ : 𝓞 F) := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := F)]
      simp
    by_cases hv : (ℓ : 𝓞 F) ∈ v.asIdeal
    · have hpos : v.valuation F (ℓ : F) ≠ 0 := (Valuation.ne_zero_iff _).2 hℓ
      exact (div_le_one₀ (zero_lt_iff.2 hpos)).2 (h v hv)
    · rw [hℓv, IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hv, div_one]
      exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v X
  obtain ⟨Z, hZ⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F
    ((X : F) / ℓ) hval
  refine ⟨Z, ?_⟩
  apply IsFractionRing.injective (𝓞 F) F
  have hZ' : algebraMap (𝓞 F) F Z = (X : F) / ℓ := hZ
  have hc : (ℓ : F) * ((X : F) / ℓ) = X := by field_simp
  rw [map_mul, hZ', map_natCast, hc]
  try rfl

/- English proof (translation)
Take `⟨n, -, hn⟩` from `PadicInt.exists_mem_range (⟨c, hc⟩ : ℤ_[ℓ])`. Rewrite `hn` using `[IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_lt_one_iff_dvd]`. Take `⟨y, hy⟩` from `hn`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `hy' : c - (n : ℚ_[ℓ]) = ℓ * (y : ℚ_[ℓ])`.

Use `congrArg (fun w : ℤ_[ℓ] => (w : ℚ_[ℓ])) hy` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `hℓ : (ℓ : ℚ_[ℓ]) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero`. Rewrite using `[show ((n : ℤ) : ℚ_[ℓ]) = (n : ℚ_[ℓ]) by push_cast; rfl, hy', mul_div_cancel_left₀ _ hℓ]`.

Conclude with `y.norm_le_one`.
-/
theorem exists_int_approx (ℓ : ℕ) [Fact ℓ.Prime] (c : ℚ_[ℓ]) (hc : ‖c‖ ≤ 1) :
    ∃ m : ℤ, ‖(c - m) / ℓ‖ ≤ 1 := by
  obtain ⟨n, -, hn⟩ := PadicInt.exists_mem_range (⟨c, hc⟩ : ℤ_[ℓ])
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_lt_one_iff_dvd] at hn
  obtain ⟨y, hy⟩ := hn
  refine ⟨n, ?_⟩
  have hy' : c - (n : ℚ_[ℓ]) = ℓ * (y : ℚ_[ℓ]) := by
    have := congrArg (fun w : ℤ_[ℓ] => (w : ℚ_[ℓ])) hy
    push_cast at this
    exact this
  have hℓ : (ℓ : ℚ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
  rw [show ((n : ℤ) : ℚ_[ℓ]) = (n : ℚ_[ℓ]) by push_cast; rfl, hy', mul_div_cancel_left₀ _ hℓ]
  exact y.norm_le_one

end PI.ProdFormulaE.Tr
