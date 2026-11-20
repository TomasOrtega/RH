import Mathlib
open NumberField

namespace GlobalTheory.UnitReal

/- English proof (translation)
Introduce `E _ _ _ q hq hqt u hu φ`. Use `set I : Ideal (𝓞 E) := Ideal.span {((q : ℕ) : 𝓞 E)} with hI`. Use `set c : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv with hc`. Use `set v : (𝓞 E)ˣ := IsCMField.unitsComplexConj E u with hv`. Establish `hvc : (v : 𝓞 E) = c u` using `rfl`.

Establish `hv1 : (v : 𝓞 E) - 1 ∈ I`. Rewrite `hu`, the goal using `[hI, Ideal.mem_span_singleton]`. Take `⟨y, hy⟩` from `hu`. Use `⟨c y, ?_⟩` and prove the remaining obligations. Rewrite using `[hvc, ← map_one c, ← map_sub, hy, map_mul, map_natCast]`.

Use `set ζ : (𝓞 E)ˣ := (IsCMField.unitsMulComplexConjInv E u : (𝓞 E)ˣ) with hζ`. Establish `hζv : ζ * v = u` using `by rw [hζ, IsCMField.unitsMulComplexConjInv_apply, inv_mul_cancel_right]`. Establish `hζ1 : Ideal.Quotient.mk I (ζ : 𝓞 E) = 1`. Establish `a1 : Ideal.Quotient.mk I (u : 𝓞 E) = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]`.

Conclude with `hu`. Establish `a2 : Ideal.Quotient.mk I (v : 𝓞 E) = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]`. Conclude with `hv1`. Use `congrArg (fun x : (𝓞 E)ˣ => Ideal.Quotient.mk I (x : 𝓞 E)) hζv` as an intermediate fact.

Simplify using `only [Units.val_mul, map_mul, a1, a2, mul_one] at this`. Conclude with `this`. Establish `ht : ζ ^ Nat.card (Units.torsion E) = 1`. Establish `h4 : (IsCMField.unitsMulComplexConjInv E u) ^ Nat.card (Units.torsion E) = 1` using `pow_card_eq_one'`. Use `congrArg Subtype.val h4` as an intermediate fact.

Simplify using `only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this`. Conclude with `this`. Establish `hζeq : ζ = 1`. Assume the negation of the conclusion as `hne`. Establish `hne' : (ζ : 𝓞 E) - 1 ≠ 0`.

Rewrite using `[sub_ne_zero]`. Introduce `h`. Conclude with `hne (Units.ext h)`. Establish `hsum : ∑ j ∈ Finset.range (Nat.card (Units.torsion E)), (ζ : 𝓞 E) ^ j = 0`. Use `mul_geom_sum ((ζ : 𝓞 E)) (Nat.card (Units.torsion E))` as an intermediate fact.

Rewrite `this` using `[← Units.val_pow_eq_pow_val, ht, Units.val_one, sub_self]`. Conclude with `(mul_eq_zero.mp this).resolve_left hne'`. Establish `hmod` using `congrArg (Ideal.Quotient.mk I) hsum`. Simplify using `only [map_sum, map_pow, hζ1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, map_zero] at hmod`. Establish `hmem : ((Nat.card (Units.torsion E) : ℕ) : 𝓞 E) ∈ I`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `hmod`. Rewrite `hmem` using `[hI, Ideal.mem_span_singleton]`. Take `⟨y, hy⟩` from `hmem`. Establish `hn` using `congrArg (Algebra.norm ℤ) hy`.

Rewrite `hn` using `[map_mul]`. Establish `e1 : ∀ n : ℕ, Algebra.norm ℤ ((n : 𝓞 E)) = (n : ℤ) ^ Module.finrank ℤ (𝓞 E)`. Introduce `n`. Rewrite using `[← map_natCast (algebraMap ℤ (𝓞 E)), Algebra.norm_algebraMap]`. Rewrite `hn` using `[e1, e1]`.

Establish `hd : 0 < Module.finrank ℤ (𝓞 E)`. Rewrite using `[RingOfIntegers.rank]`. Conclude with `Module.finrank_pos`. Establish `hdvd : (q : ℤ) ∣ (Nat.card (Units.torsion E) : ℤ) ^ Module.finrank ℤ (𝓞 E)`. Rewrite using `[hn]`.

Conclude with `Dvd.dvd.mul_right (dvd_pow_self _ hd.ne') _`. Establish `hdvd' : q ∣ Nat.card (Units.torsion E) ^ Module.finrank ℤ (𝓞 E)` using `by exact_mod_cast hdvd`. Conclude with `hqt (hq.dvd_of_dvd_pow hdvd')`. Establish `huv : (v : 𝓞 E) = u` using `by rw [← hζv, hζeq, one_mul]`. Establish `hE : IsCMField.complexConj E ((u : 𝓞 E) : E) = ((u : 𝓞 E) : E)`.

Use `congrArg (fun x : 𝓞 E => (x : E)) huv` as an intermediate fact. Conclude with `this`. Rewrite using `[← IsCMField.complexEmbedding_complexConj, hE]`.
-/
theorem unit_real_of_congr_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : ℕ), q.Prime →
    ¬ q ∣ Nat.card (Units.torsion E) → ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} →
    ∀ φ : E →+* ℂ, starRingEnd ℂ (φ ((u : 𝓞 E) : E)) = φ ((u : 𝓞 E) : E) := by
  intro E _ _ _ q hq hqt u hu φ
  set I : Ideal (𝓞 E) := Ideal.span {((q : ℕ) : 𝓞 E)} with hI
  set c : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv with hc
  set v : (𝓞 E)ˣ := IsCMField.unitsComplexConj E u with hv
  have hvc : (v : 𝓞 E) = c u := rfl
  have hv1 : (v : 𝓞 E) - 1 ∈ I := by
    rw [hI, Ideal.mem_span_singleton] at hu ⊢
    obtain ⟨y, hy⟩ := hu
    refine ⟨c y, ?_⟩
    rw [hvc, ← map_one c, ← map_sub, hy, map_mul, map_natCast]
  set ζ : (𝓞 E)ˣ := (IsCMField.unitsMulComplexConjInv E u : (𝓞 E)ˣ) with hζ
  have hζv : ζ * v = u := by rw [hζ, IsCMField.unitsMulComplexConjInv_apply, inv_mul_cancel_right]
  have hζ1 : Ideal.Quotient.mk I (ζ : 𝓞 E) = 1 := by
    have a1 : Ideal.Quotient.mk I (u : 𝓞 E) = 1 := by
      rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hu
    have a2 : Ideal.Quotient.mk I (v : 𝓞 E) = 1 := by
      rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hv1
    have := congrArg (fun x : (𝓞 E)ˣ => Ideal.Quotient.mk I (x : 𝓞 E)) hζv
    simp only [Units.val_mul, map_mul, a1, a2, mul_one] at this
    exact this
  have ht : ζ ^ Nat.card (Units.torsion E) = 1 := by
    have h4 : (IsCMField.unitsMulComplexConjInv E u) ^ Nat.card (Units.torsion E) = 1 := pow_card_eq_one'
    have := congrArg Subtype.val h4
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    exact this
  have hζeq : ζ = 1 := by
    by_contra hne
    have hne' : (ζ : 𝓞 E) - 1 ≠ 0 := by
      rw [sub_ne_zero]; intro h; exact hne (Units.ext h)
    have hsum : ∑ j ∈ Finset.range (Nat.card (Units.torsion E)), (ζ : 𝓞 E) ^ j = 0 := by
      have := mul_geom_sum ((ζ : 𝓞 E)) (Nat.card (Units.torsion E))
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one, sub_self] at this
      exact (mul_eq_zero.mp this).resolve_left hne'
    have hmod := congrArg (Ideal.Quotient.mk I) hsum
    simp only [map_sum, map_pow, hζ1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, map_zero] at hmod
    have hmem : ((Nat.card (Units.torsion E) : ℕ) : 𝓞 E) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hmod
    rw [hI, Ideal.mem_span_singleton] at hmem
    obtain ⟨y, hy⟩ := hmem
    have hn := congrArg (Algebra.norm ℤ) hy
    rw [map_mul] at hn
    have e1 : ∀ n : ℕ, Algebra.norm ℤ ((n : 𝓞 E)) = (n : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
      intro n
      rw [← map_natCast (algebraMap ℤ (𝓞 E)), Algebra.norm_algebraMap]
    rw [e1, e1] at hn
    have hd : 0 < Module.finrank ℤ (𝓞 E) := by
      rw [RingOfIntegers.rank]; exact Module.finrank_pos
    have hdvd : (q : ℤ) ∣ (Nat.card (Units.torsion E) : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
      rw [hn]; exact Dvd.dvd.mul_right (dvd_pow_self _ hd.ne') _
    have hdvd' : q ∣ Nat.card (Units.torsion E) ^ Module.finrank ℤ (𝓞 E) := by exact_mod_cast hdvd
    exact hqt (hq.dvd_of_dvd_pow hdvd')
  have huv : (v : 𝓞 E) = u := by rw [← hζv, hζeq, one_mul]
  have hE : IsCMField.complexConj E ((u : 𝓞 E) : E) = ((u : 𝓞 E) : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) huv
    exact this
  rw [← IsCMField.complexEmbedding_complexConj, hE]

end GlobalTheory.UnitReal
