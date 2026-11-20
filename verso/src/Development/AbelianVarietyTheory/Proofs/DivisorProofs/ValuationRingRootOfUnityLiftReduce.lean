import Mathlib
open NumberField

namespace GlobalTheory

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, m = n + 1` from `⟨m - 1, by omega⟩`. Use `IsPrimitiveRoot.mk_of_lt _ hm (by rw [← map_pow, hq.pow_eq_one, map_one]) fun l hl hlt h1 => ?_` and prove the remaining obligations. Establish `hp` using `congrArg φ hq.prod_one_sub_pow_eq_order`. Rewrite `hp` using `[map_prod]`. Establish `hz : ∏ k ∈ Finset.range n, φ (1 - q ^ (k + 1)) = 0`.

Use `Finset.prod_eq_zero (i := l - 1) (Finset.mem_range.2 (by omega)) ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_one, map_pow, Nat.sub_add_cancel hl, h1, sub_self]`. Rewrite `hp` using `[hz]`. Establish `hu' : IsUnit (φ ((n : o) + 1))`. Use `hu.map φ` as an intermediate fact.

Simplify using `using this`. Conclude with `hu'.ne_zero hp.symm`.
-/
theorem isPrimitiveRoot_map_of_isUnit_order' {o K : Type} [CommRing o] [IsDomain o] [CommRing K] [IsDomain K]
    (φ : o →+* K) {m : ℕ} (hm : 0 < m) {q : o} (hq : IsPrimitiveRoot q m) (hu : IsUnit (m : o)) :
    IsPrimitiveRoot (φ q) m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine IsPrimitiveRoot.mk_of_lt _ hm (by rw [← map_pow, hq.pow_eq_one, map_one]) fun l hl hlt h1 => ?_
  have hp := congrArg φ hq.prod_one_sub_pow_eq_order
  rw [map_prod] at hp
  have hz : ∏ k ∈ Finset.range n, φ (1 - q ^ (k + 1)) = 0 := by
    refine Finset.prod_eq_zero (i := l - 1) (Finset.mem_range.2 (by omega)) ?_
    rw [map_sub, map_one, map_pow, Nat.sub_add_cancel hl, h1, sub_self]
  rw [hz] at hp
  have hu' : IsUnit (φ ((n : o) + 1)) := by
    have := hu.map φ; simpa using this
  exact hu'.ne_zero hp.symm

/- English proof (translation)
Introduce `U Ω k _ _ _ _ _ _ _ h n hn ζ hζ`. Establish `hinj : Function.Injective (algebraMap U Ω)` using `IsFractionRing.injective U Ω`. Establish `hn0 : 0 < n`. Break down `Nat.eq_zero_or_pos n with h0 | h0` into its components or cases. Substitute `h0` using the available equality.

Simplify using `at hn`. Conclude with `h0`. Establish `unitOf : ∀ a : U, (algebraMap U Ω a) ^ n = 1 → IsUnit a`. Introduce `a ha`. Establish `: a ^ n = 1` using `hinj (by rw [map_pow, ha, map_one])`.

Conclude with `IsUnit.of_mul_eq_one (a ^ (n - 1)) (by rw [← pow_succ', Nat.sub_add_cancel hn0, this])`. Establish `hex : ∃ z : Uˣ, algebraMap U Ω z = ζ`. Break down `(ValuationRing.iff_isInteger_or_isInteger U Ω).1 inferInstance (ζ : Ω) with ⟨a, ha⟩ | ⟨b, hb⟩` into its components or cases. Establish `hu` using `unitOf a (by rw [ha, ← Units.val_pow_eq_pow_val, hζ, Units.val_one])`. Conclude with `⟨hu.unit, by simpa using ha⟩`.

Establish `hb' : (algebraMap U Ω b) ^ n = 1`. Rewrite using `[hb, ← Units.val_inv_eq_inv_val, ← Units.val_pow_eq_pow_val, inv_pow, hζ, inv_one, Units.val_one]`. Establish `hu` using `unitOf b hb'`. Use `⟨hu.unit⁻¹, ?_⟩` and prove the remaining obligations. Establish `: algebraMap U Ω (hu.unit : U) = (ζ : Ω)⁻¹` using `by simpa using hb`.

Establish `key : algebraMap U Ω (hu.unit : U) * algebraMap U Ω ((hu.unit⁻¹ : Uˣ) : U) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Rewrite `key` using `[this, inv_mul_eq_one₀ ζ.ne_zero]`. Conclude with `key.symm`. Take `⟨z, hz⟩` from `hex`.

Use `⟨z, ⟨hz, fun hp => ?_⟩, fun w ⟨hw, _⟩ => Units.ext (hinj (by rw [hw, hz]))⟩` and prove the remaining obligations. Establish `hpz : IsPrimitiveRoot (z : U) n`. Rewrite using `[← IsPrimitiveRoot.map_iff_of_injective hinj, hz]`. Conclude with `IsPrimitiveRoot.coe_units_iff.2 hp`. Rewrite using `[← IsPrimitiveRoot.coe_units_iff]`.

Conclude with `isPrimitiveRoot_map_of_isUnit_order' h hn0 hpz hn`.
-/
theorem valuationRing_rootOfUnity_lift_reduce : ∀ (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω]
    [Algebra U Ω] [IsFractionRing U Ω] [Field k] (h : U →+* k) (n : ℕ), IsUnit (n : U) → ∀ ζ : Ωˣ, ζ ^ n = 1 →
    ∃! z : Uˣ, algebraMap U Ω z = ζ ∧ (IsPrimitiveRoot ζ n → IsPrimitiveRoot (Units.map (h : U →* k) z) n) := by
  intro U Ω k _ _ _ _ _ _ _ h n hn ζ hζ
  have hinj : Function.Injective (algebraMap U Ω) := IsFractionRing.injective U Ω
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at hn
    · exact h0

  have unitOf : ∀ a : U, (algebraMap U Ω a) ^ n = 1 → IsUnit a := by
    intro a ha
    have : a ^ n = 1 := hinj (by rw [map_pow, ha, map_one])
    exact IsUnit.of_mul_eq_one (a ^ (n - 1)) (by rw [← pow_succ', Nat.sub_add_cancel hn0, this])
  have hex : ∃ z : Uˣ, algebraMap U Ω z = ζ := by
    rcases (ValuationRing.iff_isInteger_or_isInteger U Ω).1 inferInstance (ζ : Ω) with ⟨a, ha⟩ | ⟨b, hb⟩
    · have hu := unitOf a (by rw [ha, ← Units.val_pow_eq_pow_val, hζ, Units.val_one])
      exact ⟨hu.unit, by simpa using ha⟩
    · have hb' : (algebraMap U Ω b) ^ n = 1 := by
        rw [hb, ← Units.val_inv_eq_inv_val, ← Units.val_pow_eq_pow_val, inv_pow, hζ, inv_one, Units.val_one]
      have hu := unitOf b hb'
      refine ⟨hu.unit⁻¹, ?_⟩
      have : algebraMap U Ω (hu.unit : U) = (ζ : Ω)⁻¹ := by simpa using hb
      have key : algebraMap U Ω (hu.unit : U) * algebraMap U Ω ((hu.unit⁻¹ : Uˣ) : U) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [this, inv_mul_eq_one₀ ζ.ne_zero] at key
      exact key.symm
  obtain ⟨z, hz⟩ := hex
  refine ⟨z, ⟨hz, fun hp => ?_⟩, fun w ⟨hw, _⟩ => Units.ext (hinj (by rw [hw, hz]))⟩
  have hpz : IsPrimitiveRoot (z : U) n := by
    rw [← IsPrimitiveRoot.map_iff_of_injective hinj, hz]
    exact IsPrimitiveRoot.coe_units_iff.2 hp
  rw [← IsPrimitiveRoot.coe_units_iff]
  exact isPrimitiveRoot_map_of_isUnit_order' h hn0 hpz hn

end GlobalTheory
