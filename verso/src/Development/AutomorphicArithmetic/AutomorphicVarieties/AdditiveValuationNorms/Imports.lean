import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe

open UpperTheory.V UpperTheory.V.PropA

/- English proof (translation)
Introduce `l _ X _ _ g k`. Establish `hpoly : (Polynomial.C (l : ℤ)) ∣ ((Polynomial.X - 1) ^ l ^ k - (Polynomial.X ^ l ^ k - 1) : Polynomial ℤ)`. Rewrite using `[Polynomial.C_dvd_iff_dvd_coeff]`. Introduce `i`. Establish `hmap : Polynomial.map (Int.castRingHom (ZMod l)) ((Polynomial.X - 1) ^ l ^ k - (Polynomial.X ^ l ^ k - 1) : Polynomial ℤ) = 0`.

Simplify using `only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]`. Rewrite using `[sub_pow_char_pow, one_pow, sub_self]`. Establish `hc` using `congrArg (fun P => Polynomial.coeff P i) hmap`. Simplify using `only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc`. Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1 hc`.

Take `⟨Q, hQ⟩` from `hpoly`. Establish `key : (g - 1) ^ l ^ k - (g ^ l ^ k - 1) = (l : Module.End ℤ_[l] X) * Polynomial.aeval g Q`. Use `congrArg (Polynomial.aeval g) hQ` as an intermediate fact. Simplify using `using this`. Establish `step : ∀ f f' : Module.End ℤ_[l] X, (∃ h : Module.End ℤ_[l] X, f - f' = (l : Module.End ℤ_[l] X) * h) → InPow 1 f' → InPow 1 f`.

Introduce and unpack `f f' ⟨h, hh⟩ H x`. Take `⟨y, hy⟩` from `H x`. Use `⟨y + h x, ?_⟩` and prove the remaining obligations. Establish `hf : f = (l : Module.End ℤ_[l] X) * h + f'` using `eq_add_of_sub_eq hh`. Rewrite `hy`, the goal using `[pow_one]`.

Rewrite using `[hf, LinearMap.add_apply, Module.End.mul_apply, Module.End.natCast_apply, hy, smul_add, Nat.cast_smul_eq_nsmul ℤ_[l] l (h x), add_comm]`. Prove the components needed by the constructor for the conclusion. Conclude with `step _ _ ⟨-Polynomial.aeval g Q, by rw [mul_neg, ← key, neg_sub]⟩`. Conclude with `step _ _ ⟨Polynomial.aeval g Q, key⟩`.
-/
theorem UpperTheory.V.PropA.frob :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (g : Module.End ℤ_[l] X) (k : ℕ),
      InPow 1 ((g - 1) ^ l ^ k) ↔ InPow 1 (g ^ l ^ k - 1) := by
  intro l _ X _ _ g k
  have hpoly : (Polynomial.C (l : ℤ)) ∣
      ((Polynomial.X - 1) ^ l ^ k - (Polynomial.X ^ l ^ k - 1) : Polynomial ℤ) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have hmap : Polynomial.map (Int.castRingHom (ZMod l))
        ((Polynomial.X - 1) ^ l ^ k - (Polynomial.X ^ l ^ k - 1) : Polynomial ℤ) = 0 := by
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
      rw [sub_pow_char_pow, one_pow, sub_self]
    have hc := congrArg (fun P => Polynomial.coeff P i) hmap
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1 hc
  obtain ⟨Q, hQ⟩ := hpoly
  have key : (g - 1) ^ l ^ k - (g ^ l ^ k - 1) = (l : Module.End ℤ_[l] X) * Polynomial.aeval g Q := by
    have := congrArg (Polynomial.aeval g) hQ
    simpa using this
  have step : ∀ f f' : Module.End ℤ_[l] X, (∃ h : Module.End ℤ_[l] X, f - f' = (l : Module.End ℤ_[l] X) * h) →
      InPow 1 f' → InPow 1 f := by
    rintro f f' ⟨h, hh⟩ H x
    obtain ⟨y, hy⟩ := H x
    refine ⟨y + h x, ?_⟩
    have hf : f = (l : Module.End ℤ_[l] X) * h + f' := eq_add_of_sub_eq hh
    rw [pow_one] at hy ⊢
    rw [hf, LinearMap.add_apply, Module.End.mul_apply, Module.End.natCast_apply, hy, smul_add,
      Nat.cast_smul_eq_nsmul ℤ_[l] l (h x), add_comm]
  constructor
  · exact step _ _ ⟨-Polynomial.aeval g Q, by rw [mul_neg, ← key, neg_sub]⟩
  · exact step _ _ ⟨Polynomial.aeval g Q, key⟩
