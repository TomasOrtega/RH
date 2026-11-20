import Development.DiscreteGroups.GlobalIrreducibility.DzStickDefs

noncomputable section

namespace DiscreteGroups.sglob.Stick

open NumberField IsDedekindDomain nonZeroDivisors

universe u

/- English proof (translation)
Assume the negation of the conclusion as `hab`. Establish `hsub : a - b ≠ 0` using `sub_ne_zero.mpr hab`. Establish `h1 : (∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)) * (a - b) = 0`. Rewrite using `[(Commute.all a b).geom_sum₂_mul, ha, hb, sub_self]`. Establish `h2 : ∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i) = 0` using `(mul_eq_zero.mp h1).resolve_right hsub`.

Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Conclude with `hn (by simp)`. Establish `h3 : (n : A ⧸ P) * Ideal.Quotient.mk P b ^ (n - 1) = 0`. Use `congrArg (Ideal.Quotient.mk P) h2` as an intermediate fact.

Rewrite `this` using `[map_sum, map_zero]`. Rewrite using `[← this]`. Establish `: ∀ i ∈ Finset.range n, Ideal.Quotient.mk P (a ^ i * b ^ (n - 1 - i)) = Ideal.Quotient.mk P b ^ (n - 1)`. Introduce `i hi`. Rewrite using `[map_mul, map_pow, map_pow, h, ← pow_add]`.

Use `congr 1`. Use `Finset.mem_range.mp hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Establish `h4 : (n : A ⧸ P) = 0`.

Establish `h5 : Ideal.Quotient.mk P b ^ (n - 1) * Ideal.Quotient.mk P b = 1`. Rewrite using `[← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0), ← map_pow, hb, map_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h5, mul_one]`. Use `_ = 0 := by rw [← mul_assoc, h3, zero_mul]`.

Apply `hn` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast, h4]`.
-/
theorem eq_of_pow_eq_one_of_mk_eq {A : Type*} [CommRing A] [IsDomain A] (P : Ideal A) {n : ℕ}
    (hn : (n : A) ∉ P) {a b : A} (ha : a ^ n = 1) (hb : b ^ n = 1)
    (h : Ideal.Quotient.mk P a = Ideal.Quotient.mk P b) : a = b := by
  by_contra hab
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hab
  have h1 : (∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)) * (a - b) = 0 := by
    rw [(Commute.all a b).geom_sum₂_mul, ha, hb, sub_self]
  have h2 : ∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i) = 0 :=
    (mul_eq_zero.mp h1).resolve_right hsub
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  have h3 : (n : A ⧸ P) * Ideal.Quotient.mk P b ^ (n - 1) = 0 := by
    have := congrArg (Ideal.Quotient.mk P) h2
    rw [map_sum, map_zero] at this
    rw [← this]
    have : ∀ i ∈ Finset.range n, Ideal.Quotient.mk P (a ^ i * b ^ (n - 1 - i)) =
        Ideal.Quotient.mk P b ^ (n - 1) := by
      intro i hi
      rw [map_mul, map_pow, map_pow, h, ← pow_add]
      congr 1
      have := Finset.mem_range.mp hi
      omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h4 : (n : A ⧸ P) = 0 := by
    have h5 : Ideal.Quotient.mk P b ^ (n - 1) * Ideal.Quotient.mk P b = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0), ← map_pow, hb, map_one]
    calc (n : A ⧸ P) = (n : A ⧸ P) * (Ideal.Quotient.mk P b ^ (n - 1) * Ideal.Quotient.mk P b) := by
          rw [h5, mul_one]
      _ = 0 := by rw [← mul_assoc, h3, zero_mul]
  apply hn
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, h4]

/- English proof (translation)
Introduce `hmem`. Establish `h0 : (n : A ⧸ P) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hmem`. Take `⟨m, hm⟩` from `hn`.

Establish `hq : ((Fintype.card k : ℕ) : A ⧸ P) = 0`. Rewrite using `[← map_natCast ι, Nat.cast_card_eq_zero, map_zero]`. Establish `hpos : 1 ≤ Fintype.card k` using `Fintype.card_pos`. Establish `h1 : ((Fintype.card k - 1 : ℕ) : A ⧸ P) = 0`. Rewrite using `[hm, Nat.cast_mul, h0, zero_mul]`.

Establish `h2 : ((Fintype.card k - 1 + 1 : ℕ) : A ⧸ P) = 1`. Rewrite using `[Nat.cast_add, h1, Nat.cast_one, zero_add]`. Rewrite `h2` using `[Nat.sub_add_cancel hpos, hq]`. Conclude with `zero_ne_one h2`.
-/
theorem natCast_not_mem_of_dvd {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime] {k : Type*}
    [Field k] [Fintype k] (ι : k →+* A ⧸ P) {n : ℕ} (hn : n ∣ Fintype.card k - 1) :
    (n : A) ∉ P := by
  intro hmem
  have h0 : (n : A ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  obtain ⟨m, hm⟩ := hn
  have hq : ((Fintype.card k : ℕ) : A ⧸ P) = 0 := by
    rw [← map_natCast ι, Nat.cast_card_eq_zero, map_zero]
  have hpos : 1 ≤ Fintype.card k := Fintype.card_pos
  have h1 : ((Fintype.card k - 1 : ℕ) : A ⧸ P) = 0 := by
    rw [hm, Nat.cast_mul, h0, zero_mul]
  have h2 : ((Fintype.card k - 1 + 1 : ℕ) : A ⧸ P) = 1 := by
    rw [Nat.cast_add, h1, Nat.cast_one, zero_add]
  rw [Nat.sub_add_cancel hpos, hq] at h2
  exact zero_ne_one h2

/- English proof (translation)
Use `⟨by rw [← map_pow, hμ.pow_eq_one, map_one], fun l hl => ?_⟩` and prove the remaining obligations. Apply `hμ.dvd_of_pow_eq_one` to reduce the goal to its premises. Use `eq_of_pow_eq_one_of_mk_eq P hn ?_ (one_pow n) (by rw [map_pow, hl, map_one])` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one, one_pow]`.
-/
theorem isPrimitiveRoot_mk {A : Type*} [CommRing A] [IsDomain A] (P : Ideal A) {n : ℕ}
    (hn : (n : A) ∉ P) {μ : A} (hμ : IsPrimitiveRoot μ n) :
    IsPrimitiveRoot (Ideal.Quotient.mk P μ) n := by
  refine ⟨by rw [← map_pow, hμ.pow_eq_one, map_one], fun l hl => ?_⟩
  apply hμ.dvd_of_pow_eq_one
  refine eq_of_pow_eq_one_of_mk_eq P hn ?_ (one_pow n) (by rw [map_pow, hl, map_one])
  rw [← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one, one_pow]

/- English proof (translation)
Establish `hnP : (n : A) ∉ P` using `natCast_not_mem_of_dvd P ι hn`. Establish `hq1 : 0 < Fintype.card k - 1` using `Nat.sub_pos_of_lt Fintype.one_lt_card`. Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Rewrite `hn` using `[zero_dvd_iff]`.

Use linear arithmetic over natural numbers and integers. Establish `: NeZero n` using `⟨hn0⟩`. Use `set m := (Fintype.card k - 1) / n with hm`. Establish `hmn : m * n = Fintype.card k - 1` using `Nat.div_mul_cancel hn`. Establish `hm0 : m ≠ 0`.

Introduce and unpack `h0`. Rewrite `hmn` using `[h0, zero_mul]`. Use linear arithmetic over natural numbers and integers. Establish `hprim` using `isPrimitiveRoot_mk P hnP hμ`. Establish `hex : ∀ x : kˣ, ∃ y : A, y ^ n = 1 ∧ Ideal.Quotient.mk P y = ι (x : k) ^ m`.

Introduce `x`. Establish `hx : (ι (x : k) ^ m) ^ n = 1`. Rewrite using `[← pow_mul, hmn, ← map_pow, FiniteField.pow_card_sub_one_eq_one _ x.ne_zero, map_one]`. Take `⟨i, -, hi⟩` from `hprim.eq_pow_of_pow_eq_one hx`. Use `⟨μ ^ i, ?_, by rw [map_pow, hi]⟩` and prove the remaining obligations.

Rewrite using `[← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one, one_pow]`. Use `choose φ hφ1 hφ2 using hex`. Set `Φ : kˣ →* A` to `{ toFun := φ map_one' := by`. Use `eq_of_pow_eq_one_of_mk_eq P hnP (hφ1 1) (one_pow n) ?_` and prove the remaining obligations. Rewrite using `[hφ2, Units.val_one, map_one, one_pow, map_one]`.

Use the proof step `map_mul' := by`. Introduce `x y`. Use `eq_of_pow_eq_one_of_mk_eq P hnP (hφ1 _) ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_pow, hφ1, hφ1, one_mul]`. Rewrite using `[hφ2, map_mul, hφ2, hφ2, Units.val_mul, map_mul, mul_pow] }`.

Use `⟨MulChar.ofUnitHom Φ.toHomUnits, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Rewrite using `[MulChar.map_zero, map_zero, map_zero, zero_pow hm0]`.

Take `⟨u, rfl⟩` from `(isUnit_iff_ne_zero.mpr hx)`. Rewrite using `[MulChar.ofUnitHom_coe, MonoidHom.coe_toHomUnits]`. Conclude with `hφ2 u`. Use extensionality with `u`. Rewrite using `[MulChar.pow_apply_coe, MulChar.ofUnitHom_coe, MonoidHom.coe_toHomUnits, MulChar.one_apply_coe]`.

Conclude with `hφ1 u`.
-/
theorem exists_powResChar {A : Type*} [CommRing A] [IsDomain A] (P : Ideal A) [P.IsPrime]
    {k : Type*} [Field k] [Fintype k] (ι : k →+* A ⧸ P) {n : ℕ} (hn : n ∣ Fintype.card k - 1)
    {μ : A} (hμ : IsPrimitiveRoot μ n) :
    ∃ ρ : MulChar k A,
      (∀ x, Ideal.Quotient.mk P (ρ x) = ι x ^ ((Fintype.card k - 1) / n)) ∧ ρ ^ n = 1 := by
  classical
  have hnP : (n : A) ∉ P := natCast_not_mem_of_dvd P ι hn
  have hq1 : 0 < Fintype.card k - 1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hn
    omega
  have : NeZero n := ⟨hn0⟩
  set m := (Fintype.card k - 1) / n with hm
  have hmn : m * n = Fintype.card k - 1 := Nat.div_mul_cancel hn
  have hm0 : m ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hmn
    omega
  have hprim := isPrimitiveRoot_mk P hnP hμ
  have hex : ∀ x : kˣ, ∃ y : A, y ^ n = 1 ∧ Ideal.Quotient.mk P y = ι (x : k) ^ m := by
    intro x
    have hx : (ι (x : k) ^ m) ^ n = 1 := by
      rw [← pow_mul, hmn, ← map_pow, FiniteField.pow_card_sub_one_eq_one _ x.ne_zero, map_one]
    obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hx
    refine ⟨μ ^ i, ?_, by rw [map_pow, hi]⟩
    rw [← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one, one_pow]
  choose φ hφ1 hφ2 using hex
  let Φ : kˣ →* A :=
    { toFun := φ
      map_one' := by
        refine eq_of_pow_eq_one_of_mk_eq P hnP (hφ1 1) (one_pow n) ?_
        rw [hφ2, Units.val_one, map_one, one_pow, map_one]
      map_mul' := by
        intro x y
        refine eq_of_pow_eq_one_of_mk_eq P hnP (hφ1 _) ?_ ?_
        · rw [mul_pow, hφ1, hφ1, one_mul]
        · rw [hφ2, map_mul, hφ2, hφ2, Units.val_mul, map_mul, mul_pow] }
  refine ⟨MulChar.ofUnitHom Φ.toHomUnits, ?_, ?_⟩
  · intro x
    by_cases hx : x = 0
    · subst hx
      rw [MulChar.map_zero, map_zero, map_zero, zero_pow hm0]
    · obtain ⟨u, rfl⟩ := (isUnit_iff_ne_zero.mpr hx)
      rw [MulChar.ofUnitHom_coe, MonoidHom.coe_toHomUnits]
      exact hφ2 u
  · ext u
    rw [MulChar.pow_apply_coe, MulChar.ofUnitHom_coe, MonoidHom.coe_toHomUnits,
      MulChar.one_apply_coe]
    exact hφ1 u

end DiscreteGroups.sglob.Stick
