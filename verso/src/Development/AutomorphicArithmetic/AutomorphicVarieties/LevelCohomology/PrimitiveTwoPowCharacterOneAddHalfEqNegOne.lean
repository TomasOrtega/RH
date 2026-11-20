import Mathlib

/- English proof (translation)
Introduce `R _ _ n hn ξ hξ`. Take `⟨k, rfl⟩ : ∃ k, n = k + 2` from `⟨n - 2, by omega⟩`. Establish `hk : k + 2 - 1 = k + 1` using `by omega`. Rewrite using `[hk]`. Establish `h2 : (2 : ZMod (2 ^ (k + 2))) ^ (k + 2) = 0`.

Use `ZMod.natCast_self (2 ^ (k + 2))` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `huu : ((1 : ZMod (2 ^ (k + 2))) + 2 ^ (k + 1)) * (1 + 2 ^ (k + 1)) = 1`. Establish `e : ((1 : ZMod (2 ^ (k + 2))) + 2 ^ (k + 1)) * (1 + 2 ^ (k + 1)) = 1 + 2 ^ (k + 2) * (1 + 2 ^ k)` using `by ring`.

Rewrite using `[e, h2, zero_mul, add_zero]`. Establish `hsq : ξ (1 + 2 ^ (k + 1)) * ξ (1 + 2 ^ (k + 1)) = 1`. Rewrite using `[← map_mul, huu, map_one]`. Establish `hpm : ξ (1 + 2 ^ (k + 1)) = 1 ∨ ξ (1 + 2 ^ (k + 1)) = -1`. Establish `: (ξ (1 + 2 ^ (k + 1)) - 1) * (ξ (1 + 2 ^ (k + 1)) + 1) = 0`.

Take the linear combination `hsq`. Break down `mul_eq_zero.mp this with h | h` into its components or cases. Conclude with `Or.inl (sub_eq_zero.mp h)`. Conclude with `Or.inr (eq_neg_of_add_eq_zero_left h)`. Break down `hpm with h1 | h1` into its components or cases.

It suffices to derive a contradiction. Establish `hd : 2 ^ (k + 1) ∣ 2 ^ (k + 2)` using `pow_dvd_pow 2 (by omega)`. Establish `hft : ξ.FactorsThrough (2 ^ (k + 1))`. Rewrite using `[DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]`. Introduce `x hx`.

Establish `hx'` using `hx`. Rewrite `hx'` using `[MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ← ZMod.natCast_val, Units.val_one]`. Establish `hx'' : (((x : ZMod (2 ^ (k + 2))).val : ℕ) : ZMod (2 ^ (k + 1))) = ((1 : ℕ) : ZMod _)`. Rewrite using `[hx', Nat.cast_one]`. Rewrite `hx''` using `[ZMod.natCast_eq_natCast_iff]`.

Rewrite using `[MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]`. Establish `hv : (x : ZMod (2 ^ (k + 2))).val < 2 ^ (k + 2)` using `ZMod.val_lt _`. Establish `hM : 2 ≤ 2 ^ (k + 1)`. Combine the equalities or inequalities in the displayed calculation. Establish `hmod : (x : ZMod (2 ^ (k + 2))).val % 2 ^ (k + 1) = 1`.

Establish `h` using `hx''`. Unfold `Nat.ModEq at h`. Rewrite using `[h]`. Conclude with `Nat.mod_eq_of_lt (by omega)`. Establish `hq : (x : ZMod (2 ^ (k + 2))).val / 2 ^ (k + 1) < 2`.

Rewrite using `[Nat.div_lt_iff_lt_mul (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Establish `hdm` using `Nat.div_add_mod (x : ZMod (2 ^ (k + 2))).val (2 ^ (k + 1))`. Rewrite using `[← ZMod.natCast_zmod_val (x : ZMod (2 ^ (k + 2)))]`. Generalize the expression as in `hqd : (x : ZMod (2 ^ (k + 2))).val / 2 ^ (k + 1) = q at hq hdm`.

Break down `(by omega : q = 0 ∨ q = 1) with hq0 | hq1` into its components or cases. Rewrite `hdm` using `[hq0, mul_zero, zero_add, hmod]`. Rewrite using `[← hdm, Nat.cast_one, map_one]`. Rewrite `hdm` using `[hq1, mul_one, hmod]`. Rewrite using `[← hdm]`.

Use `push_cast`. Rewrite using `[add_comm ((2 : ZMod (2 ^ (k + 2))) ^ (k + 1)) 1]`. Conclude with `h1`. Establish `hle : ξ.conductor ≤ 2 ^ (k + 1)` using `Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff _).mpr hft)`. Establish `hlt : 2 ^ (k + 1) < 2 ^ (k + 2)` using `Nat.pow_lt_pow_right (by norm_num) (by omega)`.

Rewrite `hξ` using `[DirichletCharacter.isPrimitive_def]`. Use linear arithmetic over natural numbers and integers. Conclude with `h1`.
-/
theorem UpperTheory.primitive_two_pow_character_one_add_half_eq_neg_one :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ), 2 ≤ n → ∀ ξ : DirichletCharacter R (2 ^ n), ξ.IsPrimitive → ξ (1 + 2 ^ (n - 1)) = -1 := by
  intro R _ _ n hn ξ hξ
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk : k + 2 - 1 = k + 1 := by omega
  rw [hk]
  have h2 : (2 : ZMod (2 ^ (k + 2))) ^ (k + 2) = 0 := by
    have := ZMod.natCast_self (2 ^ (k + 2))
    push_cast at this
    exact this
  have huu : ((1 : ZMod (2 ^ (k + 2))) + 2 ^ (k + 1)) * (1 + 2 ^ (k + 1)) = 1 := by
    have e : ((1 : ZMod (2 ^ (k + 2))) + 2 ^ (k + 1)) * (1 + 2 ^ (k + 1))
        = 1 + 2 ^ (k + 2) * (1 + 2 ^ k) := by ring
    rw [e, h2, zero_mul, add_zero]
  have hsq : ξ (1 + 2 ^ (k + 1)) * ξ (1 + 2 ^ (k + 1)) = 1 := by
    rw [← map_mul, huu, map_one]
  have hpm : ξ (1 + 2 ^ (k + 1)) = 1 ∨ ξ (1 + 2 ^ (k + 1)) = -1 := by
    have : (ξ (1 + 2 ^ (k + 1)) - 1) * (ξ (1 + 2 ^ (k + 1)) + 1) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hpm with h1 | h1
  · exfalso
    have hd : 2 ^ (k + 1) ∣ 2 ^ (k + 2) := pow_dvd_pow 2 (by omega)
    have hft : ξ.FactorsThrough (2 ^ (k + 1)) := by
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
      intro x hx
      have hx' := hx
      rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ← ZMod.natCast_val,
        Units.val_one] at hx'
      have hx'' : (((x : ZMod (2 ^ (k + 2))).val : ℕ) : ZMod (2 ^ (k + 1))) = ((1 : ℕ) : ZMod _) := by
        rw [hx', Nat.cast_one]
      rw [ZMod.natCast_eq_natCast_iff] at hx''
      rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
      have hv : (x : ZMod (2 ^ (k + 2))).val < 2 ^ (k + 2) := ZMod.val_lt _
      have hM : 2 ≤ 2 ^ (k + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hmod : (x : ZMod (2 ^ (k + 2))).val % 2 ^ (k + 1) = 1 := by
        have h := hx''
        unfold Nat.ModEq at h
        rw [h]
        exact Nat.mod_eq_of_lt (by omega)
      have hq : (x : ZMod (2 ^ (k + 2))).val / 2 ^ (k + 1) < 2 := by
        rw [Nat.div_lt_iff_lt_mul (by positivity)]
        calc (x : ZMod (2 ^ (k + 2))).val < 2 ^ (k + 2) := hv
          _ = 2 * 2 ^ (k + 1) := by ring
      have hdm := Nat.div_add_mod (x : ZMod (2 ^ (k + 2))).val (2 ^ (k + 1))
      rw [← ZMod.natCast_zmod_val (x : ZMod (2 ^ (k + 2)))]
      generalize hqd : (x : ZMod (2 ^ (k + 2))).val / 2 ^ (k + 1) = q at hq hdm
      rcases (by omega : q = 0 ∨ q = 1) with hq0 | hq1
      · rw [hq0, mul_zero, zero_add, hmod] at hdm
        rw [← hdm, Nat.cast_one, map_one]
      · rw [hq1, mul_one, hmod] at hdm
        rw [← hdm]
        push_cast
        rw [add_comm ((2 : ZMod (2 ^ (k + 2))) ^ (k + 1)) 1]
        exact h1
    have hle : ξ.conductor ≤ 2 ^ (k + 1) :=
      Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff _).mpr hft)
    have hlt : 2 ^ (k + 1) < 2 ^ (k + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [DirichletCharacter.isPrimitive_def] at hξ
    omega
  · exact h1
