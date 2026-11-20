import Mathlib
import GroundTheory.GlobalFields.CyclotomicCharacters.ProfinitePadic

open scoped GroundTheory.LocalField.Abstract

namespace GroundTheory.Global

namespace Cyclotomic

section Discrete

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

def unitsLevel : ℕ := if ℓ = 2 then 3 else 1

def torsionExponent : ℕ := if ℓ = 2 then 2 else ℓ - 1

omit hℓ in
/- English proof (translation)
Apply the tactic sequence `unfold unitsLevel; split_ifs <;> norm_num`.
-/
theorem unitsLevel_ne_zero : unitsLevel ℓ ≠ 0 := by
  unfold unitsLevel; split_ifs <;> norm_num

/- English proof (translation)
Unfold `unitsLevel`. Use `split_ifs with h`. Substitute `h` using the available equality. Evaluate the numerical expressions. Use `hℓ.out.two_le` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem unitsLevel_add_two_le : unitsLevel ℓ + 2 ≤ ℓ * unitsLevel ℓ := by
  unfold unitsLevel
  split_ifs with h
  · subst h; norm_num
  · have := hℓ.out.two_le
    omega

/- English proof (translation)
Unfold `torsionExponent`. Use `split_ifs`. Evaluate the numerical expressions. Use `hℓ.out.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem torsionExponent_pos : 0 < torsionExponent ℓ := by
  unfold torsionExponent
  split_ifs
  · norm_num
  · have := hℓ.out.two_le
    omega

/- English proof (translation)
Distinguish the cases in `h : ℓ = 2`. Substitute `h` using the available equality. Establish `key : ∀ y : ZMod 8, (∃ z : ZMod 8, y * z = 1) → y ^ 2 = 1` using `by decide`. Establish `h8 : (2 : ℕ) ^ unitsLevel 2 = 8` using `by simp [unitsLevel]`. Rewrite using `[torsionExponent, if_pos rfl]`.

Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[Units.val_pow_eq_pow_val, Units.val_one]`. Use `revert x`. Rewrite using `[h8]`. Introduce `x`.

Conclude with `key _ ⟨_, x.mul_inv⟩`. Establish `: NeZero ℓ` using `⟨hℓ.out.ne_zero⟩`. Establish `hc : Fintype.card (ZMod (ℓ ^ unitsLevel ℓ))ˣ = ℓ - 1`. Rewrite using `[ZMod.card_units_eq_totient, unitsLevel, if_neg h, pow_one, Nat.totient_prime hℓ.out]`. Rewrite using `[torsionExponent, if_neg h, ← hc, pow_card_eq_one]`.
-/
theorem pow_torsionExponent (x : (ZMod (ℓ ^ unitsLevel ℓ))ˣ) : x ^ torsionExponent ℓ = 1 := by
  by_cases h : ℓ = 2
  · subst h
    have key : ∀ y : ZMod 8, (∃ z : ZMod 8, y * z = 1) → y ^ 2 = 1 := by decide
    have h8 : (2 : ℕ) ^ unitsLevel 2 = 8 := by simp [unitsLevel]
    rw [torsionExponent, if_pos rfl]
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    revert x
    rw [h8]
    intro x
    exact key _ ⟨_, x.mul_inv⟩
  · have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
    have hc : Fintype.card (ZMod (ℓ ^ unitsLevel ℓ))ˣ = ℓ - 1 := by
      rw [ZMod.card_units_eq_totient, unitsLevel, if_neg h, pow_one, Nat.totient_prime hℓ.out]
    rw [torsionExponent, if_neg h, ← hc, pow_card_eq_one]

def unitsKer (n : ℕ) : Subgroup (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ :=
  (ZMod.unitsMap (pow_dvd_pow ℓ (Nat.le_add_left (unitsLevel ℓ) n))).ker

/- English proof (translation)
Establish `: NeZero ℓ` using `⟨hℓ.out.ne_zero⟩`. Establish `h1` using `Subgroup.card_mul_index (unitsKer ℓ n)`. Rewrite using `[unitsKer, Subgroup.index_ker, MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective _), Subgroup.card_top, Nat.card_eq_fintype_card (α := (ZMod (ℓ ^ unitsLevel ℓ))ˣ), Nat.card_eq_fintype_card (α := (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ), ZMod.card_units_eq_totient, ZMod.card_units_eq_to …`. Use `unitsLevel_ne_zero ℓ` as an intermediate fact. Use the proof step `omega)] at h1`.

Establish `hr : n + unitsLevel ℓ - 1 = n + (unitsLevel ℓ - 1)`. Use `unitsLevel_ne_zero ℓ` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hpos : 0 < ℓ ^ (unitsLevel ℓ - 1) * (ℓ - 1)` using `Nat.mul_pos (pow_pos hℓ.out.pos _) (by have := hℓ.out.two_le; omega)`. Establish `h2 : Nat.card (unitsKer ℓ n) * (ℓ ^ (unitsLevel ℓ - 1) * (ℓ - 1)) = ℓ ^ n * (ℓ ^ (unitsLevel ℓ - 1) * (ℓ - 1))`.

Rewrite using `[← mul_assoc (ℓ ^ n), ← pow_add, ← hr]`. Conclude with `h1`. Conclude with `Nat.eq_of_mul_eq_mul_right hpos h2`.
-/
theorem card_unitsKer (n : ℕ) : Nat.card (unitsKer ℓ n) = ℓ ^ n := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have h1 := Subgroup.card_mul_index (unitsKer ℓ n)
  rw [unitsKer, Subgroup.index_ker, MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective _),
    Subgroup.card_top, Nat.card_eq_fintype_card (α := (ZMod (ℓ ^ unitsLevel ℓ))ˣ),
    Nat.card_eq_fintype_card (α := (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ), ZMod.card_units_eq_totient,
    ZMod.card_units_eq_totient, Nat.totient_prime_pow hℓ.out (Nat.pos_of_ne_zero
      (unitsLevel_ne_zero ℓ)), Nat.totient_prime_pow hℓ.out (by
        have := unitsLevel_ne_zero ℓ; omega)] at h1
  have hr : n + unitsLevel ℓ - 1 = n + (unitsLevel ℓ - 1) := by
    have := unitsLevel_ne_zero ℓ; omega
  have hpos : 0 < ℓ ^ (unitsLevel ℓ - 1) * (ℓ - 1) :=
    Nat.mul_pos (pow_pos hℓ.out.pos _) (by have := hℓ.out.two_le; omega)
  have h2 : Nat.card (unitsKer ℓ n) * (ℓ ^ (unitsLevel ℓ - 1) * (ℓ - 1)) =
      ℓ ^ n * (ℓ ^ (unitsLevel ℓ - 1) * (ℓ - 1)) := by
    rw [← mul_assoc (ℓ ^ n), ← pow_add, ← hr]
    exact h1
  exact Nat.eq_of_mul_eq_mul_right hpos h2

/- English proof (translation)
Use `Nat.Coprime.pow_right _ ?_` and prove the remaining obligations. Rewrite using `[Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hℓ.out]`. Introduce `h`. Rewrite `h` using `[add_comm]`. Conclude with `hℓ.out.not_dvd_one ((Nat.dvd_add_right (dvd_pow_self ℓ (unitsLevel_ne_zero ℓ))).1 h)`.
-/
theorem coprime_one_add_pow (k : ℕ) : Nat.Coprime (1 + ℓ ^ unitsLevel ℓ) (ℓ ^ k) := by
  refine Nat.Coprime.pow_right _ ?_
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hℓ.out]
  intro h
  rw [add_comm] at h
  exact hℓ.out.not_dvd_one
    ((Nat.dvd_add_right (dvd_pow_self ℓ (unitsLevel_ne_zero ℓ))).1 h)

def genUnit (n : ℕ) : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ :=
  ZMod.unitOfCoprime (1 + ℓ ^ unitsLevel ℓ) (coprime_one_add_pow ℓ _)

/- English proof (translation)
Simplify using `[genUnit]`.
-/
@[simp] theorem coe_genUnit (n : ℕ) :
    (genUnit ℓ n : ZMod (ℓ ^ (n + unitsLevel ℓ))) = 1 + (ℓ : ZMod _) ^ unitsLevel ℓ := by
  simp [genUnit]

/- English proof (translation)
Rewrite using `[← orderOf_units, coe_genUnit]`. Use `ZMod.orderOf_one_add_mul_prime_pow hℓ.out (unitsLevel ℓ) (unitsLevel_ne_zero ℓ) (unitsLevel_add_two_le ℓ) 1 (by norm_cast; exact hℓ.out.not_dvd_one) n` as an intermediate fact. Simplify using `using this`.
-/
theorem orderOf_genUnit (n : ℕ) : orderOf (genUnit ℓ n) = ℓ ^ n := by
  rw [← orderOf_units, coe_genUnit]
  have := ZMod.orderOf_one_add_mul_prime_pow hℓ.out (unitsLevel ℓ) (unitsLevel_ne_zero ℓ)
    (unitsLevel_add_two_le ℓ) 1 (by norm_cast; exact hℓ.out.not_dvd_one) n
  simpa using this

/- English proof (translation)
Use `pow_orderOf_eq_one (genUnit ℓ n)` as an intermediate fact. Rewrite `this` using `[orderOf_genUnit]`. Then use the resulting hypothesis.
-/
theorem genUnit_pow_eq_one (n : ℕ) : genUnit ℓ n ^ (ℓ ^ n) = 1 := by
  have := pow_orderOf_eq_one (genUnit ℓ n)
  rwa [orderOf_genUnit] at this

/- English proof (translation)
Rewrite using `[unitsKer, MonoidHom.mem_ker]`. Use `Units.ext ?_` and prove the remaining obligations. Simplify using `only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, coe_genUnit, map_add, map_one, map_pow, map_natCast, Units.val_one]`. Rewrite using `[← Nat.cast_pow, ZMod.natCast_self, add_zero]`.
-/
theorem genUnit_mem_unitsKer (n : ℕ) : genUnit ℓ n ∈ unitsKer ℓ n := by
  rw [unitsKer, MonoidHom.mem_ker]
  refine Units.ext ?_
  simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, coe_genUnit, map_add, map_one,
    map_pow, map_natCast, Units.val_one]
  rw [← Nat.cast_pow, ZMod.natCast_self, add_zero]

/- English proof (translation)
The claim follows from `Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 (genUnit_mem_unitsKer ℓ n)) (by rw [card_unitsKer, Nat.card_zpowers, orderOf_genUnit])`.
-/
theorem zpowers_genUnit (n : ℕ) : Subgroup.zpowers (genUnit ℓ n) = unitsKer ℓ n :=
  Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 (genUnit_mem_unitsKer ℓ n))
    (by rw [card_unitsKer, Nat.card_zpowers, orderOf_genUnit])

/- English proof (translation)
Rewrite using `[pow_eq_pow_iff_modEq, orderOf_genUnit]`. Conclude with `h`.
-/
theorem genUnit_pow_val_eq (n : ℕ) {a b : ℕ} (h : a ≡ b [MOD ℓ ^ n]) :
    genUnit ℓ n ^ a = genUnit ℓ n ^ b := by
  rw [pow_eq_pow_iff_modEq, orderOf_genUnit]
  exact h

def expHom (n : ℕ) : Multiplicative (ZMod (ℓ ^ n)) →* (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ where
  toFun a := genUnit ℓ n ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
    rw [← pow_add, toAdd_mul]
    exact genUnit_pow_val_eq ℓ n (by rw [ZMod.val_add]; exact Nat.mod_modEq _ _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem expHom_apply (n : ℕ) (a : Multiplicative (ZMod (ℓ ^ n))) :
    expHom ℓ n a = genUnit ℓ n ^ (Multiplicative.toAdd a).val :=
  rfl

/- English proof (translation)
Establish `: NeZero ℓ` using `⟨hℓ.out.ne_zero⟩`. Use `(injective_iff_map_eq_one _).2 fun a ha => ?_` and prove the remaining obligations. Rewrite `ha` using `[expHom_apply]`. Establish `h1 : ℓ ^ n ∣ (Multiplicative.toAdd a).val`. Use `orderOf_dvd_of_pow_eq_one ha` as an intermediate fact.

Rewrite `this` using `[orderOf_genUnit]`. Then use the resulting hypothesis. Establish `h2` using `Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _)`. Rewrite `h2` using `[ZMod.val_eq_zero]`. Conclude with `h2`.
-/
theorem expHom_injective (n : ℕ) : Function.Injective (expHom ℓ n) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  refine (injective_iff_map_eq_one _).2 fun a ha => ?_
  rw [expHom_apply] at ha
  have h1 : ℓ ^ n ∣ (Multiplicative.toAdd a).val := by
    have := orderOf_dvd_of_pow_eq_one ha
    rwa [orderOf_genUnit] at this
  have h2 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _)
  rw [ZMod.val_eq_zero] at h2
  exact h2

/- English proof (translation)
Apply `Subgroup.eq_of_le_of_card_ge` to reduce the goal to its premises. Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[← zpowers_genUnit]`. Conclude with `Subgroup.npow_mem_zpowers _ _`. Rewrite using `[card_unitsKer, ← Nat.card_congr (MonoidHom.ofInjective (expHom_injective ℓ n)).toEquiv]`.

Conclude with `(Nat.card_zmod _).ge`.
-/
theorem range_expHom (n : ℕ) : (expHom ℓ n).range = unitsKer ℓ n := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨a, rfl⟩
    rw [← zpowers_genUnit]
    exact Subgroup.npow_mem_zpowers _ _
  · rw [card_unitsKer, ← Nat.card_congr (MonoidHom.ofInjective (expHom_injective ℓ n)).toEquiv]
    exact (Nat.card_zmod _).ge

noncomputable def expEquiv (n : ℕ) : Multiplicative (ZMod (ℓ ^ n)) ≃* unitsKer ℓ n :=
  (MonoidHom.ofInjective (expHom_injective ℓ n)).trans (MulEquiv.subgroupCongr (range_expHom ℓ n))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_expEquiv (n : ℕ) (a : Multiplicative (ZMod (ℓ ^ n))) :
    (expEquiv ℓ n a : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ) = expHom ℓ n a :=
  rfl

def powKer (n : ℕ) : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ →* unitsKer ℓ n :=
  (powMonoidHom (torsionExponent ℓ)).codRestrict (unitsKer ℓ n) fun x => by
    rw [unitsKer, MonoidHom.mem_ker, powMonoidHom_apply, map_pow, pow_torsionExponent]

noncomputable def logMod (n : ℕ) : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ →* Multiplicative (ZMod (ℓ ^ n)) :=
  (expEquiv ℓ n).symm.toMonoidHom.comp (powKer ℓ n)

/- English proof (translation)
Use `congrArg Subtype.val ((expEquiv ℓ n).apply_symm_apply (powKer ℓ n x))` as an intermediate fact. Rewrite `this` using `[coe_expEquiv]`. Conclude with `this`.
-/
theorem expHom_logMod (n : ℕ) (x : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ) :
    expHom ℓ n (logMod ℓ n x) = x ^ torsionExponent ℓ := by
  have := congrArg Subtype.val ((expEquiv ℓ n).apply_symm_apply (powKer ℓ n x))
  rw [coe_expEquiv] at this
  exact this

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => h ▸ expHom_logMod ℓ n x, fun h => expHom_injective ℓ n (by rw [expHom_logMod, h])⟩`.
-/
theorem logMod_eq_iff (n : ℕ) (x : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ)
    (a : Multiplicative (ZMod (ℓ ^ n))) :
    logMod ℓ n x = a ↔ expHom ℓ n a = x ^ torsionExponent ℓ :=
  ⟨fun h => h ▸ expHom_logMod ℓ n x,
    fun h => expHom_injective ℓ n (by rw [expHom_logMod, h])⟩

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Simplify using `only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, coe_genUnit, map_add, map_one, map_pow, map_natCast]`.
-/
theorem unitsMap_genUnit {m n : ℕ} (h : m ≤ n) :
    ZMod.unitsMap (pow_dvd_pow ℓ (by omega : m + unitsLevel ℓ ≤ n + unitsLevel ℓ)) (genUnit ℓ n) =
      genUnit ℓ m := by
  refine Units.ext ?_
  simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, coe_genUnit, map_add, map_one,
    map_pow, map_natCast]

/- English proof (translation)
Establish `: NeZero ℓ` using `⟨hℓ.out.ne_zero⟩`. Use `set a := Multiplicative.toAdd (logMod ℓ n x) with ha`. Establish `key : logMod ℓ m (ZMod.unitsMap (pow_dvd_pow ℓ (by omega : m + unitsLevel ℓ ≤ n + unitsLevel ℓ)) x) = Multiplicative.ofAdd (ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) a)`. Rewrite using `[logMod_eq_iff, expHom_apply, toAdd_ofAdd, ← map_pow, ← expHom_logMod ℓ n x, expHom_apply, map_pow, unitsMap_genUnit ℓ h, ← ha]`. Use `genUnit_pow_val_eq ℓ m ?_` and prove the remaining obligations.

Rewrite using `[ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]`. Conclude with `Nat.mod_modEq _ _`. Rewrite using `[key, toAdd_ofAdd]`.
-/
theorem castHom_logMod {m n : ℕ} (h : m ≤ n) (x : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ) :
    ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (Multiplicative.toAdd (logMod ℓ n x)) =
      Multiplicative.toAdd (logMod ℓ m
        (ZMod.unitsMap (pow_dvd_pow ℓ (by omega : m + unitsLevel ℓ ≤ n + unitsLevel ℓ)) x)) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  set a := Multiplicative.toAdd (logMod ℓ n x) with ha
  have key : logMod ℓ m
      (ZMod.unitsMap (pow_dvd_pow ℓ (by omega : m + unitsLevel ℓ ≤ n + unitsLevel ℓ)) x) =
        Multiplicative.ofAdd (ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) a) := by
    rw [logMod_eq_iff, expHom_apply, toAdd_ofAdd, ← map_pow, ← expHom_logMod ℓ n x, expHom_apply,
      map_pow, unitsMap_genUnit ℓ h, ← ha]
    refine genUnit_pow_val_eq ℓ m ?_
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
    exact Nat.mod_modEq _ _
  rw [key, toAdd_ofAdd]

end Discrete

section Limit

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

def compatibleFamilies : Subring (∀ n : ℕ, ZMod (ℓ ^ n)) :=
  ⨅ (m : ℕ) (n : ℕ) (h : m ≤ n), RingHom.eqLocus
    ((ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m))).comp
      (Pi.evalRingHom (fun k => ZMod (ℓ ^ k)) n)) (Pi.evalRingHom (fun k => ZMod (ℓ ^ k)) m)

omit hℓ in
/- English proof (translation)
Simplify using `[compatibleFamilies, Subring.mem_iInf, RingHom.mem_eqLocus]`.
-/
theorem mem_compatibleFamilies {x : ∀ n : ℕ, ZMod (ℓ ^ n)} :
    x ∈ compatibleFamilies ℓ ↔
      ∀ (m n : ℕ) (h : m ≤ n), ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (x n) = x m := by
  simp [compatibleFamilies, Subring.mem_iInf, RingHom.mem_eqLocus]

noncomputable def limFamilies : compatibleFamilies ℓ →+* ℤ_[ℓ] :=
  PadicInt.lift (f := fun n => (Pi.evalRingHom (fun k => ZMod (ℓ ^ k)) n).comp
    (compatibleFamilies ℓ).subtype) fun m n h => by
      ext x
      exact (mem_compatibleFamilies ℓ).1 x.2 m n h

/- English proof (translation)
The claim follows from `RingHom.congr_fun (PadicInt.lift_spec _ n) x`.
-/
theorem toZModPow_limFamilies (x : compatibleFamilies ℓ) (n : ℕ) :
    PadicInt.toZModPow n (limFamilies ℓ x) = (x : ∀ n : ℕ, ZMod (ℓ ^ n)) n :=
  RingHom.congr_fun (PadicInt.lift_spec _ n) x

noncomputable def redUnits (k : ℕ) : ℤ_[ℓ]ˣ →* (ZMod (ℓ ^ k))ˣ :=
  Units.map (PadicInt.toZModPow k).toMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_redUnits (k : ℕ) (u : ℤ_[ℓ]ˣ) :
    (redUnits ℓ k u : ZMod (ℓ ^ k)) = PadicInt.toZModPow k (u : ℤ_[ℓ]) :=
  rfl

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Simplify using `only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, coe_redUnits, ZMod.castHom_apply]`. Conclude with `PadicInt.cast_toZModPow _ _ h _`.
-/
theorem unitsMap_redUnits {k k' : ℕ} (h : k ≤ k') (u : ℤ_[ℓ]ˣ) :
    ZMod.unitsMap (pow_dvd_pow ℓ h) (redUnits ℓ k' u) = redUnits ℓ k u := by
  refine Units.ext ?_
  simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, coe_redUnits,
    ZMod.castHom_apply]
  exact PadicInt.cast_toZModPow _ _ h _

/- English proof (translation)
Rewrite using `[mem_compatibleFamilies]`. Introduce `m n h`. Rewrite using `[castHom_logMod ℓ h, unitsMap_redUnits ℓ (k := m + unitsLevel ℓ) (k' := n + unitsLevel ℓ) (by omega)]`.
-/
theorem logFamily_mem (u : ℤ_[ℓ]ˣ) :
    (fun n => Multiplicative.toAdd (logMod ℓ n (redUnits ℓ (n + unitsLevel ℓ) u))) ∈
      compatibleFamilies ℓ := by
  rw [mem_compatibleFamilies]
  intro m n h
  rw [castHom_logMod ℓ h,
    unitsMap_redUnits ℓ (k := m + unitsLevel ℓ) (k' := n + unitsLevel ℓ) (by omega)]

noncomputable def padicUnitsLog : ℤ_[ℓ]ˣ →* Multiplicative ℤ_[ℓ] where
  toFun u := Multiplicative.ofAdd (limFamilies ℓ ⟨_, logFamily_mem ℓ u⟩)
  map_one' := by
    refine congrArg Multiplicative.ofAdd (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [toZModPow_limFamilies, map_zero]
    simp
  map_mul' u v := by
    rw [← ofAdd_add]
    refine congrArg Multiplicative.ofAdd (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [map_add, toZModPow_limFamilies, toZModPow_limFamilies, toZModPow_limFamilies]
    simp

/- English proof (translation)
The claim follows from `toZModPow_limFamilies ℓ _ n`.
-/
theorem toZModPow_padicUnitsLog (u : ℤ_[ℓ]ˣ) (n : ℕ) :
    PadicInt.toZModPow n (Multiplicative.toAdd (padicUnitsLog ℓ u)) =
      Multiplicative.toAdd (logMod ℓ n (redUnits ℓ (n + unitsLevel ℓ) u)) :=
  toZModPow_limFamilies ℓ _ n

/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Use `⟨(continuous_toZModPow k).comp Units.continuous_val, ?_⟩` and prove the remaining obligations. Establish `: (fun u : ℤ_[ℓ]ˣ => ((redUnits ℓ k u)⁻¹ : (ZMod (ℓ ^ k))ˣ).val) = fun u => PadicInt.toZModPow k ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ])`. Use function extensionality and compare the values at `u`. Rewrite using `[← map_inv]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `(continuous_toZModPow k).comp (Units.continuous_val.comp continuous_inv)`.
-/
theorem continuous_redUnits (k : ℕ) : Continuous (redUnits ℓ k) := by
  rw [Units.continuous_iff]
  refine ⟨(continuous_toZModPow k).comp Units.continuous_val, ?_⟩
  have : (fun u : ℤ_[ℓ]ˣ => ((redUnits ℓ k u)⁻¹ : (ZMod (ℓ ^ k))ˣ).val) =
      fun u => PadicInt.toZModPow k ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by
    funext u; rw [← map_inv]; rfl
  rw [this]
  exact (continuous_toZModPow k).comp (Units.continuous_val.comp continuous_inv)

/- English proof (translation)
Establish `hc : Continuous fun u : ℤ_[ℓ]ˣ => Multiplicative.toAdd (padicUnitsLog ℓ u)` using `continuous_of_continuous_toZModPow fun n => ((continuous_of_discreteTopology (f := fun v : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ => Multiplicative.toAdd (logMod ℓ n v))).comp (continuous_redUnits ℓ _)).congr fun u => (toZModPow_padicUnitsLog ℓ u n).symm`. Conclude with `continuous_ofAdd.comp hc`.
-/
theorem continuous_padicUnitsLog : Continuous (padicUnitsLog ℓ) := by
  have hc : Continuous fun u : ℤ_[ℓ]ˣ => Multiplicative.toAdd (padicUnitsLog ℓ u) :=
    continuous_of_continuous_toZModPow fun n =>
      ((continuous_of_discreteTopology (f := fun v : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ =>
        Multiplicative.toAdd (logMod ℓ n v))).comp (continuous_redUnits ℓ _)).congr fun u =>
          (toZModPow_padicUnitsLog ℓ u n).symm
  exact continuous_ofAdd.comp hc

def genNat : ℕ := if ℓ = 2 then 3 else ℓ + 1

def genLog : ℕ := if ℓ = 2 then 1 else ℓ - 1

/- English proof (translation)
Unfold `genNat torsionExponent unitsLevel genLog`. Use `split_ifs with h`. Substitute `h` using the available equality. Evaluate the numerical expressions. Rewrite using `[pow_one, add_comm]`.
-/
theorem genNat_pow : genNat ℓ ^ torsionExponent ℓ = (1 + ℓ ^ unitsLevel ℓ) ^ genLog ℓ := by
  unfold genNat torsionExponent unitsLevel genLog
  split_ifs with h
  · subst h; norm_num
  · rw [pow_one, add_comm]

/- English proof (translation)
Rewrite using `[Nat.Prime.coprime_iff_not_dvd hℓ.out]`. Unfold `genNat`. Use `split_ifs with h`. Substitute `h` using the available equality. Evaluate the numerical expressions.

Introduce `hd`. Conclude with `hℓ.out.not_dvd_one ((Nat.dvd_add_right (dvd_refl ℓ)).1 hd)`.
-/
theorem coprime_genNat : Nat.Coprime ℓ (genNat ℓ) := by
  rw [Nat.Prime.coprime_iff_not_dvd hℓ.out]
  unfold genNat
  split_ifs with h
  · subst h; norm_num
  · intro hd
    exact hℓ.out.not_dvd_one ((Nat.dvd_add_right (dvd_refl ℓ)).1 hd)

/- English proof (translation)
Rewrite using `[Nat.Prime.coprime_iff_not_dvd hℓ.out]`. Unfold `genLog`. Use `split_ifs with h`. Substitute `h` using the available equality. Evaluate the numerical expressions.

Use `hℓ.out.two_le` as an intermediate fact. Conclude with `Nat.not_dvd_of_pos_of_lt (by omega) (by omega)`.
-/
theorem coprime_genLog : Nat.Coprime ℓ (genLog ℓ) := by
  rw [Nat.Prime.coprime_iff_not_dvd hℓ.out]
  unfold genLog
  split_ifs with h
  · subst h; norm_num
  · have := hℓ.out.two_le
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)

/- English proof (translation)
The claim follows from `PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hk)`.
-/
theorem isUnit_natCast_of_coprime {k : ℕ} (hk : Nat.Coprime ℓ k) : IsUnit (k : ℤ_[ℓ]) :=
  PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hk)

noncomputable def genPadicUnit : ℤ_[ℓ]ˣ := (isUnit_natCast_of_coprime ℓ (coprime_genNat ℓ)).unit

/- English proof (translation)
Use `PadicInt.ext_of_toZModPow.mp fun n => ?_` and prove the remaining obligations. Rewrite using `[toZModPow_padicUnitsLog, map_natCast]`. Establish `: logMod ℓ n (redUnits ℓ (n + unitsLevel ℓ) (genPadicUnit ℓ)) = Multiplicative.ofAdd ((genLog ℓ : ℕ) : ZMod (ℓ ^ n))`. Rewrite using `[logMod_eq_iff, expHom_apply, toAdd_ofAdd, pow_val_natCast (genUnit_pow_eq_one ℓ n)]`. Use `Units.ext ?_` and prove the remaining obligations.

Simplify using `only [Units.val_pow_eq_pow_val, coe_genUnit, coe_redUnits, genPadicUnit, IsUnit.unit_spec, map_natCast]`. Rewrite using `[← Nat.cast_pow (genNat ℓ), genNat_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, toAdd_ofAdd]`.
-/
theorem padicUnitsLog_genPadicUnit :
    Multiplicative.toAdd (padicUnitsLog ℓ (genPadicUnit ℓ)) = (genLog ℓ : ℤ_[ℓ]) := by
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [toZModPow_padicUnitsLog, map_natCast]
  have : logMod ℓ n (redUnits ℓ (n + unitsLevel ℓ) (genPadicUnit ℓ)) =
      Multiplicative.ofAdd ((genLog ℓ : ℕ) : ZMod (ℓ ^ n)) := by
    rw [logMod_eq_iff, expHom_apply, toAdd_ofAdd, pow_val_natCast (genUnit_pow_eq_one ℓ n)]
    refine Units.ext ?_
    simp only [Units.val_pow_eq_pow_val, coe_genUnit, coe_redUnits, genPadicUnit,
      IsUnit.unit_spec, map_natCast]
    rw [← Nat.cast_pow (genNat ℓ), genNat_pow]
    push_cast
    ring
  rw [this, toAdd_ofAdd]

/- English proof (translation)
Establish `hc : Continuous fun u : ℤ_[ℓ]ˣ => Multiplicative.toAdd (padicUnitsLog ℓ u)` using `continuous_toAdd.comp (continuous_padicUnitsLog ℓ)`. Use `set s : ℤ_[ℓ] := (genLog ℓ : ℤ_[ℓ])`. Establish `hs : IsUnit s` using `isUnit_natCast_of_coprime ℓ (coprime_genLog ℓ)`. Use `set R : Set ℤ_[ℓ] := Set.range fun u : ℤ_[ℓ]ˣ => Multiplicative.toAdd (padicUnitsLog ℓ u)`. Establish `hR : IsClosed R` using `(isCompact_range hc).isClosed`.

Establish `hmem : ∀ t : ℤ_[ℓ], s * t ∈ R` using `fun t => PadicInt.denseRange_natCast.induction_on t (hR.preimage (continuous_const.mul continuous_id)) fun k => ⟨genPadicUnit ℓ ^ k, by show Multiplicative.toAdd (padicUnitsLog ℓ (genPadicUnit ℓ ^ k)) = s * k`. Rewrite using `[map_pow, toAdd_pow, padicUnitsLog_genPadicUnit, nsmul_eq_mul, mul_comm]⟩`. Introduce `y`. Take `⟨u, hu⟩` from `hmem (↑hs.unit⁻¹ * Multiplicative.toAdd y)`. Establish `hu : Multiplicative.toAdd (padicUnitsLog ℓ u) = s * (↑hs.unit⁻¹ * Multiplicative.toAdd y)` using `hu`.

Use `⟨u, ?_⟩` and prove the remaining obligations. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Rewrite using `[hu, ← mul_assoc, IsUnit.mul_val_inv, one_mul]`.
-/
theorem padicUnitsLog_surjective : Function.Surjective (padicUnitsLog ℓ) := by
  have hc : Continuous fun u : ℤ_[ℓ]ˣ => Multiplicative.toAdd (padicUnitsLog ℓ u) :=
    continuous_toAdd.comp (continuous_padicUnitsLog ℓ)
  set s : ℤ_[ℓ] := (genLog ℓ : ℤ_[ℓ])
  have hs : IsUnit s := isUnit_natCast_of_coprime ℓ (coprime_genLog ℓ)
  set R : Set ℤ_[ℓ] := Set.range fun u : ℤ_[ℓ]ˣ => Multiplicative.toAdd (padicUnitsLog ℓ u)
  have hR : IsClosed R := (isCompact_range hc).isClosed
  have hmem : ∀ t : ℤ_[ℓ], s * t ∈ R := fun t =>
    PadicInt.denseRange_natCast.induction_on t
      (hR.preimage (continuous_const.mul continuous_id)) fun k =>
        ⟨genPadicUnit ℓ ^ k, by
          show Multiplicative.toAdd (padicUnitsLog ℓ (genPadicUnit ℓ ^ k)) = s * k
          rw [map_pow, toAdd_pow, padicUnitsLog_genPadicUnit, nsmul_eq_mul, mul_comm]⟩
  intro y
  obtain ⟨u, hu⟩ := hmem (↑hs.unit⁻¹ * Multiplicative.toAdd y)
  have hu : Multiplicative.toAdd (padicUnitsLog ℓ u) = s * (↑hs.unit⁻¹ * Multiplicative.toAdd y) :=
    hu
  refine ⟨u, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [hu, ← mul_assoc, IsUnit.mul_val_inv, one_mul]

/- English proof (translation)
Establish `h1` using `congrArg (fun v => Multiplicative.toAdd (padicUnitsLog ℓ v)) h`. Simplify using `only [map_pow, toAdd_pow, map_one, toAdd_one, nsmul_eq_mul] at h1`. Break down `mul_eq_zero.1 h1 with h2 | h2` into its components or cases. Conclude with `absurd h2 (Nat.cast_ne_zero.2 hk.ne')`. Conclude with `congrArg Multiplicative.ofAdd h2`.
-/
theorem padicUnitsLog_eq_one_of_pow_eq_one {u : ℤ_[ℓ]ˣ} {k : ℕ} (hk : 0 < k) (h : u ^ k = 1) :
    padicUnitsLog ℓ u = 1 := by
  have h1 := congrArg (fun v => Multiplicative.toAdd (padicUnitsLog ℓ v)) h
  simp only [map_pow, toAdd_pow, map_one, toAdd_one, nsmul_eq_mul] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact absurd h2 (Nat.cast_ne_zero.2 hk.ne')
  · exact congrArg Multiplicative.ofAdd h2

/- English proof (translation)
Use `⟨fun h => ?_, padicUnitsLog_eq_one_of_pow_eq_one ℓ (torsionExponent_pos ℓ)⟩` and prove the remaining obligations. Establish `hk : ∀ k, PadicInt.toZModPow (k + unitsLevel ℓ) ((u ^ torsionExponent ℓ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = 1` using `fun k => by`. Establish `h1` using `toZModPow_padicUnitsLog ℓ u k`. Rewrite `h1` using `[h, toAdd_one, map_zero]`. Establish `h2 : logMod ℓ k (redUnits ℓ (k + unitsLevel ℓ) u) = 1` using `congrArg Multiplicative.ofAdd h1.symm`.

Rewrite `h2` using `[logMod_eq_iff, map_one]`. Establish `h3` using `congrArg Units.val h2`. Rewrite `h3` using `[Units.val_one, Units.val_pow_eq_pow_val, coe_redUnits, ← map_pow]`. Rewrite using `[Units.val_pow_eq_pow_val]`. Conclude with `h3.symm`.

Use `Units.ext (PadicInt.ext_of_toZModPow.mp fun k => ?_)` and prove the remaining obligations. Rewrite using `[← PadicInt.zmod_cast_comp_toZModPow k (k + unitsLevel ℓ) (Nat.le_add_right _ _), RingHom.comp_apply, RingHom.comp_apply, hk]`. Simplify using the standard rewrite rules.
-/
theorem padicUnitsLog_eq_one_iff (u : ℤ_[ℓ]ˣ) :
    padicUnitsLog ℓ u = 1 ↔ u ^ torsionExponent ℓ = 1 := by
  refine ⟨fun h => ?_, padicUnitsLog_eq_one_of_pow_eq_one ℓ (torsionExponent_pos ℓ)⟩
  have hk : ∀ k, PadicInt.toZModPow (k + unitsLevel ℓ) ((u ^ torsionExponent ℓ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) =
      1 := fun k => by
    have h1 := toZModPow_padicUnitsLog ℓ u k
    rw [h, toAdd_one, map_zero] at h1
    have h2 : logMod ℓ k (redUnits ℓ (k + unitsLevel ℓ) u) = 1 :=
      congrArg Multiplicative.ofAdd h1.symm
    rw [logMod_eq_iff, map_one] at h2
    have h3 := congrArg Units.val h2
    rw [Units.val_one, Units.val_pow_eq_pow_val, coe_redUnits, ← map_pow] at h3
    rw [Units.val_pow_eq_pow_val]
    exact h3.symm
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun k => ?_)
  rw [← PadicInt.zmod_cast_comp_toZModPow k (k + unitsLevel ℓ) (Nat.le_add_right _ _),
    RingHom.comp_apply, RingHom.comp_apply, hk]
  simp

/- English proof (translation)
Use extensionality with `u`. Rewrite using `[MonoidHom.mem_ker, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨_, torsionExponent_pos ℓ, (padicUnitsLog_eq_one_iff ℓ u).1 h⟩`.

Introduce and unpack `⟨k, hk, h⟩`. Conclude with `padicUnitsLog_eq_one_of_pow_eq_one ℓ hk h`.
-/
theorem ker_padicUnitsLog : (padicUnitsLog ℓ).ker = CommGroup.torsion ℤ_[ℓ]ˣ := by
  ext u
  rw [MonoidHom.mem_ker, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  constructor
  · intro h
    exact ⟨_, torsionExponent_pos ℓ, (padicUnitsLog_eq_one_iff ℓ u).1 h⟩
  · rintro ⟨k, hk, h⟩
    exact padicUnitsLog_eq_one_of_pow_eq_one ℓ hk h

/- English proof (translation)
Rewrite using `[← ker_padicUnitsLog, MonoidHom.mem_ker, padicUnitsLog_eq_one_iff]`.
-/
theorem mem_torsion_iff (u : ℤ_[ℓ]ˣ) :
    u ∈ CommGroup.torsion ℤ_[ℓ]ˣ ↔ u ^ torsionExponent ℓ = 1 := by
  rw [← ker_padicUnitsLog, MonoidHom.mem_ker, padicUnitsLog_eq_one_iff]

/- English proof (translation)
Rewrite using `[mem_torsion_iff, torsionExponent, if_pos rfl]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1` using `congrArg Units.val h`. Rewrite `h1` using `[Units.val_pow_eq_pow_val, Units.val_one, sq, mul_self_eq_one_iff]`.

Break down `h1 with h1 | h1` into its components or cases. Conclude with `Or.inl (Units.ext h1)`. Conclude with `Or.inr (Units.ext (by rw [h1, Units.val_neg, Units.val_one]))`. Apply the tactic sequence `rintro (rfl | rfl) <;> simp`.
-/
theorem mem_torsion_two_iff (u : ℤ_[2]ˣ) :
    u ∈ CommGroup.torsion ℤ_[2]ˣ ↔ u = 1 ∨ u = -1 := by
  rw [mem_torsion_iff, torsionExponent, if_pos rfl]
  constructor
  · intro h
    have h1 := congrArg Units.val h
    rw [Units.val_pow_eq_pow_val, Units.val_one, sq, mul_self_eq_one_iff] at h1
    rcases h1 with h1 | h1
    · exact Or.inl (Units.ext h1)
    · exact Or.inr (Units.ext (by rw [h1, Units.val_neg, Units.val_one]))
  · rintro (rfl | rfl) <;> simp

noncomputable def unitsModTorsionEquiv :
    ℤ_[ℓ]ˣ ⧸ CommGroup.torsion ℤ_[ℓ]ˣ ≃* Multiplicative ℤ_[ℓ] :=
  (QuotientGroup.quotientMulEquivOfEq (ker_padicUnitsLog ℓ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (padicUnitsLog_surjective ℓ))

end Limit

end Cyclotomic

end GroundTheory.Global
