import Mathlib
import GroundTheory.LocalFields.PadicLogHom

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section ExpLog

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

omit [ValuativeRel K] [IsNonarchimedeanLocalField K] [CharZero K] in
/- English proof (translation)
Rewrite using `[expSeries, tsum_eq_single 0]`. Simplify using the standard rewrite rules. Introduce `k hk`. Simplify using `[zero_pow hk]`.
-/
theorem expSeries_zero : expSeries (0 : K) = 1 := by
  rw [expSeries, tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [expSeries_zero]`. Consider the case `succ m ih`. Rewrite using `[succ_nsmul, expSeries_add p (nsmul_mem hx m) hx ha, ih, pow_succ]`.
-/
theorem expSeries_nsmul {a : ℤ} {x : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) (m : ℕ) :
    expSeries (m • x) = expSeries x ^ m := by
  induction m with
  | zero => simp [expSeries_zero]
  | succ m ih =>
    rw [succ_nsmul, expSeries_add p (nsmul_mem hx m) hx ha, ih, pow_succ]

/- English proof (translation)
Establish `hcx : c * x ∈ valBall K a`. Simplify using `using valBall_antitone (by omega : a ≤ d + a) (mul_mem_valBall hc hx)`. Establish `hs` using `summable_expSeries p hcx ha`. Rewrite using `[expSeries, hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]`. Simplify using `only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one, Nat.factorial_one]`.

Establish `: ∀ t : K, 1 + (c * x + t) - 1 - c * x = t` using `fun t ↦ by ring`. Rewrite using `[this]`. Use `tsum_mem_valBall fun k ↦ ?_` and prove the remaining obligations. Establish `h1 : (c * x) ^ (k + 1 + 1) / ((k + 1 + 1).factorial : K) = c ^ (k + 1 + 1) * (x ^ (k + 1 + 1) / ((k + 1 + 1).factorial : K))`. Rewrite using `[mul_pow, mul_div_assoc]`.

Rewrite using `[h1]`. Establish `hxk` using `expTerm_mem p hx (k + 1 + 1)`. Establish `hck` using `pow_mem_valBall hc (k + 1 + 1)`. Use `valBall_antitone ?_ (mul_mem_valBall hck hxk)` and prove the remaining obligations. Establish `h0` using `sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega : k + 1 + 1 ≠ 0)`.

Use `set v := padicValNat p (k + 1 + 1).factorial`. Use `set e := absRamificationIndex K`. Establish `hp2 : (2 : ℤ) ≤ p` using `by exact_mod_cast hp.out.two_le`. Establish `hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1`. Rewrite using `[Nat.cast_sub hp.out.one_le]`.

Simplify using the standard rewrite rules. Establish `h0' : (((p - 1) * v : ℕ) : ℤ) < k + 1 + 1` using `by exact_mod_cast h0`. Move the coercions through the operations in `[hp1] at h0'`. Establish `he : (0 : ℤ) ≤ e` using `by positivity`. Establish `h0'' : ((p : ℤ) - 1) * v ≤ k + 1` using `by linarith`.

Establish `ha' : (e : ℤ) + 1 ≤ ((p : ℤ) - 1) * a` using `by linarith`. Establish `hk : (0 : ℤ) ≤ k + 1` using `by positivity`. Establish `hkd : (0 : ℤ) ≤ k * d` using `by positivity`. Use `push_cast`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h0'' he, mul_le_mul_of_nonneg_left ha' hk]`.
-/
theorem expSeries_mul_sub_one_sub_mem {a d : ℤ} {x c : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) (hc : c ∈ valBall K d) (hd : 0 ≤ d) :
    expSeries (c * x) - 1 - c * x ∈ valBall K (2 * d + a + 1) := by
  have hcx : c * x ∈ valBall K a := by
    simpa using valBall_antitone (by omega : a ≤ d + a) (mul_mem_valBall hc hx)
  have hs := summable_expSeries p hcx ha
  rw [expSeries, hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one,
    Nat.factorial_one]
  have : ∀ t : K, 1 + (c * x + t) - 1 - c * x = t := fun t ↦ by ring
  rw [this]
  refine tsum_mem_valBall fun k ↦ ?_
  have h1 : (c * x) ^ (k + 1 + 1) / ((k + 1 + 1).factorial : K) =
      c ^ (k + 1 + 1) * (x ^ (k + 1 + 1) / ((k + 1 + 1).factorial : K)) := by
    rw [mul_pow, mul_div_assoc]
  rw [h1]
  have hxk := expTerm_mem p hx (k + 1 + 1)
  have hck := pow_mem_valBall hc (k + 1 + 1)
  refine valBall_antitone ?_ (mul_mem_valBall hck hxk)
  have h0 := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega : k + 1 + 1 ≠ 0)
  set v := padicValNat p (k + 1 + 1).factorial
  set e := absRamificationIndex K
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub hp.out.one_le]; simp
  have h0' : (((p - 1) * v : ℕ) : ℤ) < k + 1 + 1 := by exact_mod_cast h0
  push_cast [hp1] at h0'
  have he : (0 : ℤ) ≤ e := by positivity
  have h0'' : ((p : ℤ) - 1) * v ≤ k + 1 := by linarith
  have ha' : (e : ℤ) + 1 ≤ ((p : ℤ) - 1) * a := by linarith
  have hk : (0 : ℤ) ≤ k + 1 := by positivity
  have hkd : (0 : ℤ) ≤ k * d := by positivity
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left h0'' he, mul_le_mul_of_nonneg_left ha' hk]

/- English proof (translation)
Establish `ha1` using `one_le_of_lt_sub_one_mul p ha`. Establish `hy : expSeries x - 1 ∈ valBall K 1` using `valBall_antitone ha1 (expSeries_sub_one_mem p hx ha)`. Establish `h1` using `tendsto_logSeries p hy`. Simplify using `only [add_sub_cancel] at h1`. Use `tendsto_nhds_unique h1 ?_` and prove the remaining obligations.

Rewrite using `[← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_valBall]`. Introduce `N`. Rewrite using `[eventually_atTop]`. Use `set e := absRamificationIndex K`. Establish `he` using `one_le_absRamificationIndex (K := K) p`.

Use `⟨N.toNat, fun k hk ↦ ?_⟩` and prove the remaining obligations. Establish `hm0 : p ^ k ≠ 0` using `pow_ne_zero _ hp.out.ne_zero`. Establish `hm : ((p ^ k : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.mpr hm0`. Establish `heq : (expSeries x ^ (p ^ k) - 1) / ((p ^ k : ℕ) : K) - x = (expSeries (((p ^ k : ℕ) : K) * x) - 1 - ((p ^ k : ℕ) : K) * x) / ((p ^ k : ℕ) : K)`. Rewrite using `[← expSeries_nsmul p hx ha, nsmul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[heq]`. Establish `hmem` using `expSeries_mul_sub_one_sub_mem p hx ha (natCast_prime_pow_mem_valBall p k) (by positivity)`. Establish `hdiv` using `div_natCast_mem_valBall p hmem hm0`. Use `valBall_antitone ?_ hdiv` and prove the remaining obligations.

Rewrite using `[padicValNat.prime_pow]`. Establish `h2 : N ≤ (N.toNat : ℤ)` using `Int.self_le_toNat N`. Establish `h3 : (N.toNat : ℤ) ≤ k` using `by exact_mod_cast hk`. Establish `he' : (1 : ℤ) ≤ e` using `by exact_mod_cast he`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem logSeries_expSeries_sub_one {a : ℤ} {x : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    logSeries (expSeries x - 1) = x := by
  have ha1 := one_le_of_lt_sub_one_mul p ha
  have hy : expSeries x - 1 ∈ valBall K 1 :=
    valBall_antitone ha1 (expSeries_sub_one_mem p hx ha)
  have h1 := tendsto_logSeries p hy
  simp only [add_sub_cancel] at h1
  refine tendsto_nhds_unique h1 ?_
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_valBall]
  intro N
  rw [eventually_atTop]
  set e := absRamificationIndex K
  have he := one_le_absRamificationIndex (K := K) p
  refine ⟨N.toNat, fun k hk ↦ ?_⟩
  have hm0 : p ^ k ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hm : ((p ^ k : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have heq : (expSeries x ^ (p ^ k) - 1) / ((p ^ k : ℕ) : K) - x =
      (expSeries (((p ^ k : ℕ) : K) * x) - 1 - ((p ^ k : ℕ) : K) * x) / ((p ^ k : ℕ) : K) := by
    rw [← expSeries_nsmul p hx ha, nsmul_eq_mul]
    field_simp
  rw [heq]
  have hmem := expSeries_mul_sub_one_sub_mem p hx ha (natCast_prime_pow_mem_valBall p k)
    (by positivity)
  have hdiv := div_natCast_mem_valBall p hmem hm0
  refine valBall_antitone ?_ hdiv
  rw [padicValNat.prime_pow]
  have h2 : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  have h3 : (N.toNat : ℤ) ≤ k := by exact_mod_cast hk
  have he' : (1 : ℤ) ≤ e := by exact_mod_cast he
  nlinarith

end ExpLog

section Iso

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Establish `hset` using `hϖ.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (v := valuation K) n`. Establish `: y ∈ 𝓂[K] ^ n ↔ y ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])` using `Iff.rfl`. Rewrite using `[this, hset, mem_valBall]`. Use `show valuation K (y : K) ≤ valuation K (ϖ : K) ^ n ↔ _`.

Rewrite using `[← map_pow, ← normalizedValuation_le_iff, map_pow, normalizedValuation_uniformizer hϖ, ← WithZero.exp_nsmul]`. Simplify using the standard rewrite rules.
-/
theorem mem_maximalIdeal_pow_iff_valBall {n : ℕ} {y : 𝒪[K]} :
    y ∈ 𝓂[K] ^ n ↔ (y : K) ∈ valBall K n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hset := hϖ.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (v := valuation K) n
  have : y ∈ 𝓂[K] ^ n ↔ y ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) := Iff.rfl
  rw [this, hset, mem_valBall]
  show valuation K (y : K) ≤ valuation K (ϖ : K) ^ n ↔ _
  rw [← map_pow, ← normalizedValuation_le_iff, map_pow, normalizedValuation_uniformizer hϖ,
    ← WithZero.exp_nsmul]
  simp

/- English proof (translation)
Rewrite using `[← normalizedValuation_le_one_iff]`. Conclude with `hx.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)`.
-/
theorem mem_integer_of_mem_valBall {n : ℤ} (hn : 0 ≤ n) {x : K} (hx : x ∈ valBall K n) :
    x ∈ 𝒪[K] := by
  rw [← normalizedValuation_le_one_iff]
  exact hx.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)

variable (K) in

noncomputable def valBallEquivMaximalIdealPow (n : ℕ) :
    valBall K n ≃ₜ+ (𝓂[K] ^ n : Ideal 𝒪[K]) where
  toFun x := ⟨⟨x, mem_integer_of_mem_valBall (by positivity) x.2⟩,
    mem_maximalIdeal_pow_iff_valBall.mpr x.2⟩
  invFun y := ⟨((y : 𝒪[K]) : K), mem_maximalIdeal_pow_iff_valBall.mp y.2⟩
  left_inv x := rfl
  right_inv y := rfl
  map_add' x y := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

/- English proof (translation)
Use `one_le_of_lt_sub_one_mul p hn` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem one_le_of_lt_sub_one_mul_nat {n : ℕ}
    (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) : 1 ≤ n := by
  have := one_le_of_lt_sub_one_mul p hn
  omega

omit [CharZero K] in
/- English proof (translation)
The claim follows from `(mem_unitFiltrationUnits_iff_valBall hn1).mp u.2`.
-/
theorem sub_one_mem_valBall_of_mem {n : ℕ} (hn1 : 1 ≤ n) (u : unitFiltrationUnits K n) :
    ((u : Kˣ) : K) - 1 ∈ valBall K n :=
  (mem_unitFiltrationUnits_iff_valBall hn1).mp u.2

noncomputable def logValBallHom (n : ℕ) (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) :
    Additive (unitFiltrationUnits K n) →+ valBall K n where
  toFun u := ⟨logSeries ((((Additive.toMul u : unitFiltrationUnits K n) : Kˣ) : K) - 1),
    logSeries_mem_valBall p
      (sub_one_mem_valBall_of_mem (one_le_of_lt_sub_one_mul_nat p hn) (Additive.toMul u)) hn⟩
  map_zero' := Subtype.ext (by simp [logSeries])
  map_add' u w := by
    have h := (padicLog K).map_add
      (Additive.ofMul ⟨((Additive.toMul u : unitFiltrationUnits K n) : Kˣ),
        unitFiltrationUnits_antitone (one_le_of_lt_sub_one_mul_nat p hn) (Additive.toMul u).2⟩)
      (Additive.ofMul ⟨((Additive.toMul w : unitFiltrationUnits K n) : Kˣ),
        unitFiltrationUnits_antitone (one_le_of_lt_sub_one_mul_nat p hn) (Additive.toMul w).2⟩)
    exact Subtype.ext h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_logValBallHom (n : ℕ) (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n)
    (u : Additive (unitFiltrationUnits K n)) :
    (logValBallHom p n hn u : K) =
      logSeries ((((Additive.toMul u : unitFiltrationUnits K n) : Kˣ) : K) - 1) := rfl

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `u hu`. Establish `h` using `congrArg Subtype.val hu`. Rewrite `h` using `[coe_logValBallHom]`. Establish `hx` using `eq_zero_of_logSeries_eq_zero p hn (sub_one_mem_valBall_of_mem (one_le_of_lt_sub_one_mul_nat p hn) (Additive.toMul u)) h`.

Apply `Additive.toMul.injective` to reduce the goal to its premises. Use `ext`. Simplify `hx` using `[sub_eq_zero]`.
-/
theorem logValBallHom_injective (n : ℕ) (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) :
    Function.Injective (logValBallHom p n hn) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  have h := congrArg Subtype.val hu
  rw [coe_logValBallHom] at h
  have hx := eq_zero_of_logSeries_eq_zero p hn
    (sub_one_mem_valBall_of_mem (one_le_of_lt_sub_one_mul_nat p hn) (Additive.toMul u)) h
  apply Additive.toMul.injective
  ext
  simpa [sub_eq_zero] using hx

omit [CharZero K] in
/- English proof (translation)
Introduce `h`. Rewrite `hx` using `[h, zero_sub, mem_valBall, Valuation.map_neg, map_one, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem expSeries_ne_zero {n : ℕ} (hn1 : 1 ≤ n) {x : K} (hx : expSeries x - 1 ∈ valBall K n) :
    expSeries x ≠ 0 := by
  intro h
  rw [h, zero_sub, mem_valBall, Valuation.map_neg, map_one, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at hx
  omega

noncomputable def expUnit (n : ℕ) (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n)
    (x : valBall K n) : unitFiltrationUnits K n :=
  ⟨Units.mk0 (expSeries (x : K))
    (expSeries_ne_zero (one_le_of_lt_sub_one_mul_nat p hn) (expSeries_sub_one_mem p x.2 hn)),
    (mem_unitFiltrationUnits_iff_valBall (one_le_of_lt_sub_one_mul_nat p hn)).mpr
      (expSeries_sub_one_mem p x.2 hn)⟩

/- English proof (translation)
The claim follows from `Subtype.ext (logSeries_expSeries_sub_one p x.2 hn)`.
-/
theorem logValBallHom_expUnit (n : ℕ) (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n)
    (x : valBall K n) : logValBallHom p n hn (Additive.ofMul (expUnit p n hn x)) = x :=
  Subtype.ext (logSeries_expSeries_sub_one p x.2 hn)

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `x0`. Rewrite using `[ContinuousAt, ← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_valBall]`. Introduce `N`. Use `set r : ℤ := max N n`.

Establish `hr : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * r` using `sub_one_le_of_lt p hn (le_max_right _ _)`. Establish `hopen` using `(isOpen_valBall r).preimage (continuous_subtype_val.sub continuous_const : Continuous fun x : valBall K n ↦ (x : K) - x0)`. Use `filter_upwards [hopen.mem_nhds (by simp)] with x hx`. Establish `hx' : (x : K) - x0 ∈ valBall K r` using `hx`. Establish `hxn : (x : K) - x0 ∈ valBall K n` using `valBall_antitone (le_max_right _ _) hx'`.

Establish `heq : expSeries (x : K) = expSeries (x0 : K) * expSeries ((x : K) - x0)`. Rewrite using `[← expSeries_add p x0.2 hxn hn, add_sub_cancel]`. Establish `h0 : expSeries (x0 : K) ∈ valBall K 0`. Establish `h1` using `valBall_antitone (by positivity : (0 : ℤ) ≤ n) (expSeries_sub_one_mem p x0.2 hn)`. Establish `h2 : (1 : K) ∈ valBall K 0` using `by simp [mem_valBall]`.

Simplify using `using add_mem h1 h2`. Rewrite using `[heq, show expSeries (x0 : K) * expSeries ((x : K) - x0) - expSeries (x0 : K) = expSeries (x0 : K) * (expSeries ((x : K) - x0) - 1) by ring]`. Establish `hNr : N ≤ 0 + r` using `by rw [zero_add]; exact le_max_left _ _`. Use `valBall_antitone hNr (mul_mem_valBall h0 ?_)` and prove the remaining obligations. Conclude with `expSeries_sub_one_mem p hx' hr`.
-/
theorem continuous_expSeries_valBall (n : ℕ)
    (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) :
    Continuous fun x : valBall K n ↦ expSeries (x : K) := by
  rw [continuous_iff_continuousAt]
  intro x0
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_valBall]
  intro N
  set r : ℤ := max N n
  have hr : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * r :=
    sub_one_le_of_lt p hn (le_max_right _ _)
  have hopen := (isOpen_valBall r).preimage
    (continuous_subtype_val.sub continuous_const : Continuous fun x : valBall K n ↦ (x : K) - x0)
  filter_upwards [hopen.mem_nhds (by simp)] with x hx
  have hx' : (x : K) - x0 ∈ valBall K r := hx
  have hxn : (x : K) - x0 ∈ valBall K n := valBall_antitone (le_max_right _ _) hx'
  have heq : expSeries (x : K) = expSeries (x0 : K) * expSeries ((x : K) - x0) := by
    rw [← expSeries_add p x0.2 hxn hn, add_sub_cancel]
  have h0 : expSeries (x0 : K) ∈ valBall K 0 := by
    have h1 := valBall_antitone (by positivity : (0 : ℤ) ≤ n) (expSeries_sub_one_mem p x0.2 hn)
    have h2 : (1 : K) ∈ valBall K 0 := by simp [mem_valBall]
    simpa using add_mem h1 h2
  rw [heq, show expSeries (x0 : K) * expSeries ((x : K) - x0) - expSeries (x0 : K) =
    expSeries (x0 : K) * (expSeries ((x : K) - x0) - 1) by ring]
  have hNr : N ≤ 0 + r := by rw [zero_add]; exact le_max_left _ _
  refine valBall_antitone hNr (mul_mem_valBall h0 ?_)
  exact expSeries_sub_one_mem p hx' hr

noncomputable def logValBallEquiv (n : ℕ) (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) :
    Additive (unitFiltrationUnits K n) ≃ₜ+ valBall K n where
  toFun := logValBallHom p n hn
  invFun x := Additive.ofMul (expUnit p n hn x)
  left_inv u := logValBallHom_injective p n hn (logValBallHom_expUnit p n hn _)
  right_inv x := logValBallHom_expUnit p n hn x
  map_add' := map_add _
  continuous_toFun := by
    have hι : Continuous fun u : Additive (unitFiltrationUnits K n) ↦
        (Additive.ofMul (⟨((Additive.toMul u : unitFiltrationUnits K n) : Kˣ),
          unitFiltrationUnits_antitone (one_le_of_lt_sub_one_mul_nat p hn)
            (Additive.toMul u).2⟩ : unitFiltrationUnits K 1)) :=
      continuous_ofMul.comp ((continuous_subtype_val.comp continuous_toMul).subtype_mk _)
    exact (continuous_padicLog.comp hι).subtype_mk _
  continuous_invFun := by
    refine continuous_ofMul.comp (Continuous.subtype_mk ?_ _)
    rw [Units.isEmbedding_val₀.continuous_iff]
    exact continuous_expSeries_valBall p n hn

noncomputable def unitFiltrationLogEquiv (n : ℕ)
    (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) :
    Additive (unitFiltrationUnits K n) ≃ₜ+ (𝓂[K] ^ n : Ideal 𝒪[K]) :=
  (logValBallEquiv p n hn).trans (valBallEquivMaximalIdealPow K n)

/- English proof (translation)
Use `congrArg (fun v ↦ (((Additive.toMul v : unitFiltrationUnits K n) : Kˣ) : K)) ((logValBallEquiv p n hn).symm_apply_apply (Additive.ofMul u))` as an intermediate fact. Conclude with `this`.
-/
theorem expSeries_logSeries {n : ℕ} (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n)
    (u : unitFiltrationUnits K n) :
    expSeries (logSeries (((u : Kˣ) : K) - 1)) = ((u : Kˣ) : K) := by
  have := congrArg (fun v ↦ (((Additive.toMul v : unitFiltrationUnits K n) : Kˣ) : K))
    ((logValBallEquiv p n hn).symm_apply_apply (Additive.ofMul u))
  exact this

end Iso

end GroundTheory.LocalField
