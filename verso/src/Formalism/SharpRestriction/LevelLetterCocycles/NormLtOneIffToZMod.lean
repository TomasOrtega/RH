import Mathlib

noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators.Cyc

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Rewrite using `[← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]`.
-/
theorem norm_lt_one_iff_toZMod (x : ℤ_[l]) : ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by

  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

/- English proof (translation)
Rewrite using `[show (-((1 : ℕ) : ℤ)) = -1 by simp, PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]`. Simplify using `using h`.
-/
theorem norm_le_inv_of_lt_one (x : ℤ_[l]) (h : ‖x‖ < 1) : ‖x‖ ≤ (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by

  rw [show (-((1 : ℕ) : ℤ)) = -1 by simp, PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]
  simpa using h

/- English proof (translation)
Use `set F : Polynomial ℤ := Polynomial.X ^ (l - 1) - 1 with hFdef`. Establish `hc0 : PadicInt.toZMod c ≠ 0` using `fun h0 => by`. Use `(norm_lt_one_iff_toZMod c).mpr h0` as an intermediate fact. Rewrite `this` using `[hc]`. Conclude with `lt_irrefl _ this`.

Establish `hn : ‖((l - 1 : ℕ) : ℤ_[l])‖ = 1`. Use `le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => ?_)` and prove the remaining obligations. Rewrite `h` using `[norm_lt_one_iff_toZMod, map_natCast, ZMod.natCast_eq_zero_iff]`. Establish `h2` using `hl.out.two_le`. Use `Nat.le_of_dvd (by omega) h` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `e1 : Polynomial.aeval c F = c ^ (l - 1) - 1` using `by simp [hFdef]`. Establish `e2 : Polynomial.aeval c (Polynomial.derivative F) = ((l - 1 : ℕ) : ℤ_[l]) * c ^ (l - 1 - 1)`. Simplify using `[hFdef, Polynomial.derivative_X_pow]`. Establish `hF' : ‖Polynomial.aeval c (Polynomial.derivative F)‖ = 1`.

Rewrite using `[e2, norm_mul, norm_pow, hc, one_pow, mul_one, hn]`. Establish `hF : ‖Polynomial.aeval c F‖ < 1`. Rewrite using `[e1, norm_lt_one_iff_toZMod, map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one hc0, sub_self]`. Take `⟨z, hz, hzc, -⟩` from `hensels_lemma (F := F) (a := c) (by rw [hF', one_pow]; exact hF)`. Use `⟨z, ?_, ?_⟩` and prove the remaining obligations.

Simplify `hz` using `[hFdef, sub_eq_zero]`. Rewrite `hzc` using `[hF']`. Conclude with `hzc`.
-/
theorem teich (c : ℤ_[l]) (hc : ‖c‖ = 1) : ∃ ω : ℤ_[l], ω ^ (l - 1) = 1 ∧ ‖ω - c‖ < 1 := by

  classical
  set F : Polynomial ℤ := Polynomial.X ^ (l - 1) - 1 with hFdef
  have hc0 : PadicInt.toZMod c ≠ 0 := fun h0 => by
    have := (norm_lt_one_iff_toZMod c).mpr h0
    rw [hc] at this
    exact lt_irrefl _ this
  have hn : ‖((l - 1 : ℕ) : ℤ_[l])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => ?_)
    rw [norm_lt_one_iff_toZMod, map_natCast, ZMod.natCast_eq_zero_iff] at h
    have h2 := hl.out.two_le
    have := Nat.le_of_dvd (by omega) h
    omega
  have e1 : Polynomial.aeval c F = c ^ (l - 1) - 1 := by simp [hFdef]
  have e2 : Polynomial.aeval c (Polynomial.derivative F) = ((l - 1 : ℕ) : ℤ_[l]) * c ^ (l - 1 - 1) := by
    simp [hFdef, Polynomial.derivative_X_pow]
  have hF' : ‖Polynomial.aeval c (Polynomial.derivative F)‖ = 1 := by
    rw [e2, norm_mul, norm_pow, hc, one_pow, mul_one, hn]
  have hF : ‖Polynomial.aeval c F‖ < 1 := by
    rw [e1, norm_lt_one_iff_toZMod, map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one hc0, sub_self]
  obtain ⟨z, hz, hzc, -⟩ := hensels_lemma (F := F) (a := c) (by rw [hF', one_pow]; exact hF)
  refine ⟨z, ?_, ?_⟩
  · simpa [hFdef, sub_eq_zero] using hz
  · rw [hF'] at hzc; exact hzc

/- English proof (translation)
Establish `hp` using `hl.out`. Establish `h3 : 3 ≤ l` using `by have := hp.two_le; omega`. Establish `hu1 : u - 1 ∈ Ideal.span {(l : ℤ_[l]) ^ 1}`. Rewrite using `[← PadicInt.norm_le_pow_iff_mem_span_pow, hu]`. Simplify using the standard rewrite rules.

Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.1 hu1`. Establish `hlpos : (0 : ℝ) < l` using `by exact_mod_cast hp.pos`. Establish `hrn : ‖r‖ = 1`. Establish `: ‖u - 1‖ = ‖r‖ * (l : ℝ)⁻¹` using `by rw [← hr, pow_one, norm_mul, PadicInt.norm_p]`. Rewrite `this` using `[hu]`.

Establish `hne : (l : ℝ)⁻¹ ≠ 0` using `inv_ne_zero hlpos.ne'`. Clear denominators, using `at this` for the nonvanishing conditions. Combine the linear equalities and inequalities to obtain the conclusion. Use `set a : ℤ := ((PadicInt.toZModPow (n + 1) r).val : ℤ) with ha_def`. Establish `ha_cast : (a : ZMod (l ^ (n + 1))) = PadicInt.toZModPow (n + 1) r`.

Rewrite using `[ha_def, Int.cast_natCast, ZMod.natCast_zmod_val]`. Establish `ha : ¬ (l : ℤ) ∣ a`. Introduce `hdvd`. Establish `h1 : (a : ZMod (l ^ 1)) = 0`. Rewrite using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`.

Simplify using `using hdvd`. Establish `h2 : (a : ZMod (l ^ 1)) = PadicInt.toZModPow 1 r`. Rewrite using `[← PadicInt.zmod_cast_comp_toZModPow 1 (n + 1) (by omega), RingHom.comp_apply, ← ha_cast, map_intCast]`. Rewrite `h1` using `[h2, ← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow, hrn]`. Establish `: (l : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1`.

Rewrite using `[Nat.cast_one, zpow_neg_one]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hord : orderOf (1 + (l : ZMod (l ^ (n + 1))) ^ 1 * a) = l ^ n` using `ZMod.orderOf_one_add_mul_prime_pow hp 1 one_ne_zero (by omega) a ha n`. Establish `hub : PadicInt.toZModPow (n + 1) u = 1 + (l : ZMod (l ^ (n + 1))) ^ 1 * a`. Establish `: u = 1 + (l : ℤ_[l]) ^ 1 * r` using `by rw [pow_one, mul_comm]; rw [pow_one] at hr; rw [hr]; ring`.

Rewrite using `[this, map_add, map_one, map_mul, map_pow, map_natCast, ha_cast]`. Establish `huu : IsUnit (PadicInt.toZModPow (n + 1) u)`. Apply `IsUnit.map` to reduce the goal to its premises. Rewrite using `[PadicInt.isUnit_iff]`. Establish `: u = 1 + (u - 1)` using `by ring`.

Rewrite using `[this]`. Establish `h1 : ‖(u - 1)‖ < ‖(1 : ℤ_[l])‖`. Rewrite using `[hu, norm_one]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)`. Rewrite using `[← norm_one (α := ℤ_[l])]`. Conclude with `PadicInt.norm_add_eq_max_of_ne (ne_of_lt h1).symm |>.trans (max_eq_left h1.le)`.

Establish `hcu : IsUnit (PadicInt.toZModPow (n + 1) c)`. Apply `IsUnit.map` to reduce the goal to its premises. Rewrite using `[PadicInt.isUnit_iff]`. Establish `: c = 1 + (c - 1)` using `by ring`. Rewrite using `[this]`.

Establish `h1 : ‖(c - 1)‖ < ‖(1 : ℤ_[l])‖` using `by rw [norm_one]; exact hc`. Rewrite using `[← norm_one (α := ℤ_[l])]`. Conclude with `PadicInt.norm_add_eq_max_of_ne (ne_of_lt h1).symm |>.trans (max_eq_left h1.le)`. Use `set U := huu.unit`. Use `set C := hcu.unit`.

Establish `hdiv : l ^ 1 ∣ l ^ (n + 1)` using `pow_dvd_pow l (by omega)`. Use `haveI : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩`. Use `haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hp.ne_zero⟩`. Establish `hker : ∀ x : ℤ_[l], ‖x - 1‖ < 1 → ∀ hx : IsUnit (PadicInt.toZModPow (n + 1) x), hx.unit ∈ (ZMod.unitsMap hdiv).ker`. Introduce `x hx hxu`.

Rewrite using `[MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_def, Units.coe_map, IsUnit.unit_spec]`. Express the relevant statement in the definitionally equal form `ZMod.castHom hdiv (ZMod (l ^ 1)) (PadicInt.toZModPow (n + 1) x) = 1`. Rewrite using `[← RingHom.comp_apply, PadicInt.zmod_cast_comp_toZModPow 1 (n + 1) (by omega), ← sub_eq_zero, ← map_one (PadicInt.toZModPow 1), ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]`. Conclude with `norm_le_inv_of_lt_one _ hx`. Establish `hUk : U ∈ (ZMod.unitsMap hdiv).ker` using `hker u (by rw [hu]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)) huu`.

Establish `hCk : C ∈ (ZMod.unitsMap hdiv).ker` using `hker c hc hcu`. Establish `hcardG : Nat.card (ZMod (l ^ (n + 1)))ˣ = l ^ n * (l - 1)`. Rewrite using `[Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hp]`. Establish `hcardH : Nat.card (ZMod (l ^ 1))ˣ = l - 1`. Rewrite using `[Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hp]`.

Establish `hrange : (ZMod.unitsMap hdiv).range = ⊤` using `MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective hdiv)`. Establish `hcardK : Nat.card (ZMod.unitsMap hdiv).ker = l ^ n`. Establish `h1` using `Subgroup.card_mul_index (ZMod.unitsMap hdiv).ker`. Rewrite `h1` using `[Subgroup.index_ker, hrange, Subgroup.card_top, hcardH, hcardG]`. Establish `hl1 : 0 < l - 1` using `by omega`.

Conclude with `Nat.eq_of_mul_eq_mul_right hl1 h1`. Establish `hzp : Subgroup.zpowers U = (ZMod.unitsMap hdiv).ker`. Apply `Subgroup.eq_of_le_of_card_ge` to reduce the goal to its premises. Rewrite using `[Subgroup.zpowers_le]`. Conclude with `hUk`.

Rewrite using `[hcardK, Nat.card_zpowers, ← orderOf_units, IsUnit.unit_spec, hub, hord]`. Rewrite `hCk` using `[← hzp, ← mem_powers_iff_mem_zpowers]`. Take `⟨k, hk⟩` from `hCk`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_pow, sub_eq_zero]`.

Use `congrArg Units.val hk` as an intermediate fact. Simplify `this` using `[U, C]`.
-/
theorem pow_approx (hl2 : l ≠ 2) (u : ℤ_[l]) (hu : ‖u - 1‖ = (l : ℝ)⁻¹) (c : ℤ_[l]) (hc : ‖c - 1‖ < 1)
    (n : ℕ) : ∃ k : ℕ, ‖u ^ k - c‖ ≤ (l : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
  have hp := hl.out
  have h3 : 3 ≤ l := by have := hp.two_le; omega

  have hu1 : u - 1 ∈ Ideal.span {(l : ℤ_[l]) ^ 1} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow, hu]; simp
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hu1
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hp.pos
  have hrn : ‖r‖ = 1 := by
    have : ‖u - 1‖ = ‖r‖ * (l : ℝ)⁻¹ := by rw [← hr, pow_one, norm_mul, PadicInt.norm_p]
    rw [hu] at this
    have hne : (l : ℝ)⁻¹ ≠ 0 := inv_ne_zero hlpos.ne'
    field_simp at this
    linarith

  set a : ℤ := ((PadicInt.toZModPow (n + 1) r).val : ℤ) with ha_def
  have ha_cast : (a : ZMod (l ^ (n + 1))) = PadicInt.toZModPow (n + 1) r := by
    rw [ha_def, Int.cast_natCast, ZMod.natCast_zmod_val]
  have ha : ¬ (l : ℤ) ∣ a := by
    intro hdvd
    have h1 : (a : ZMod (l ^ 1)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; simpa using hdvd
    have h2 : (a : ZMod (l ^ 1)) = PadicInt.toZModPow 1 r := by
      rw [← PadicInt.zmod_cast_comp_toZModPow 1 (n + 1) (by omega), RingHom.comp_apply, ← ha_cast, map_intCast]
    rw [h2, ← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow, hrn] at h1
    have : (l : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 := by
      rw [Nat.cast_one, zpow_neg_one]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    linarith
  have hord : orderOf (1 + (l : ZMod (l ^ (n + 1))) ^ 1 * a) = l ^ n :=
    ZMod.orderOf_one_add_mul_prime_pow hp 1 one_ne_zero (by omega) a ha n
  have hub : PadicInt.toZModPow (n + 1) u = 1 + (l : ZMod (l ^ (n + 1))) ^ 1 * a := by
    have : u = 1 + (l : ℤ_[l]) ^ 1 * r := by rw [pow_one, mul_comm]; rw [pow_one] at hr; rw [hr]; ring
    rw [this, map_add, map_one, map_mul, map_pow, map_natCast, ha_cast]

  have huu : IsUnit (PadicInt.toZModPow (n + 1) u) := by
    apply IsUnit.map
    rw [PadicInt.isUnit_iff]
    have : u = 1 + (u - 1) := by ring
    rw [this]
    have h1 : ‖(u - 1)‖ < ‖(1 : ℤ_[l])‖ := by
      rw [hu, norm_one]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    rw [← norm_one (α := ℤ_[l])]
    exact PadicInt.norm_add_eq_max_of_ne (ne_of_lt h1).symm |>.trans (max_eq_left h1.le)
  have hcu : IsUnit (PadicInt.toZModPow (n + 1) c) := by
    apply IsUnit.map
    rw [PadicInt.isUnit_iff]
    have : c = 1 + (c - 1) := by ring
    rw [this]
    have h1 : ‖(c - 1)‖ < ‖(1 : ℤ_[l])‖ := by rw [norm_one]; exact hc
    rw [← norm_one (α := ℤ_[l])]
    exact PadicInt.norm_add_eq_max_of_ne (ne_of_lt h1).symm |>.trans (max_eq_left h1.le)
  set U := huu.unit
  set C := hcu.unit
  have hdiv : l ^ 1 ∣ l ^ (n + 1) := pow_dvd_pow l (by omega)
  haveI : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hker : ∀ x : ℤ_[l], ‖x - 1‖ < 1 → ∀ hx : IsUnit (PadicInt.toZModPow (n + 1) x), hx.unit ∈ (ZMod.unitsMap hdiv).ker := by
    intro x hx hxu
    rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_def, Units.coe_map, IsUnit.unit_spec]
    change ZMod.castHom hdiv (ZMod (l ^ 1)) (PadicInt.toZModPow (n + 1) x) = 1
    rw [← RingHom.comp_apply, PadicInt.zmod_cast_comp_toZModPow 1 (n + 1) (by omega),
      ← sub_eq_zero, ← map_one (PadicInt.toZModPow 1), ← map_sub, ← RingHom.mem_ker,
      PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
    exact norm_le_inv_of_lt_one _ hx
  have hUk : U ∈ (ZMod.unitsMap hdiv).ker := hker u (by rw [hu]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)) huu
  have hCk : C ∈ (ZMod.unitsMap hdiv).ker := hker c hc hcu

  have hcardG : Nat.card (ZMod (l ^ (n + 1)))ˣ = l ^ n * (l - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hp]
  have hcardH : Nat.card (ZMod (l ^ 1))ˣ = l - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hp]
  have hrange : (ZMod.unitsMap hdiv).range = ⊤ := MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective hdiv)
  have hcardK : Nat.card (ZMod.unitsMap hdiv).ker = l ^ n := by
    have h1 := Subgroup.card_mul_index (ZMod.unitsMap hdiv).ker
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, hcardH, hcardG] at h1
    have hl1 : 0 < l - 1 := by omega
    exact Nat.eq_of_mul_eq_mul_right hl1 h1
  have hzp : Subgroup.zpowers U = (ZMod.unitsMap hdiv).ker := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact hUk
    · rw [hcardK, Nat.card_zpowers, ← orderOf_units, IsUnit.unit_spec, hub, hord]
  rw [← hzp, ← mem_powers_iff_mem_zpowers] at hCk
  obtain ⟨k, hk⟩ := hCk
  refine ⟨k, ?_⟩
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_pow,
    sub_eq_zero]
  have := congrArg Units.val hk
  simpa [U, C] using this

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators.Cyc
