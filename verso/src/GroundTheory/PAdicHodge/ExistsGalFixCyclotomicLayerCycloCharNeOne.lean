import Mathlib
import GroundTheory.PAdicHodge.TateCpTwist
import GroundTheory.PAdicHodge.AxLemma
import GroundTheory.PAdicHodge.TateNormalizedTrace
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open IntermediateField UniformSpace

variable {p : ℕ} [hp : Fact p.Prime]

section Torsion

/- English proof (translation)
Take `⟨m', rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hm`. Establish `hexp : (1 + w) ^ (m' + 1) - 1 = ((m' + 1 : ℕ) : PadicAlgCl p) * w + ∑ k ∈ Finset.range m', w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)`. Rewrite using `[add_comm (1 : PadicAlgCl p) w, add_pow, Finset.sum_range_succ', Finset.sum_range_succ']`. Simplify using `only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, pow_one, Nat.choose_one_right, zero_add]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.out.one_lt`. Establish `hwpos : 0 < ‖w‖` using `norm_pos_iff.2 hw0`. Establish `hmpos : 0 < ‖((m' + 1 : ℕ) : PadicAlgCl p)‖`. Rewrite using `[norm_pos_iff]`. Conclude with `Nat.succ_ne_zero m'` after adjusting the coercions.

Establish `hlead : 0 < ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖`. Rewrite using `[norm_mul]`. Conclude with `mul_pos hmpos hwpos`. Establish `hterm : ∀ k ∈ Finset.range m', ‖w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ < ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖`. Introduce `k _`.

Establish `hch : ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p) * ((k + 1 + 1 : ℕ) : PadicAlgCl p) = ((m' + 1 : ℕ) : PadicAlgCl p) * (m'.choose (k + 1) : PadicAlgCl p)`. Conclude with `(Nat.add_one_mul_choose_eq m' (k + 1)).symm` after adjusting the coercions. Establish `hk0 : (k + 1 + 1 : ℕ) ≠ 0` using `by omega`. Establish `hknorm : ((k + 1 + 1 : ℕ) : ℝ)⁻¹ ≤ ‖((k + 1 + 1 : ℕ) : PadicAlgCl p)‖`. Rewrite using `[norm_natCast_padicAlgCl hk0, zpow_neg, zpow_natCast]`.

Use `gcongr`. Conclude with `Nat.le_of_dvd (by omega) pow_padicValNat_dvd` after adjusting the coercions. Establish `hkpos : (0 : ℝ) < ((k + 1 + 1 : ℕ) : ℝ)` using `by exact_mod_cast Nat.succ_pos _`. Establish `hC : ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ ≤ ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ((k + 1 + 1 : ℕ) : ℝ)`. Establish `h1` using `congrArg norm hch`.

Rewrite `h1` using `[norm_mul, norm_mul]`. Establish `h2 : ‖(m'.choose (k + 1) : PadicAlgCl p)‖ ≤ 1` using `IsUltrametricDist.norm_natCast_le_one (PadicAlgCl p) _`. Establish `h3 : ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ * ((k + 1 + 1 : ℕ) : ℝ)⁻¹ ≤ ‖((m' + 1 : ℕ) : PadicAlgCl p)‖`. Combine the equalities or inequalities in the displayed calculation. Rewrite `h3` using `[← div_eq_mul_inv, div_le_iff₀ hkpos]`. Then use the resulting hypothesis.

Establish `hpow : ((k + 1 + 1 : ℕ) : ℝ) * ‖w‖ ^ (k + 1) < 1`. Establish `h1 : ‖w‖ ^ (k + 1) < ((p : ℝ)⁻¹) ^ (k + 1)` using `pow_lt_pow_left₀ hw (norm_nonneg _) (Nat.succ_ne_zero k)`. Establish `h2 : ((k + 1 + 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ (k + 1)`. Use `Nat.lt_pow_self (n := k + 1) hp.out.one_lt` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, norm_pow, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Use `_ < (‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ‖w‖) * 1 := mul_lt_mul_of_pos_left hpow (mul_pos hmpos hwpos)`.

Use `_ = _ := mul_one _`. Establish `htail : ‖∑ k ∈ Finset.range m', w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ < ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖`. Break down `(Finset.range m').eq_empty_or_nonempty with h | h` into its components or cases. Rewrite using `[h, Finset.sum_empty, norm_zero]`. Conclude with `hlead`.

Take `⟨i, hi, hle⟩` from `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty h (fun k => w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p))`. Conclude with `hle.trans_lt (hterm i hi)`. Introduce `h`. Establish `h0 : (1 + w) ^ (m' + 1) - 1 = 0` using `by rw [h, sub_self]`. Rewrite `h0` using `[hexp]`.

Establish `hne : ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ ≠ ‖∑ k ∈ Finset.range m', w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖` using `htail.ne'`. Use `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Conclude with `hlead.ne (this.trans (max_eq_left htail.le))`.
-/
theorem one_add_pow_ne_one {w : PadicAlgCl p} (hw0 : w ≠ 0) (hw : ‖w‖ < (p : ℝ)⁻¹) {m : ℕ}
    (hm : m ≠ 0) : (1 + w) ^ m ≠ 1 := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have hexp : (1 + w) ^ (m' + 1) - 1 = ((m' + 1 : ℕ) : PadicAlgCl p) * w +
      ∑ k ∈ Finset.range m', w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p) := by
    rw [add_comm (1 : PadicAlgCl p) w, add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, pow_one,
      Nat.choose_one_right, zero_add]
    ring
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hmpos : 0 < ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ := by
    rw [norm_pos_iff]; exact_mod_cast Nat.succ_ne_zero m'
  have hlead : 0 < ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ := by
    rw [norm_mul]; exact mul_pos hmpos hwpos

  have hterm : ∀ k ∈ Finset.range m', ‖w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖
      < ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ := by
    intro k _

    have hch : ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p) * ((k + 1 + 1 : ℕ) : PadicAlgCl p) =
        ((m' + 1 : ℕ) : PadicAlgCl p) * (m'.choose (k + 1) : PadicAlgCl p) := by
      exact_mod_cast (Nat.add_one_mul_choose_eq m' (k + 1)).symm
    have hk0 : (k + 1 + 1 : ℕ) ≠ 0 := by omega
    have hknorm : ((k + 1 + 1 : ℕ) : ℝ)⁻¹ ≤ ‖((k + 1 + 1 : ℕ) : PadicAlgCl p)‖ := by
      rw [norm_natCast_padicAlgCl hk0, zpow_neg, zpow_natCast]
      gcongr
      exact_mod_cast Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    have hkpos : (0 : ℝ) < ((k + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    have hC : ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ ≤
        ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ((k + 1 + 1 : ℕ) : ℝ) := by
      have h1 := congrArg norm hch
      rw [norm_mul, norm_mul] at h1
      have h2 : ‖(m'.choose (k + 1) : PadicAlgCl p)‖ ≤ 1 :=
        IsUltrametricDist.norm_natCast_le_one (PadicAlgCl p) _
      have h3 : ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ * ((k + 1 + 1 : ℕ) : ℝ)⁻¹ ≤
          ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ := by
        calc _ ≤ ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ *
              ‖((k + 1 + 1 : ℕ) : PadicAlgCl p)‖ := by gcongr
          _ = _ := h1
          _ ≤ ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * 1 := by gcongr
          _ = _ := mul_one _
      rwa [← div_eq_mul_inv, div_le_iff₀ hkpos] at h3

    have hpow : ((k + 1 + 1 : ℕ) : ℝ) * ‖w‖ ^ (k + 1) < 1 := by
      have h1 : ‖w‖ ^ (k + 1) < ((p : ℝ)⁻¹) ^ (k + 1) :=
        pow_lt_pow_left₀ hw (norm_nonneg _) (Nat.succ_ne_zero k)
      have h2 : ((k + 1 + 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ (k + 1) := by
        have := Nat.lt_pow_self (n := k + 1) hp.out.one_lt
        exact_mod_cast this
      calc ((k + 1 + 1 : ℕ) : ℝ) * ‖w‖ ^ (k + 1) < ((k + 1 + 1 : ℕ) : ℝ) * ((p : ℝ)⁻¹) ^ (k + 1) :=
            mul_lt_mul_of_pos_left h1 hkpos
        _ ≤ (p : ℝ) ^ (k + 1) * ((p : ℝ)⁻¹) ^ (k + 1) := by gcongr
        _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ (by positivity), one_pow]
    rw [norm_mul, norm_pow, norm_mul]
    calc ‖w‖ ^ (k + 1 + 1) * ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖
        ≤ ‖w‖ ^ (k + 1 + 1) * (‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ((k + 1 + 1 : ℕ) : ℝ)) := by
          gcongr
      _ = (‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ‖w‖) * (((k + 1 + 1 : ℕ) : ℝ) * ‖w‖ ^ (k + 1)) := by
          ring
      _ < (‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ‖w‖) * 1 :=
          mul_lt_mul_of_pos_left hpow (mul_pos hmpos hwpos)
      _ = _ := mul_one _
  have htail : ‖∑ k ∈ Finset.range m', w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖
      < ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ := by
    rcases (Finset.range m').eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty, norm_zero]; exact hlead
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty h
        (fun k => w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p))
      exact hle.trans_lt (hterm i hi)
  intro h
  have h0 : (1 + w) ^ (m' + 1) - 1 = 0 := by rw [h, sub_self]
  rw [hexp] at h0
  have hne : ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ ≠
      ‖∑ k ∈ Finset.range m', w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ :=
    htail.ne'
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [h0, norm_zero] at this
  exact hlead.ne (this.trans (max_eq_left htail.le))

end Torsion

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

section Character

/- English proof (translation)
Rewrite using `[cycloChar, MonoidHom.comp_apply, cyclotomicCharacter.toZModPow]`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `@Subsingleton.elim (ZMod 1) _ _ _`. Use `(modularCyclotomicCharacter.unique _ _ _ ?_).symm` and prove the remaining obligations. Introduce `t ht`.

Establish `hp1 : p ^ n ≠ 1` using `(Nat.one_lt_pow hn.ne' hp.out.one_lt).ne'`. Rewrite using `[ZMod.val_one'' hp1, pow_one]`. Establish `ht' : (t : PadicAlgCl p) ^ p ^ n = 1`. Use `(mem_rootsOfUnity _ _).1 ht` as an intermediate fact. Simplify using `using congrArg Units.val this`.

Conclude with `h _ ht'`.
-/
theorem cycloChar_toZModPow_eq_one (σ : Gal(PadicAlgCl p/K)) (n : ℕ)
    (h : ∀ ζ : PadicAlgCl p, ζ ^ p ^ n = 1 → σ ζ = ζ) :
    (cycloChar K σ : ℤ_[p]).toZModPow n = 1 := by
  rw [cycloChar, MonoidHom.comp_apply, cyclotomicCharacter.toZModPow]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact @Subsingleton.elim (ZMod 1) _ _ _
  refine (modularCyclotomicCharacter.unique _ _ _ ?_).symm
  intro t ht
  have hp1 : p ^ n ≠ 1 := (Nat.one_lt_pow hn.ne' hp.out.one_lt).ne'
  rw [ZMod.val_one'' hp1, pow_one]
  have ht' : (t : PadicAlgCl p) ^ p ^ n = 1 := by
    have := (mem_rootsOfUnity _ _).1 ht
    simpa using congrArg Units.val this
  exact h _ ht'

/- English proof (translation)
Rewrite using `[PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, cycloChar_toZModPow_eq_one K σ n h, sub_self]`.
-/
theorem norm_cycloChar_sub_one_le (σ : Gal(PadicAlgCl p/K)) (n : ℕ)
    (h : ∀ ζ : PadicAlgCl p, ζ ^ p ^ n = 1 → σ ζ = ζ) :
    ‖(cycloChar K σ : ℤ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    map_one, cycloChar_toZModPow_eq_one K σ n h, sub_self]

/- English proof (translation)
Use `Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)` and prove the remaining obligations. Rewrite using `[cycloChar_toZModPow_eq_one K σ n (h n), Units.val_one, map_one]`.
-/
theorem cycloChar_eq_one_of_forall (σ : Gal(PadicAlgCl p/K))
    (h : ∀ n : ℕ, ∀ ζ : PadicAlgCl p, ζ ^ p ^ n = 1 → σ ζ = ζ) : cycloChar K σ = 1 := by
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  rw [cycloChar_toZModPow_eq_one K σ n (h n), Units.val_one, map_one]

/- English proof (translation)
Introduce `hpow`. Establish `hm : cycloChar K σ ^ j.natAbs = 1`. Break down `Int.natAbs_eq j with hj' | hj'` into its components or cases. Rewrite `hpow` using `[hj', zpow_natCast]`. Conclude with `hpow`.

Rewrite `hpow` using `[hj', zpow_neg, inv_eq_one, zpow_natCast]`. Conclude with `hpow`. Use `set u : ℤ_[p] := ((cycloChar K σ : ℤ_[p]ˣ) : ℤ_[p])`. Use `set w : PadicAlgCl p := algebraMap ℚ_[p] (PadicAlgCl p) ((u - 1 : ℤ_[p]) : ℚ_[p])`. Establish `hw0 : w ≠ 0`.

Introduce `hw`. Rewrite `hw` using `[map_eq_zero, PadicInt.coe_eq_zero, sub_eq_zero]`. Conclude with `hne (Units.ext hw)`. Establish `hw : ‖w‖ < (p : ℝ)⁻¹`. Rewrite using `[norm_algebraMap', ← PadicInt.norm_def]`.

Use `(norm_cycloChar_sub_one_le K σ 2 h2).trans_lt ?_` and prove the remaining obligations. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.out.one_lt`. Rewrite using `[← zpow_neg_one]`. Conclude with `zpow_lt_zpow_right₀ hp1 (by norm_num)`. Apply `one_add_pow_ne_one hw0 hw (Int.natAbs_ne_zero.2 hj)` to reduce the goal to its premises.

Establish `h1 : (1 : PadicAlgCl p) + w = algebraMap ℚ_[p] (PadicAlgCl p) (u : ℚ_[p])`. Simplify using `[w, u]`. Rewrite using `[h1, ← map_pow, ← PadicInt.coe_pow, ← Units.val_pow_eq_pow_val, hm]`. Simplify using the standard rewrite rules.
-/
theorem cycloChar_zpow_ne_one (σ : Gal(PadicAlgCl p/K))
    (h2 : ∀ ζ : PadicAlgCl p, ζ ^ p ^ 2 = 1 → σ ζ = ζ) (hne : cycloChar K σ ≠ 1) {j : ℤ}
    (hj : j ≠ 0) : cycloChar K σ ^ j ≠ 1 := by
  intro hpow
  have hm : cycloChar K σ ^ j.natAbs = 1 := by
    rcases Int.natAbs_eq j with hj' | hj'
    · rw [hj', zpow_natCast] at hpow; exact hpow
    · rw [hj', zpow_neg, inv_eq_one, zpow_natCast] at hpow; exact hpow
  set u : ℤ_[p] := ((cycloChar K σ : ℤ_[p]ˣ) : ℤ_[p])
  set w : PadicAlgCl p := algebraMap ℚ_[p] (PadicAlgCl p) ((u - 1 : ℤ_[p]) : ℚ_[p])
  have hw0 : w ≠ 0 := by
    intro hw
    rw [map_eq_zero, PadicInt.coe_eq_zero, sub_eq_zero] at hw
    exact hne (Units.ext hw)
  have hw : ‖w‖ < (p : ℝ)⁻¹ := by
    rw [norm_algebraMap', ← PadicInt.norm_def]
    refine (norm_cycloChar_sub_one_le K σ 2 h2).trans_lt ?_
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    rw [← zpow_neg_one]
    exact zpow_lt_zpow_right₀ hp1 (by norm_num)
  apply one_add_pow_ne_one hw0 hw (Int.natAbs_ne_zero.2 hj)
  have h1 : (1 : PadicAlgCl p) + w = algebraMap ℚ_[p] (PadicAlgCl p) (u : ℚ_[p]) := by
    simp [w, u]
  rw [h1, ← map_pow, ← PadicInt.coe_pow, ← Units.val_pow_eq_pow_val, hm]
  simp

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[twistScalar, ← map_one (algebraMap ℚ_[p] ℂ_[p]), (algebraMap ℚ_[p] ℂ_[p]).injective.eq_iff]`. Establish `h' : ((cycloChar K σ ^ j : ℤ_[p]ˣ) : ℤ_[p]) = 1` using `Subtype.ext h`. Conclude with `cycloChar_zpow_ne_one K σ h2 hne hj (Units.ext h')`.
-/
theorem twistScalar_ne_one (σ : Gal(PadicAlgCl p/K))
    (h2 : ∀ ζ : PadicAlgCl p, ζ ^ p ^ 2 = 1 → σ ζ = ζ) (hne : cycloChar K σ ≠ 1) {j : ℤ}
    (hj : j ≠ 0) : twistScalar K j σ ≠ 1 := by
  intro h
  rw [twistScalar, ← map_one (algebraMap ℚ_[p] ℂ_[p]),
    (algebraMap ℚ_[p] ℂ_[p]).injective.eq_iff] at h
  have h' : ((cycloChar K σ ^ j : ℤ_[p]ˣ) : ℤ_[p]) = 1 := Subtype.ext h
  exact cycloChar_zpow_ne_one K σ h2 hne hj (Units.ext h')

variable [FiniteDimensional ℚ_[p] K]

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Use `set E : IntermediateField K (PadicAlgCl p) := extendScalars (le_cyclotomicLayer K n)`. Establish `hcyc : ∀ m, cycl p m ≤ cyclotomicLayer K n`. Introduce `m`.

Use `adjoin_le_iff.2 fun ζ hζ => ?_` and prove the remaining obligations. Establish `hζ' : ζ ^ p ^ m = 1` using `hζ`. Establish `hmem : ζ ∈ fixedField E.fixingSubgroup`. Rewrite using `[mem_fixedField_iff]`. Introduce `σ hσ`.

Establish `hσ' : ∀ y ∈ cyclotomicLayer K n, σ y = y` using `fun y hy => (mem_fixingSubgroup_iff _ _).1 hσ y hy`. Establish `h1` using `hcon σ hσ'`. Rewrite using `[cycloChar_spec K σ hζ', h1, Units.val_one, map_one]`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Simplify using `only [pow_zero, pow_one] at hζ'`.

Simplify using `[hζ']`. Establish `hp1 : p ^ m ≠ 1` using `(Nat.one_lt_pow hm.ne' hp.out.one_lt).ne'`. Rewrite using `[ZMod.val_one'' hp1, pow_one]`. Rewrite `hmem` using `[InfiniteGalois.fixedField_fixingSubgroup]`. Conclude with `hmem`.

Establish `hle` using `IntermediateField.finrank_le_of_le_right (hcyc (Module.finrank ℚ_[p] (cyclotomicLayer K n) + 1))`. Rewrite `hle` using `[finrank_cycl, Nat.totient_prime_pow_succ hp.out]`. Establish `h1 : Module.finrank ℚ_[p] (cyclotomicLayer K n) < p ^ Module.finrank ℚ_[p] (cyclotomicLayer K n)` using `Nat.lt_pow_self hp.out.one_lt`. Establish `h2 : 1 ≤ p - 1` using `by have := hp.out.two_le; omega`. Establish `h3 : p ^ Module.finrank ℚ_[p] (cyclotomicLayer K n) ≤ p ^ Module.finrank ℚ_[p] (cyclotomicLayer K n) * (p - 1)` using `Nat.le_mul_of_pos_right _ h2`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_gal_fix_cyclotomicLayer_cycloChar_ne_one (n : ℕ) :
    ∃ σ : Gal(PadicAlgCl p/K), (∀ y ∈ cyclotomicLayer K n, σ y = y) ∧ cycloChar K σ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  set E : IntermediateField K (PadicAlgCl p) := extendScalars (le_cyclotomicLayer K n)
  have hcyc : ∀ m, cycl p m ≤ cyclotomicLayer K n := by
    intro m
    refine adjoin_le_iff.2 fun ζ hζ => ?_
    have hζ' : ζ ^ p ^ m = 1 := hζ
    have hmem : ζ ∈ fixedField E.fixingSubgroup := by
      rw [mem_fixedField_iff]
      intro σ hσ
      have hσ' : ∀ y ∈ cyclotomicLayer K n, σ y = y := fun y hy =>
        (mem_fixingSubgroup_iff _ _).1 hσ y hy
      have h1 := hcon σ hσ'
      rw [cycloChar_spec K σ hζ', h1, Units.val_one, map_one]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp only [pow_zero, pow_one] at hζ'
        simp [hζ']
      · have hp1 : p ^ m ≠ 1 := (Nat.one_lt_pow hm.ne' hp.out.one_lt).ne'
        rw [ZMod.val_one'' hp1, pow_one]
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
    exact hmem
  have hle := IntermediateField.finrank_le_of_le_right (hcyc (Module.finrank ℚ_[p] (cyclotomicLayer K n) + 1))
  rw [finrank_cycl, Nat.totient_prime_pow_succ hp.out] at hle
  have h1 : Module.finrank ℚ_[p] (cyclotomicLayer K n) < p ^ Module.finrank ℚ_[p] (cyclotomicLayer K n) :=
    Nat.lt_pow_self hp.out.one_lt
  have h2 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
  have h3 : p ^ Module.finrank ℚ_[p] (cyclotomicLayer K n) ≤
      p ^ Module.finrank ℚ_[p] (cyclotomicLayer K n) * (p - 1) := Nat.le_mul_of_pos_right _ h2
  omega

end Character

section Invariants

noncomputable abbrev cyclotomicLimitGal : Subgroup Gal(PadicAlgCl p/K) :=
  (extendScalars ((le_cyclotomicLayer K 0).trans (cyclotomicLayer_le_cyclotomicLimit K 0))).fixingSubgroup

/- English proof (translation)
Use `cycloChar_eq_one_of_forall K σ fun n ζ hζ => ?_` and prove the remaining obligations. Establish `hmem : ζ ∈ cyclotomicLimit K` using `cyclotomicLayer_le_cyclotomicLimit K n (cycl_le_cyclotomicLayer K n (pow_eq_one_mem_cycl hζ))`. Conclude with `(mem_fixingSubgroup_iff _ _).1 hσ ζ hmem`.
-/
theorem cycloChar_eq_one_of_mem_cyclotomicLimitGal {σ : Gal(PadicAlgCl p/K)}
    (hσ : σ ∈ cyclotomicLimitGal K) : cycloChar K σ = 1 := by
  refine cycloChar_eq_one_of_forall K σ fun n ζ hζ => ?_
  have hmem : ζ ∈ cyclotomicLimit K :=
    cyclotomicLayer_le_cyclotomicLimit K n (cycl_le_cyclotomicLayer K n (pow_eq_one_mem_cycl hζ))
  exact (mem_fixingSubgroup_iff _ _).1 hσ ζ hmem

/- English proof (translation)
Establish `h` using `fixedPoints_closedSubgroup_eq_closure (cyclotomicLimitGal K) (InfiniteGalois.fixingSubgroup_isClosed _)`. Establish `hx' : x ∈ {x : ℂ_[p] | ∀ σ ∈ cyclotomicLimitGal K, σ • x = x}` using `hx`. Rewrite `hx'` using `[h, InfiniteGalois.fixedField_fixingSubgroup]`. Conclude with `hx'`.
-/
theorem mem_cyclotomicCompletion_of_forall_smul_eq {x : ℂ_[p]}
    (hx : ∀ σ ∈ cyclotomicLimitGal K, σ • x = x) : x ∈ cyclotomicCompletion K := by
  have h := fixedPoints_closedSubgroup_eq_closure (cyclotomicLimitGal K)
    (InfiniteGalois.fixingSubgroup_isClosed _)
  have hx' : x ∈ {x : ℂ_[p] | ∀ σ ∈ cyclotomicLimitGal K, σ • x = x} := hx
  rw [h, InfiniteGalois.fixedField_fixingSubgroup] at hx'
  exact hx'

variable [FiniteDimensional ℚ_[p] K]

/- English proof (translation)
Establish `hxc : x ∈ cyclotomicCompletion K`. Use `mem_cyclotomicCompletion_of_forall_smul_eq K fun σ hσ => ?_` and prove the remaining obligations. Establish `h1 : twistScalar K j σ = 1`. Simplify using `[twistScalar, cycloChar_eq_one_of_mem_cyclotomicLimitGal K hσ]`. Simplify `hx σ` using `[h1]`.

Establish `hR : ∀ n, stableIndex K ≤ n → tateTraceHat K n x = 0`. Introduce `n hn`. Establish `key : ∀ σ : Gal(PadicAlgCl p/K), tateTraceHat K n x = twistScalar K j σ * (σ • tateTraceHat K n x)`. Introduce `σ`. Establish `hc : twistScalar K j σ = ((algebraMap ℚ_[p] (PadicAlgCl p) (((cycloChar K σ ^ j : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) : PadicAlgCl p) : ℂ_[p])` using `rfl`.

Use `conv_lhs => rw [← hx σ]`. Rewrite using `[hc, tateTraceHat_mul (IntermediateField.algebraMap_mem _ _) (smul_mem_cyclotomicCompletion σ hxc), tateTraceHat_smul n σ hxc]`. Take `⟨σ, hσ, hne⟩` from `exists_gal_fix_cyclotomicLayer_cycloChar_ne_one K n`. Establish `h2 : ∀ ζ : PadicAlgCl p, ζ ^ p ^ 2 = 1 → σ ζ = ζ` using `fun ζ hζ => hσ ζ (cycl_le_cyclotomicLayer K n (cycl_mono (p := p) ((two_le_stableIndex K).trans hn) (pow_eq_one_mem_cycl hζ)))`. Take `⟨b, hb, hbx⟩` from `tateTraceHat_mem n hxc`.

Establish `hfix : σ • tateTraceHat K n x = tateTraceHat K n x`. Rewrite using `[← hbx, gal_smul_coe, hσ b hb]`. Establish `h3` using `key σ`. Rewrite `h3` using `[hfix]`. Establish `h4 : (twistScalar K j σ - 1) * tateTraceHat K n x = 0`.

Rewrite using `[sub_mul, one_mul, ← h3, sub_self]`. Conclude with `(mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 (twistScalar_ne_one K σ h2 hne hj))`. Use `set c := tateBound K`. Establish `hc0 : 0 ≤ c` using `tateBound_nonneg K`. Establish `hbound : ∀ ε > 0, ‖x‖ ≤ (1 + c) * ε`.

Introduce `ε hε`. Take `⟨_, ⟨y, hy, rfl⟩, hxy⟩` from `Metric.mem_closure_iff.1 hxc ε hε`. Take `⟨m, hm⟩` from `(mem_cyclotomicLimit K).1 hy`. Use `set m' := max m (stableIndex K)`. Establish `hym : y ∈ cyclotomicLayer K m'` using `cyclotomicLayer_mono K (le_max_left _ _) hm`.

Establish `hyc : (y : ℂ_[p]) ∈ cyclotomicCompletion K` using `coe_mem_closureInCp hy`. Establish `hsub : (y : ℂ_[p]) - x ∈ cyclotomicCompletion K` using `sub_mem_closureInCp hyc hxc`. Establish `h1 : tateTraceHat K m' (y : ℂ_[p]) = tateTraceHat K m' ((y : ℂ_[p]) - x) + tateTraceHat K m' x`. Rewrite using `[← tateTraceHat_add m' hsub hxc, sub_add_cancel]`. Rewrite `h1` using `[tateTraceHat_coe_of_mem hym, hR m' (le_max_right _ _), add_zero]`.

Establish `h2 : ‖(y : ℂ_[p])‖ ≤ c * ε`. Rewrite using `[h1]`. Use `(norm_tateTraceHat_le m' hsub).trans ?_` and prove the remaining obligations. Rewrite using `[← dist_eq_norm, dist_comm]`. Conclude with `mul_le_mul_of_nonneg_left hxy.le hc0`.

Combine the equalities or inequalities in the displayed calculation. Assume the negation of the conclusion as `hx0`. Establish `hpos : 0 < ‖x‖` using `norm_pos_iff.2 hx0`. Establish `h` using `hbound (‖x‖ / (2 * (1 + c))) (by positivity)`. Establish `h' : (1 + c) * (‖x‖ / (2 * (1 + c))) = ‖x‖ / 2`.

Clear the denominators using the available nonvanishing facts. Rewrite `h` using `[h']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_zero_of_forall_twistScalar_mul_smul_eq {j : ℤ} (hj : j ≠ 0) {x : ℂ_[p]}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), twistScalar K j σ * (σ • x) = x) : x = 0 := by

  have hxc : x ∈ cyclotomicCompletion K := by
    refine mem_cyclotomicCompletion_of_forall_smul_eq K fun σ hσ => ?_
    have h1 : twistScalar K j σ = 1 := by
      simp [twistScalar, cycloChar_eq_one_of_mem_cyclotomicLimitGal K hσ]
    simpa [h1] using hx σ

  have hR : ∀ n, stableIndex K ≤ n → tateTraceHat K n x = 0 := by
    intro n hn
    have key : ∀ σ : Gal(PadicAlgCl p/K),
        tateTraceHat K n x = twistScalar K j σ * (σ • tateTraceHat K n x) := by
      intro σ
      have hc : twistScalar K j σ =
          ((algebraMap ℚ_[p] (PadicAlgCl p) (((cycloChar K σ ^ j : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) :
            PadicAlgCl p) : ℂ_[p]) := rfl
      conv_lhs => rw [← hx σ]
      rw [hc, tateTraceHat_mul (IntermediateField.algebraMap_mem _ _) (smul_mem_cyclotomicCompletion σ hxc),
        tateTraceHat_smul n σ hxc]
    obtain ⟨σ, hσ, hne⟩ := exists_gal_fix_cyclotomicLayer_cycloChar_ne_one K n
    have h2 : ∀ ζ : PadicAlgCl p, ζ ^ p ^ 2 = 1 → σ ζ = ζ := fun ζ hζ =>
      hσ ζ (cycl_le_cyclotomicLayer K n (cycl_mono (p := p)
        ((two_le_stableIndex K).trans hn) (pow_eq_one_mem_cycl hζ)))
    obtain ⟨b, hb, hbx⟩ := tateTraceHat_mem n hxc
    have hfix : σ • tateTraceHat K n x = tateTraceHat K n x := by
      rw [← hbx, gal_smul_coe, hσ b hb]
    have h3 := key σ
    rw [hfix] at h3
    have h4 : (twistScalar K j σ - 1) * tateTraceHat K n x = 0 := by
      rw [sub_mul, one_mul, ← h3, sub_self]
    exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 (twistScalar_ne_one K σ h2 hne hj))

  set c := tateBound K
  have hc0 : 0 ≤ c := tateBound_nonneg K
  have hbound : ∀ ε > 0, ‖x‖ ≤ (1 + c) * ε := by
    intro ε hε
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := Metric.mem_closure_iff.1 hxc ε hε
    obtain ⟨m, hm⟩ := (mem_cyclotomicLimit K).1 hy
    set m' := max m (stableIndex K)
    have hym : y ∈ cyclotomicLayer K m' := cyclotomicLayer_mono K (le_max_left _ _) hm
    have hyc : (y : ℂ_[p]) ∈ cyclotomicCompletion K := coe_mem_closureInCp hy
    have hsub : (y : ℂ_[p]) - x ∈ cyclotomicCompletion K := sub_mem_closureInCp hyc hxc
    have h1 : tateTraceHat K m' (y : ℂ_[p]) =
        tateTraceHat K m' ((y : ℂ_[p]) - x) + tateTraceHat K m' x := by
      rw [← tateTraceHat_add m' hsub hxc, sub_add_cancel]
    rw [tateTraceHat_coe_of_mem hym, hR m' (le_max_right _ _), add_zero] at h1
    have h2 : ‖(y : ℂ_[p])‖ ≤ c * ε := by
      rw [h1]
      refine (norm_tateTraceHat_le m' hsub).trans ?_
      rw [← dist_eq_norm, dist_comm]
      exact mul_le_mul_of_nonneg_left hxy.le hc0
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - (y : ℂ_[p])‖ + ‖(y : ℂ_[p])‖ := norm_add_le _ _
      _ ≤ ε + c * ε := add_le_add (by rw [← dist_eq_norm]; exact hxy.le) h2
      _ = (1 + c) * ε := by ring
  by_contra hx0
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have h := hbound (‖x‖ / (2 * (1 + c))) (by positivity)
  have h' : (1 + c) * (‖x‖ / (2 * (1 + c))) = ‖x‖ / 2 := by
    field_simp
  rw [h'] at h
  linarith

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[ContRepresentation.mem_invariants, LinearMap.mem_range]`. Simplify using `only [cpTwistRep_apply, twistScalar_zero, one_mul, Algebra.linearMap_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Take `⟨k, hk⟩` from `exists_eq_coe_of_forall_smul_eq (K := K) h`. Conclude with `⟨k, hk⟩`. Introduce and unpack `⟨k, rfl⟩ σ`. Conclude with `gal_smul_algebraMap_intermediateField K σ k`.
-/
theorem cpTwistRep_invariants_zero :
    (cpTwistRep K 0).invariants = LinearMap.range (Algebra.linearMap K ℂ_[p]) := by
  ext x
  rw [ContRepresentation.mem_invariants, LinearMap.mem_range]
  simp only [cpTwistRep_apply, twistScalar_zero, one_mul, Algebra.linearMap_apply]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_eq_coe_of_forall_smul_eq (K := K) h
    exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩ σ
    exact gal_smul_algebraMap_intermediateField K σ k

/- English proof (translation)
Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Rewrite `hx` using `[ContRepresentation.mem_invariants]`. Conclude with `(Submodule.mem_bot K).2 (eq_zero_of_forall_twistScalar_mul_smul_eq K hj hx)`.
-/
theorem cpTwistRep_invariants_eq_bot {j : ℤ} (hj : j ≠ 0) : (cpTwistRep K j).invariants = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [ContRepresentation.mem_invariants] at hx
  exact (Submodule.mem_bot K).2 (eq_zero_of_forall_twistScalar_mul_smul_eq K hj hx)

noncomputable def continuousCohomologyZeroEquiv :
    continuousCohomology 0 (cpTwist K 0) ≃ₗ[K] K :=
  (ContinuousCohomology.zeroIso (cpTwist K 0)).toContinuousLinearEquiv.toLinearEquiv ≪≫ₗ
    LinearEquiv.ofEq _ _ (cpTwistRep_invariants_zero K) ≪≫ₗ
    (LinearEquiv.ofInjective (Algebra.linearMap K ℂ_[p])
      (FaithfulSMul.algebraMap_injective K ℂ_[p])).symm

end Invariants

end GroundTheory.PAdicHodge
