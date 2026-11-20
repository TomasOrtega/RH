import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.PowCong

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Rewrite using `[show (k : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (k : ℚ_[l]) from (map_intCast _ k).symm]`. Conclude with `PadicAlgCl.norm_extends l _`.
-/
theorem norm_intCast_eq (k : ℤ) : ‖(k : Qbar l)‖ = ‖(k : ℚ_[l])‖ := by
  rw [show (k : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (k : ℚ_[l]) from (map_intCast _ k).symm]
  exact PadicAlgCl.norm_extends l _

/- English proof (translation)
Use `norm_intCast_eq (l := l) (n : ℤ)` as an intermediate fact. Simplify using `using this`.
-/
theorem norm_natCast_eq (n : ℕ) : ‖(n : Qbar l)‖ = ‖(n : ℚ_[l])‖ := by
  have := norm_intCast_eq (l := l) (n : ℤ)
  simpa using this

/- English proof (translation)
Rewrite using `[norm_pow, norm_natCast_eq, Padic.norm_p, zpow_neg, zpow_natCast, inv_pow]`.
-/
theorem norm_l_pow (r : ℕ) : ‖((l : ℕ) : Qbar l) ^ r‖ = (l : ℝ) ^ (-(r : ℤ)) := by
  rw [norm_pow, norm_natCast_eq, Padic.norm_p, zpow_neg, zpow_natCast, inv_pow]

/- English proof (translation)
Rewrite using `[norm_intCast_eq, norm_l_pow]`. Conclude with `(Padic.norm_int_le_pow_iff_dvd k r).mpr h`.
-/
theorem norm_intCast_le_of_dvd (r : ℕ) (k : ℤ) (h : ((l : ℤ) ^ r) ∣ k) : ‖(k : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  rw [norm_intCast_eq, norm_l_pow]
  exact (Padic.norm_int_le_pow_iff_dvd k r).mpr h

/- English proof (translation)
Rewrite using `[norm_natCast_eq, Padic.norm_natCast_eq_one_iff]`. Conclude with `(Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h`.
-/
theorem norm_natCast_eq_one {n : ℕ} (h : ¬ l ∣ n) : ‖(n : Qbar l)‖ = 1 := by
  rw [norm_natCast_eq, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h

/- English proof (translation)
Establish `hcong : ((l : ℤ) ^ r) ∣ (((a ^ e : ℕ) : ℤ) - ((b ^ e : ℕ) : ℤ))`. Establish `h1` using `(Nat.mod_modEq a (l ^ r)).pow e`. Establish `h2` using `(Nat.modEq_iff_dvd.mp h1)`. Rewrite using `[hb]`. Move the coercions through the operations in `at h2 ⊢`.

Conclude with `h2`. Establish `hsub : ‖(a : Qbar l) ^ e - (b : Qbar l) ^ e‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖`. Use `norm_intCast_le_of_dvd (l := l) r _ hcong` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.

Use `⟨?_, hsub⟩` and prove the remaining obligations. Establish `hna : ‖(a : Qbar l)‖ = 1` using `norm_natCast_eq_one ha`. Break down `Nat.eq_zero_or_pos r with hr | hr` into its components or cases. Substitute `hr` using the available equality. Establish `hb0 : b = 0` using `by rw [hb, pow_zero, Nat.mod_one]`.

Substitute `hb0` using the available equality. Break down `Nat.eq_zero_or_pos e with he | he` into its components or cases. Substitute `he` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Nat.cast_zero, zero_pow he.ne', inv_zero, sub_zero, norm_inv, norm_pow, hna]`.

Simplify using the standard rewrite rules. Establish `hnb : ‖(b : Qbar l)‖ = 1` using `norm_natCast_eq_one (hb' hr)`. Establish `ha0 : ((a : Qbar l) ^ e) ≠ 0`. Introduce `h`. Use `congrArg norm h` as an intermediate fact.

Rewrite `this` using `[norm_pow, hna]`. Simplify using `at this`. Establish `hb0 : ((b : Qbar l) ^ e) ≠ 0`. Introduce `h`. Use `congrArg norm h` as an intermediate fact.

Rewrite `this` using `[norm_pow, hnb]`. Simplify using `at this`. Rewrite using `[inv_sub_inv ha0 hb0, norm_div, norm_mul, norm_pow, norm_pow, hna, hnb, one_pow, mul_one, div_one, norm_sub_rev]`. Conclude with `hsub`.
-/
theorem key (r e a b : ℕ) (ha : ¬ l ∣ a) (hb : b = a % l ^ r) (hb' : 1 ≤ r → ¬ l ∣ b) :
    ‖((a : Qbar l) ^ e)⁻¹ - ((b : Qbar l) ^ e)⁻¹‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ ∧
      ‖(a : Qbar l) ^ e - (b : Qbar l) ^ e‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  have hcong : ((l : ℤ) ^ r) ∣ (((a ^ e : ℕ) : ℤ) - ((b ^ e : ℕ) : ℤ)) := by
    have h1 := (Nat.mod_modEq a (l ^ r)).pow e
    have h2 := (Nat.modEq_iff_dvd.mp h1)
    rw [hb]
    push_cast at h2 ⊢
    exact h2
  have hsub : ‖(a : Qbar l) ^ e - (b : Qbar l) ^ e‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
    have := norm_intCast_le_of_dvd (l := l) r _ hcong
    push_cast at this
    exact this
  refine ⟨?_, hsub⟩
  have hna : ‖(a : Qbar l)‖ = 1 := norm_natCast_eq_one ha
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hb0 : b = 0 := by rw [hb, pow_zero, Nat.mod_one]
    subst hb0
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he; simp
    · rw [Nat.cast_zero, zero_pow he.ne', inv_zero, sub_zero, norm_inv, norm_pow, hna]
      simp
  · have hnb : ‖(b : Qbar l)‖ = 1 := norm_natCast_eq_one (hb' hr)
    have ha0 : ((a : Qbar l) ^ e) ≠ 0 := by
      intro h; have := congrArg norm h; rw [norm_pow, hna] at this; simp at this
    have hb0 : ((b : Qbar l) ^ e) ≠ 0 := by
      intro h; have := congrArg norm h; rw [norm_pow, hnb] at this; simp at this
    rw [inv_sub_inv ha0 hb0, norm_div, norm_mul, norm_pow, norm_pow, hna, hnb, one_pow, mul_one, div_one,
      norm_sub_rev]
    exact hsub

/- English proof (translation)
Introduce `l hl e r x`. Establish `hp : l.Prime` using `hl.out`. Use `haveI : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩`. Establish `notdvd : ∀ {k : ℕ}, 1 ≤ k → (u : (ZMod (l ^ k))ˣ) → ¬ l ∣ (u : ZMod (l ^ k)).val`. Introduce `k hk u hd`.

Establish `hc` using `ZMod.val_coe_unit_coprime u`. Establish `: l ∣ Nat.gcd (u : ZMod (l ^ k)).val (l ^ k)` using `Nat.dvd_gcd hd (dvd_pow_self l (by omega))`. Rewrite `this` using `[hc]`. Conclude with `hp.one_lt.ne' (Nat.dvd_one.mp this)`. Use `key (l := l) r e _ _ (notdvd (by omega) x) ?_ (fun hr => notdvd hr _)` and prove the remaining obligations.

Rewrite using `[Units.coe_map]`. Simplify using `only [MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, ZMod.castHom_apply]`. Rewrite using `[ZMod.cast_eq_val, ZMod.val_natCast]`.
-/
theorem powCong : ∀ (l : ℕ) [Fact l.Prime] (e r : ℕ) (x : (ZMod (l ^ (r + 1)))ˣ), ‖(((x : ZMod (l ^ (r + 1))).val : Qbar l) ^ e)⁻¹ - (((((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : Qbar l) ^ e)⁻¹‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ ∧ ‖((x : ZMod (l ^ (r + 1))).val : Qbar l) ^ e - ((((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : Qbar l) ^ e‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  intro l hl e r x
  have hp : l.Prime := hl.out
  haveI : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have notdvd : ∀ {k : ℕ}, 1 ≤ k → (u : (ZMod (l ^ k))ˣ) → ¬ l ∣ (u : ZMod (l ^ k)).val := by
    intro k hk u hd
    have hc := ZMod.val_coe_unit_coprime u
    have : l ∣ Nat.gcd (u : ZMod (l ^ k)).val (l ^ k) := Nat.dvd_gcd hd (dvd_pow_self l (by omega))
    rw [hc] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  refine key (l := l) r e _ _ (notdvd (by omega) x) ?_ (fun hr => notdvd hr _)
  rw [Units.coe_map]
  simp only [MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, ZMod.castHom_apply]
  rw [ZMod.cast_eq_val, ZMod.val_natCast]

end GlobalTheory.PowCong
