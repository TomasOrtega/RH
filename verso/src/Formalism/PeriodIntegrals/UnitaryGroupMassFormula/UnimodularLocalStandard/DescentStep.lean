import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.IsKTheta

noncomputable section
open scoped ComplexConjugate
open Polynomial

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

/- English proof (translation)
Use `Fact.mk hp` as an intermediate fact. Establish `hA' : (A : ZMod p) ≠ 0` using `by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]`. Establish `hB' : (B : ZMod p) ≠ 0` using `by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]`. Establish `hf : (C (A : ZMod p) * X ^ 2 - C (E : ZMod p)).degree = 2`. Rewrite using `[degree_sub_C (by rw [degree_C_mul_X_pow 2 hA']; norm_num), degree_C_mul_X_pow 2 hA']`.

Both sides reduce to the same expression. Establish `hg : (C (B : ZMod p) * X ^ 2).degree = 2`. Rewrite using `[degree_C_mul_X_pow 2 hB']`. Both sides reduce to the same expression. Take `⟨x, y, hxy⟩` from `FiniteField.exists_root_sum_quadratic hf hg (by rw [ZMod.card]; exact hodd)`.

Use `⟨(x.val : ℤ), (y.val : ℤ), ?_⟩` and prove the remaining obligations. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Rewrite using `[ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]`. Simplify using `only [eval_sub, eval_mul, eval_C, eval_pow, eval_X] at hxy`.

Take the linear combination `hxy`.
-/
lemma pigeon {p : ℕ} (hp : p.Prime) (hodd : p % 2 = 1) (A B E : ℤ) (hA : ¬ (p : ℤ) ∣ A)
    (hB : ¬ (p : ℤ) ∣ B) : ∃ s t : ℤ, (p : ℤ) ∣ s ^ 2 * A + t ^ 2 * B - E := by
  have := Fact.mk hp
  have hA' : (A : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hB' : (B : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hf : (C (A : ZMod p) * X ^ 2 - C (E : ZMod p)).degree = 2 := by
    rw [degree_sub_C (by rw [degree_C_mul_X_pow 2 hA']; norm_num), degree_C_mul_X_pow 2 hA']
    rfl
  have hg : (C (B : ZMod p) * X ^ 2).degree = 2 := by
    rw [degree_C_mul_X_pow 2 hB']
    rfl
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg (by rw [ZMod.card]; exact hodd)
  refine ⟨(x.val : ℤ), (y.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X] at hxy
  linear_combination hxy

variable {a : ℕ} {b c : ℤ} {d : ℕ}

/- English proof (translation)
Take `⟨h4, -, h8, hdp⟩` from `hok`. Establish `hD : Prime (d : ℤ)` using `Nat.prime_iff_prime_int.mp hdp`. Establish `hD0 : (d : ℤ) ≠ 0` using `hD.ne_zero`. Establish `hD2 : ¬ (d : ℤ) ∣ 2`. Introduce `h`.

Establish `h' : d ∣ 2` using `by exact_mod_cast h`. Use `Nat.le_of_dvd (by norm_num) h'` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `set N := P ^ 2 + P * Q * b + Q ^ 2 * (a * c) with hNdef`. Establish `hcop : IsCoprime ((d : ℤ) ^ 2) q` using `IsCoprime.pow_left ((Irreducible.coprime_iff_not_dvd hD.irreducible).mpr hq)`.

Establish `hdN : (d : ℤ) ^ 2 ∣ N`. Apply `hcop.dvd_of_dvd_mul_right` to reduce the goal to its premises. Rewrite using `[← hM]`. Conclude with `Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hr 2) _`. Establish `hid : 4 * N = (2 * P + b * Q) ^ 2 + d * Q ^ 2`.

Rewrite using `[hNdef]`. Take the linear combination `Q ^ 2 * h4`. Establish `hX : (d : ℤ) ∣ 2 * P + b * Q`. Apply `hD.dvd_of_dvd_pow (n := 2)` to reduce the goal to its premises. Establish `: (2 * P + b * Q) ^ 2 = 4 * N - d * Q ^ 2` using `by rw [hid]; ring`.

Rewrite using `[this]`. Conclude with `dvd_sub (Dvd.dvd.mul_left (dvd_trans (dvd_pow_self _ two_ne_zero) hdN) _) (dvd_mul_right _ _)`. Establish `hQ2 : (d : ℤ) ∣ Q ^ 2`. Establish `h1 : (d : ℤ) ^ 2 ∣ d * Q ^ 2`. Establish `: (d : ℤ) * Q ^ 2 = 4 * N - (2 * P + b * Q) ^ 2` using `by rw [hid]; ring`.

Rewrite using `[this]`. Conclude with `dvd_sub (Dvd.dvd.mul_left hdN _) (pow_dvd_pow_of_dvd hX 2)`. Rewrite `h1` using `[pow_two]`. Conclude with `(mul_dvd_mul_iff_left hD0).mp h1`. Establish `hQ : (d : ℤ) ∣ Q` using `hD.dvd_of_dvd_pow hQ2`.

Establish `h2P : (d : ℤ) ∣ 2 * P`. Establish `: 2 * P = (2 * P + b * Q) - b * Q` using `by ring`. Rewrite using `[this]`. Conclude with `dvd_sub hX (Dvd.dvd.mul_left hQ _)`. Use `⟨?_, hQ⟩` and prove the remaining obligations.

Break down `hD.dvd_or_dvd h2P with h | h` into its components or cases. Conclude with `absurd h hD2`. Conclude with `h`.
-/
lemma descent_step (hok : CmOK a b c d) {P Q r p q : ℤ} (hr : (d : ℤ) ∣ r) (hp : ¬ (d : ℤ) ∣ p)
    (hq : ¬ (d : ℤ) ∣ q) (hM : r ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q) :
    (d : ℤ) ∣ P ∧ (d : ℤ) ∣ Q := by
  obtain ⟨h4, -, h8, hdp⟩ := hok
  have hD : Prime (d : ℤ) := Nat.prime_iff_prime_int.mp hdp
  have hD0 : (d : ℤ) ≠ 0 := hD.ne_zero
  have hD2 : ¬ (d : ℤ) ∣ 2 := by
    intro h
    have h' : d ∣ 2 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  set N := P ^ 2 + P * Q * b + Q ^ 2 * (a * c) with hNdef
  have hcop : IsCoprime ((d : ℤ) ^ 2) q :=
    IsCoprime.pow_left ((Irreducible.coprime_iff_not_dvd hD.irreducible).mpr hq)
  have hdN : (d : ℤ) ^ 2 ∣ N := by
    apply hcop.dvd_of_dvd_mul_right
    rw [← hM]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hr 2) _
  have hid : 4 * N = (2 * P + b * Q) ^ 2 + d * Q ^ 2 := by
    rw [hNdef]
    linear_combination Q ^ 2 * h4
  have hX : (d : ℤ) ∣ 2 * P + b * Q := by
    apply hD.dvd_of_dvd_pow (n := 2)
    have : (2 * P + b * Q) ^ 2 = 4 * N - d * Q ^ 2 := by rw [hid]; ring
    rw [this]
    exact dvd_sub (Dvd.dvd.mul_left (dvd_trans (dvd_pow_self _ two_ne_zero) hdN) _) (dvd_mul_right _ _)
  have hQ2 : (d : ℤ) ∣ Q ^ 2 := by
    have h1 : (d : ℤ) ^ 2 ∣ d * Q ^ 2 := by
      have : (d : ℤ) * Q ^ 2 = 4 * N - (2 * P + b * Q) ^ 2 := by rw [hid]; ring
      rw [this]
      exact dvd_sub (Dvd.dvd.mul_left hdN _) (pow_dvd_pow_of_dvd hX 2)
    rw [pow_two] at h1
    exact (mul_dvd_mul_iff_left hD0).mp h1
  have hQ : (d : ℤ) ∣ Q := hD.dvd_of_dvd_pow hQ2
  have h2P : (d : ℤ) ∣ 2 * P := by
    have : 2 * P = (2 * P + b * Q) - b * Q := by ring
    rw [this]
    exact dvd_sub hX (Dvd.dvd.mul_left hQ _)
  refine ⟨?_, hQ⟩
  rcases hD.dvd_or_dvd h2P with h | h
  · exact absurd h hD2
  · exact h

/- English proof (translation)
Take `⟨h4, ha, h8, hdp⟩` from `hok`. Establish `hD : Prime (d : ℤ)` using `Nat.prime_iff_prime_int.mp hdp`. Establish `hD0 : (d : ℤ) ≠ 0` using `hD.ne_zero`. Establish `hD2 : ¬ (d : ℤ) ∣ 2`. Introduce `h`.

Establish `h' : d ∣ 2` using `by exact_mod_cast h`. Use `Nat.le_of_dvd (by norm_num) h'` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hq0 : q ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hq (dvd_zero _)`. Establish `hθ : cmTheta b d * (b - cmTheta b d) = (a : ℂ) * c`. Establish `hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules.

Establish `h4' : (4 * a * c : ℂ) = b ^ 2 + d` using `by exact_mod_cast h4`. Unfold `cmTheta`. Take the linear combination `(-(((Real.sqrt d : ℝ) : ℂ) ^ 2) / 4) * Complex.I_sq + (1 / 4 : ℂ) * hs + (-1 / 4 : ℂ) * h4'`. Establish `rel : ∀ P Q r : ℤ, (r : ℂ) * γ = P + Q * cmTheta b d → r ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q`. Introduce `P Q r hr`.

Establish `h1 : (r : ℂ) * γ * conj ((r : ℂ) * γ) = r ^ 2 * ((p : ℂ) / q)`. Rewrite using `[map_mul, map_intCast, ← hN]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (r : ℂ) * γ * conj ((r : ℂ) * γ) = P ^ 2 + P * Q * b + Q ^ 2 * (a * c)`. Rewrite using `[hr, map_add, map_mul, map_intCast, map_intCast, theta_conj]`.

Take the linear combination `(Q : ℂ) ^ 2 * hθ`. Establish `hq0' : (q : ℂ) ≠ 0` using `by exact_mod_cast hq0`. Establish `hC : (r : ℂ) ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q`. Rewrite using `[← h2, h1]`. Clear the denominators using the available nonvanishing facts.

Conclude with `hC` after adjusting the coercions. Establish `main : ∀ n : ℕ, ∀ P Q r : ℤ, r.natAbs = n → r ≠ 0 → r ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q → ∃ s : ℤ, (d : ℤ) ∣ s ^ 2 * q - p`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`.

Introduce `P Q r hn hr0 hM`. Distinguish the cases in `hdr : (d : ℤ) ∣ r`. Take `⟨hP, hQ⟩` from `descent_step ⟨h4, ha, h8, hdp⟩ hdr hp hq hM`. Take `⟨P', rfl⟩` from `hP`. Take `⟨Q', rfl⟩` from `hQ`.

Take `⟨r', rfl⟩` from `hdr`. Establish `hr' : r' ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hr0`. Establish `hM' : r' ^ 2 * p = (P' ^ 2 + P' * Q' * b + Q' ^ 2 * (a * c)) * q`.

Establish `hd2 : ((d : ℤ) ^ 2) ≠ 0` using `pow_ne_zero 2 hD0`. Apply `mul_left_cancel₀ hd2` to reduce the goal to its premises. Take the linear combination `hM`. Use `ih r'.natAbs ?_ P' Q' r' rfl hr' hM'` and prove the remaining obligations. Rewrite using `[← hn, Int.natAbs_mul]`.

Establish `h1 : 1 < (d : ℤ).natAbs`. Use `hdp.two_le` as an intermediate fact. Simplify using `only [Int.natAbs_natCast]`. Use linear arithmetic over natural numbers and integers. Establish `h2 : 0 < r'.natAbs` using `Int.natAbs_pos.mpr hr'`.

Use the polynomial consequences of the given equalities and inequalities. Use `Fact.mk hdp` as an intermediate fact. Establish `hkey : (2 * r) ^ 2 * p = (2 * P + b * Q) ^ 2 * q + d * (Q ^ 2 * q)`. Take the linear combination `4 * hM + q * Q ^ 2 * h4`. Establish `h2r : ((2 * r : ℤ) : ZMod d) ≠ 0`.

Rewrite using `[Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]`. Introduce `h`. Break down `hD.dvd_or_dvd h with h | h` into its components or cases. Conclude with `hD2 h`. Conclude with `hdr h`.

Use `⟨((((2 * P + b * Q : ℤ) : ZMod d) * ((2 * r : ℤ) : ZMod d)⁻¹).val : ℤ), ?_⟩` and prove the remaining obligations. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Establish `hk` using `congrArg (Int.cast : ℤ → ZMod d) hkey`. Move the coercions through the operations in `at hk h2r ⊢`. Rewrite `*` using `[ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, add_zero]`.

Establish `hinv : (2 * (r : ZMod d))⁻¹ ^ 2 * (2 * (r : ZMod d)) ^ 2 = 1`. Rewrite using `[← mul_pow, inv_mul_cancel₀ h2r, one_pow]`. Take the linear combination `(-((2 * (r : ZMod d))⁻¹ ^ 2)) * hk + (p : ZMod d) * hinv`. Take `⟨P, Q, r, hr0, hr⟩` from `hγ`. Conclude with `main r.natAbs P Q r rfl hr0 (rel P Q r hr)`.
-/
lemma norm_square (hok : CmOK a b c d) {γ : ℂ} (hγ : IsK b d γ) {p q : ℤ} (hp : ¬ (d : ℤ) ∣ p)
    (hq : ¬ (d : ℤ) ∣ q) (hN : γ * conj γ = (p : ℂ) / q) : ∃ s : ℤ, (d : ℤ) ∣ s ^ 2 * q - p := by
  obtain ⟨h4, ha, h8, hdp⟩ := hok
  have hD : Prime (d : ℤ) := Nat.prime_iff_prime_int.mp hdp
  have hD0 : (d : ℤ) ≠ 0 := hD.ne_zero
  have hD2 : ¬ (d : ℤ) ∣ 2 := by
    intro h
    have h' : d ∣ 2 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hq (dvd_zero _)
  have hθ : cmTheta b d * (b - cmTheta b d) = (a : ℂ) * c := by
    have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp
    have h4' : (4 * a * c : ℂ) = b ^ 2 + d := by exact_mod_cast h4
    unfold cmTheta
    linear_combination (-(((Real.sqrt d : ℝ) : ℂ) ^ 2) / 4) * Complex.I_sq + (1 / 4 : ℂ) * hs +
      (-1 / 4 : ℂ) * h4'

  have rel : ∀ P Q r : ℤ, (r : ℂ) * γ = P + Q * cmTheta b d →
      r ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q := by
    intro P Q r hr
    have h1 : (r : ℂ) * γ * conj ((r : ℂ) * γ) = r ^ 2 * ((p : ℂ) / q) := by
      rw [map_mul, map_intCast, ← hN]
      ring
    have h2 : (r : ℂ) * γ * conj ((r : ℂ) * γ) = P ^ 2 + P * Q * b + Q ^ 2 * (a * c) := by
      rw [hr, map_add, map_mul, map_intCast, map_intCast, theta_conj]
      linear_combination (Q : ℂ) ^ 2 * hθ
    have hq0' : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
    have hC : (r : ℂ) ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q := by
      rw [← h2, h1]
      field_simp
    exact_mod_cast hC

  have main : ∀ n : ℕ, ∀ P Q r : ℤ, r.natAbs = n → r ≠ 0 →
      r ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q → ∃ s : ℤ, (d : ℤ) ∣ s ^ 2 * q - p := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P Q r hn hr0 hM
      by_cases hdr : (d : ℤ) ∣ r
      · obtain ⟨hP, hQ⟩ := descent_step ⟨h4, ha, h8, hdp⟩ hdr hp hq hM
        obtain ⟨P', rfl⟩ := hP
        obtain ⟨Q', rfl⟩ := hQ
        obtain ⟨r', rfl⟩ := hdr
        have hr' : r' ≠ 0 := by
          rintro rfl
          simp at hr0
        have hM' : r' ^ 2 * p = (P' ^ 2 + P' * Q' * b + Q' ^ 2 * (a * c)) * q := by
          have hd2 : ((d : ℤ) ^ 2) ≠ 0 := pow_ne_zero 2 hD0
          apply mul_left_cancel₀ hd2
          linear_combination hM
        refine ih r'.natAbs ?_ P' Q' r' rfl hr' hM'
        rw [← hn, Int.natAbs_mul]
        have h1 : 1 < (d : ℤ).natAbs := by
          have := hdp.two_le
          simp only [Int.natAbs_natCast]
          omega
        have h2 : 0 < r'.natAbs := Int.natAbs_pos.mpr hr'
        nlinarith
      · have := Fact.mk hdp
        have hkey : (2 * r) ^ 2 * p = (2 * P + b * Q) ^ 2 * q + d * (Q ^ 2 * q) := by
          linear_combination 4 * hM + q * Q ^ 2 * h4
        have h2r : ((2 * r : ℤ) : ZMod d) ≠ 0 := by
          rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
          intro h
          rcases hD.dvd_or_dvd h with h | h
          · exact hD2 h
          · exact hdr h
        refine ⟨((((2 * P + b * Q : ℤ) : ZMod d) * ((2 * r : ℤ) : ZMod d)⁻¹).val : ℤ), ?_⟩
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        have hk := congrArg (Int.cast : ℤ → ZMod d) hkey
        push_cast at hk h2r ⊢
        rw [ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, add_zero] at *
        have hinv : (2 * (r : ZMod d))⁻¹ ^ 2 * (2 * (r : ZMod d)) ^ 2 = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ h2r, one_pow]
        linear_combination (-((2 * (r : ZMod d))⁻¹ ^ 2)) * hk + (p : ZMod d) * hinv
  obtain ⟨P, Q, r, hr0, hr⟩ := hγ
  exact main r.natAbs P Q r rfl hr0 (rel P Q r hr)

end PI.UnitaryGroupMassFormula.UnimodLocStd
