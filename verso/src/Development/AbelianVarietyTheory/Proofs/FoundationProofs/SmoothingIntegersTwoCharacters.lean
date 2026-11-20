import Mathlib

namespace GlobalTheory

/- English proof (translation)
Take `⟨u₁, hu₁⟩` from `MulChar.ne_one_iff.1 h₁`. Take `⟨u₂, hu₂⟩` from `MulChar.ne_one_iff.1 h₂`. Distinguish the cases in `a : θ₂ (u₁ : ZMod N) = 1`. Distinguish the cases in `b : θ₁ (u₂ : ZMod N) = 1`. Use `⟨u₁ * u₂, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_mul, map_mul, b, mul_one]`. Conclude with `hu₁`. Rewrite using `[Units.val_mul, map_mul, a, one_mul]`. Conclude with `hu₂`. Conclude with `⟨u₂, b, hu₂⟩`.

Conclude with `⟨u₁, hu₁, a⟩`.
-/
theorem exists_unit_dirichletCharacter_ne_one_ne_one {N : ℕ} (θ₁ θ₂ : DirichletCharacter ℂ N)
    (h₁ : θ₁ ≠ 1) (h₂ : θ₂ ≠ 1) :
    ∃ u : (ZMod N)ˣ, θ₁ (u : ZMod N) ≠ 1 ∧ θ₂ (u : ZMod N) ≠ 1 := by
  obtain ⟨u₁, hu₁⟩ := MulChar.ne_one_iff.1 h₁
  obtain ⟨u₂, hu₂⟩ := MulChar.ne_one_iff.1 h₂
  by_cases a : θ₂ (u₁ : ZMod N) = 1
  · by_cases b : θ₁ (u₂ : ZMod N) = 1
    · refine ⟨u₁ * u₂, ?_, ?_⟩
      · rw [Units.val_mul, map_mul, b, mul_one]; exact hu₁
      · rw [Units.val_mul, map_mul, a, one_mul]; exact hu₂
    · exact ⟨u₂, b, hu₂⟩
  · exact ⟨u₁, hu₁, a⟩

/- English proof (translation)
Establish `hy1 : x ^ n ≠ 1`. Break down `hn with rfl | rfl` into its components or cases. Simplify using `using hx1`. Rewrite using `[zpow_neg_one]`. Conclude with `fun h => hx1 (inv_eq_one.1 h)`.

Establish `hyn : ‖x ^ n‖ = 1` using `by rw [norm_zpow, hx, one_zpow]`. Establish `hp0 : (p : ℂ) ≠ 0` using `by exact_mod_cast (show p ≠ 0 by omega)`. Introduce `h`. Break down `Nat.lt_or_ge e 2 with he2 | he2` into its components or cases. Establish `: e = 1` using `by omega`.

Substitute `this` using the available equality. Establish `h' : (p : ℂ) ^ 2 * x ^ n = (p : ℂ) ^ 2` using `h.symm`. Conclude with `hy1 ((mul_eq_left₀ (pow_ne_zero 2 hp0)).1 h')`. Establish `h2` using `congrArg norm h`. Rewrite `h2` using `[norm_mul, hyn, mul_one, norm_pow, norm_pow, Complex.norm_natCast]`.

Establish `hp' : (1 : ℝ) < p` using `by exact_mod_cast hp`. Use `pow_lt_pow_right₀ hp' (show 2 < e + 1 by omega)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sq_ne_pow_succ_mul_zpow {p e : ℕ} (hp : 1 < p) (he : 1 ≤ e) {x : ℂ} (hx : ‖x‖ = 1)
    (hx1 : x ≠ 1) {n : ℤ} (hn : n = 1 ∨ n = -1) :
    (p : ℂ) ^ 2 ≠ (p : ℂ) ^ (e + 1) * x ^ n := by
  have hy1 : x ^ n ≠ 1 := by
    rcases hn with rfl | rfl
    · simpa using hx1
    · rw [zpow_neg_one]; exact fun h => hx1 (inv_eq_one.1 h)
  have hyn : ‖x ^ n‖ = 1 := by rw [norm_zpow, hx, one_zpow]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  intro h
  rcases Nat.lt_or_ge e 2 with he2 | he2
  · have : e = 1 := by omega
    subst this
    have h' : (p : ℂ) ^ 2 * x ^ n = (p : ℂ) ^ 2 := h.symm
    exact hy1 ((mul_eq_left₀ (pow_ne_zero 2 hp0)).1 h')
  · have h2 := congrArg norm h
    rw [norm_mul, hyn, mul_one, norm_pow, norm_pow, Complex.norm_natCast] at h2
    have hp' : (1 : ℝ) < p := by exact_mod_cast hp
    have := pow_lt_pow_right₀ hp' (show 2 < e + 1 by omega)
    linarith

/- English proof (translation)
Introduce `N l e θ₁ θ₂ ψ hN hl hlN he h₁ h₂`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Use `haveI : NeZero l := ⟨hl.ne_zero⟩`. Use `haveI : NeZero (N * l) := ⟨Nat.mul_ne_zero hN.ne' hl.ne_zero⟩`. Establish `hcop : N.Coprime l` using `((Nat.Prime.coprime_iff_not_dvd hl).2 hlN).symm`.

Establish `hM : 0 < 6 * N * l` using `Nat.mul_pos (Nat.mul_pos (by norm_num) hN) hl.pos`. Take `⟨u, hu₁, hu₂⟩` from `exists_unit_dirichletCharacter_ne_one_ne_one θ₁ θ₂ h₁ h₂`. Take `⟨k, hkN, hkl⟩` from `Nat.chineseRemainder hcop (u : ZMod N).val 1`. Establish `hkN' : (k : ZMod N) = u`. Rewrite using `[(ZMod.natCast_eq_natCast_iff k _ N).2 hkN, ZMod.natCast_zmod_val]`.

Establish `hkl' : (k : ZMod l) = 1`. Rewrite using `[(ZMod.natCast_eq_natCast_iff k 1 l).2 hkl, Nat.cast_one]`. Establish `hk1 : k.Coprime N` using `(ZMod.isUnit_iff_coprime k N).1 (hkN' ▸ u.isUnit)`. Establish `hk2 : k.Coprime l` using `(ZMod.isUnit_iff_coprime k l).1 (hkl' ▸ isUnit_one)`. Establish `hunit : IsUnit (k : ZMod (N * l))` using `(ZMod.isUnit_iff_coprime k (N * l)).2 (Nat.Coprime.mul_right hk1 hk2)`.

Take `⟨p, hpgt, hp, hpk⟩` from `Nat.forall_exists_prime_gt_and_eq_mod hunit (6 * N * l)`. Establish `hpN : (p : ZMod N) = u`. Use `congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) hpk` as an intermediate fact. Rewrite `this` using `[map_natCast, map_natCast]`. Rewrite using `[this, hkN']`.

Establish `hpl : (p : ZMod l) = 1`. Use `congrArg (ZMod.castHom (dvd_mul_left l N) (ZMod l)) hpk` as an intermediate fact. Rewrite `this` using `[map_natCast, map_natCast]`. Rewrite using `[this, hkl']`. Establish `hpcop : p.Coprime (6 * N * l)` using `(Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hM hpgt)`.

Use `⟨6 * N * l + 1, p, by omega, hp.one_lt, ?_, hpcop, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[add_comm, Nat.coprime_add_self_left]`. Conclude with `Nat.coprime_one_left _`. Introduce `z hz h`. Establish `h2` using `congrArg norm h`.

Rewrite `h2` using `[norm_pow, Complex.norm_natCast, hz]`. Establish `hc' : (1 : ℝ) < ((6 * N * l + 1 : ℕ) : ℝ)` using `by exact_mod_cast (show 1 < 6 * N * l + 1 by omega)`. Use `one_lt_pow₀ hc' (show e ≠ 0 by omega)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `n₁ n₂ hn`.

Rewrite using `[hpl, map_one, one_zpow, mul_one, mul_one, hpN]`. Conclude with `⟨sq_ne_pow_succ_mul_zpow hp.one_lt he (DirichletCharacter.unit_norm_eq_one _ _) hu₁ hn, sq_ne_pow_succ_mul_zpow hp.one_lt he (DirichletCharacter.unit_norm_eq_one _ _) hu₂ hn⟩`.
-/
theorem smoothing_integers_two_characters : ∀ (N l e : ℕ) (θ₁ θ₂ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ l), 0 < N → l.Prime → ¬ l ∣ N → 1 ≤ e → θ₁ ≠ 1 → θ₂ ≠ 1 →
    ∃ c d : ℕ, 1 < c ∧ 1 < d ∧ c.Coprime (6 * N * l) ∧ d.Coprime (6 * N * l) ∧
      (∀ z : ℂ, ‖z‖ = 1 → (c : ℂ) ^ e ≠ z) ∧
      ∀ n₁ n₂ : ℤ, (n₁ = 1 ∨ n₁ = -1) →
        (d : ℂ) ^ 2 ≠ (d : ℂ) ^ (e + 1) * (θ₁ d ^ n₁ * ψ d ^ n₂) ∧
        (d : ℂ) ^ 2 ≠ (d : ℂ) ^ (e + 1) * (θ₂ d ^ n₁ * ψ d ^ n₂) := by
  intro N l e θ₁ θ₂ ψ hN hl hlN he h₁ h₂
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne_zero⟩
  haveI : NeZero (N * l) := ⟨Nat.mul_ne_zero hN.ne' hl.ne_zero⟩
  have hcop : N.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN).symm
  have hM : 0 < 6 * N * l := Nat.mul_pos (Nat.mul_pos (by norm_num) hN) hl.pos
  obtain ⟨u, hu₁, hu₂⟩ := exists_unit_dirichletCharacter_ne_one_ne_one θ₁ θ₂ h₁ h₂
  obtain ⟨k, hkN, hkl⟩ := Nat.chineseRemainder hcop (u : ZMod N).val 1
  have hkN' : (k : ZMod N) = u := by
    rw [(ZMod.natCast_eq_natCast_iff k _ N).2 hkN, ZMod.natCast_zmod_val]
  have hkl' : (k : ZMod l) = 1 := by
    rw [(ZMod.natCast_eq_natCast_iff k 1 l).2 hkl, Nat.cast_one]
  have hk1 : k.Coprime N := (ZMod.isUnit_iff_coprime k N).1 (hkN' ▸ u.isUnit)
  have hk2 : k.Coprime l := (ZMod.isUnit_iff_coprime k l).1 (hkl' ▸ isUnit_one)
  have hunit : IsUnit (k : ZMod (N * l)) :=
    (ZMod.isUnit_iff_coprime k (N * l)).2 (Nat.Coprime.mul_right hk1 hk2)
  obtain ⟨p, hpgt, hp, hpk⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit (6 * N * l)
  have hpN : (p : ZMod N) = u := by
    have := congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) hpk
    rw [map_natCast, map_natCast] at this
    rw [this, hkN']
  have hpl : (p : ZMod l) = 1 := by
    have := congrArg (ZMod.castHom (dvd_mul_left l N) (ZMod l)) hpk
    rw [map_natCast, map_natCast] at this
    rw [this, hkl']
  have hpcop : p.Coprime (6 * N * l) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hM hpgt)
  refine ⟨6 * N * l + 1, p, by omega, hp.one_lt, ?_, hpcop, ?_, ?_⟩
  · rw [add_comm, Nat.coprime_add_self_left]; exact Nat.coprime_one_left _
  · intro z hz h
    have h2 := congrArg norm h
    rw [norm_pow, Complex.norm_natCast, hz] at h2
    have hc' : (1 : ℝ) < ((6 * N * l + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < 6 * N * l + 1 by omega)
    have := one_lt_pow₀ hc' (show e ≠ 0 by omega)
    linarith
  · intro n₁ n₂ hn
    rw [hpl, map_one, one_zpow, mul_one, mul_one, hpN]
    exact ⟨sq_ne_pow_succ_mul_zpow hp.one_lt he (DirichletCharacter.unit_norm_eq_one _ _) hu₁ hn,
      sq_ne_pow_succ_mul_zpow hp.one_lt he (DirichletCharacter.unit_norm_eq_one _ _) hu₂ hn⟩

end GlobalTheory
