import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepNewton

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

/- English proof (translation)
Introduce `a b c d ha hd lam hlam m _ _ Λ l x y T i₀ h k hk w hw`. Take `⟨hOK, -, hθ, -, -, hl, -, -, -⟩` from `h`. Take `⟨hwsat, hwT, p, q, hq, hww⟩` from `hw`. Take `⟨τ, r, s, hτ1, hτ2, hs, hτsat⟩` from `rep_tau a b c d hOK Λ hθ hl`. Establish `hlp : Prime (l : ℤ)` using `Nat.prime_iff_prime_int.mp hl`.

Establish `hq0 : (q : ℂ) ≠ 0`. Establish `: q ≠ 0` using `by rintro rfl; exact hq (dvd_zero _)`. Conclude with `this` after adjusting the coercions. Establish `hs0 : (s : ℂ) ≠ 0`. Establish `: s ≠ 0` using `by rintro rfl; exact hs (dvd_zero _)`.

Conclude with `this` after adjusting the coercions. Use `set ε : ℂ := ((l ^ k * p : ℤ) : ℂ) / (q : ℂ) with hε`. Establish `hεc : conj ε = ε` using `by rw [hε, map_div₀, map_intCast, map_intCast]`. Establish `hξ : (1 - ε * τ) * conj (1 - ε * τ) = 1 - ε + ε ^ 2 * ((r : ℂ) / s)`. Rewrite using `[map_sub, map_one, map_mul, hεc]`.

Take the linear combination `(-ε) * hτ1 + ε ^ 2 * hτ2`. Use `⟨(1 - ε * τ) • w, ?_, ?_, p ^ 2 * (r * q - s * q + l ^ k * p * r), q ^ 3 * s, ?_, ?_⟩` and prove the remaining obligations. Establish `e : (1 - ε * τ) • w = w - ε • (τ • w)` using `by rw [sub_smul, one_smul, smul_smul]`. Rewrite using `[e, hε]`. Conclude with `rep_sat_sub l Λ hl hwsat (rep_sat_rat l Λ hl (hτsat w hwsat) _ _ hq)`.

Introduce `j hj`. Simplify using `[hwT j hj]`. Introduce `h`. Break down `hlp.dvd_mul.mp h with h | h` into its components or cases. Conclude with `hq (hlp.dvd_of_dvd_pow h)`.

Conclude with `hs h`. Rewrite using `[rep_H_smul, hξ, hww]`. Rewrite using `[hε]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem keyNewton : KeyNewton := by
  intro a b c d ha hd lam hlam m _ _ Λ l x y T i₀ h k hk w hw
  obtain ⟨hOK, -, hθ, -, -, hl, -, -, -⟩ := h
  obtain ⟨hwsat, hwT, p, q, hq, hww⟩ := hw
  obtain ⟨τ, r, s, hτ1, hτ2, hs, hτsat⟩ := rep_tau a b c d hOK Λ hθ hl
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hq0 : (q : ℂ) ≠ 0 := by
    have : q ≠ 0 := by rintro rfl; exact hq (dvd_zero _)
    exact_mod_cast this
  have hs0 : (s : ℂ) ≠ 0 := by
    have : s ≠ 0 := by rintro rfl; exact hs (dvd_zero _)
    exact_mod_cast this
  set ε : ℂ := ((l ^ k * p : ℤ) : ℂ) / (q : ℂ) with hε
  have hεc : conj ε = ε := by rw [hε, map_div₀, map_intCast, map_intCast]
  have hξ : (1 - ε * τ) * conj (1 - ε * τ) = 1 - ε + ε ^ 2 * ((r : ℂ) / s) := by
    rw [map_sub, map_one, map_mul, hεc]
    linear_combination (-ε) * hτ1 + ε ^ 2 * hτ2
  refine ⟨(1 - ε * τ) • w, ?_, ?_, p ^ 2 * (r * q - s * q + l ^ k * p * r), q ^ 3 * s, ?_, ?_⟩
  · have e : (1 - ε * τ) • w = w - ε • (τ • w) := by rw [sub_smul, one_smul, smul_smul]
    rw [e, hε]
    exact rep_sat_sub l Λ hl hwsat (rep_sat_rat l Λ hl (hτsat w hwsat) _ _ hq)
  · intro j hj; simp [hwT j hj]
  · intro h
    rcases hlp.dvd_mul.mp h with h | h
    · exact hq (hlp.dvd_of_dvd_pow h)
    · exact hs h
  · rw [rep_H_smul, hξ, hww]
    rw [hε]
    push_cast
    field_simp
    ring

end PI.UnitaryGroupMassFormula.UnimodLocStd
