import Development.AutomorphicArithmetic.CharacterBoxes.HalfPlane

open Complex

namespace Claim

/- English proof (authored)
The prime p exceeds 1, and Re(s) is positive, so the norm of p^(−s) is p^(−Re(s)) < 1. The norm of the character value is at most 1, hence the norm of their product is strictly below 1. The product cannot equal 1, which proves the Euler factor is nonzero.
-/
theorem factor_ne_zero {M : ℕ} (ψ : DirichletCharacter ℂ M) {s : ℂ} (hs : 0 < s.re) (p : ℕ)
    (hp : p.Prime) : (1 : ℂ) - ψ p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : ψ p * (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hn : ‖ψ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖ψ p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ := by
          gcongr; exact ψ.norm_le_one _
      _ < 1 := by rw [one_mul]; exact hpow
  rw [h1, norm_one] at hn
  exact lt_irrefl _ hn

/- English proof (authored)
The change-of-level formula expresses the original L-value as the primitive L-value times a product of Euler factors. Here s is distinct from 1 because Re(s) < 1. Each Euler factor is nonzero since Re(s) > 0 makes the term subtracted from 1 have absolute value less than 1. The product can therefore vanish only through the primitive L-value.
-/
theorem prim_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (h : DirichletCharacter.LFunction χ s = 0) :
    DirichletCharacter.LFunction χ.primitiveCharacter s = 0 := by
  have hs : s ≠ 1 := fun e => by rw [e, Complex.one_re] at hs1; exact lt_irrefl _ hs1
  have key := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level
    χ.primitiveCharacter (Or.inr hs)
  rw [χ.changeLevel_primitiveCharacter, h] at key
  rcases mul_eq_zero.mp key.symm with h' | h'
  · exact h'
  · obtain ⟨p, hp, hp0⟩ := Finset.prod_eq_zero_iff.mp h'
    exact absurd hp0 (factor_ne_zero _ hs0 p (Nat.prime_of_mem_primeFactors hp))

/- English proof (authored)
Distinguish even and odd characters. Their gamma factors are Γℝ(s) and Γℝ(s + 1), respectively. Positive real part of s implies positive real part of both arguments, so the factors are nonzero.
-/
theorem gamma_ne_zero {M : ℕ} [NeZero M] (φ : DirichletCharacter ℂ M) {t : ℂ} (ht : 0 < t.re) :
    DirichletCharacter.gammaFactor φ t ≠ 0 := by
  rcases φ.even_or_odd with hφ | hφ
  · rw [hφ.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos ht
  · rw [hφ.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by rw [Complex.add_re, Complex.one_re]; linarith)

/- English proof (authored)
The gamma factor is nonzero at s, so the zero of the ordinary L-function gives a zero of the completed L-function. The inverse character is primitive by invariance of the conductor under inversion. Its functional equation transfers the completed zero to 1 − s. Since 1 − s is distinct from zero, the expression for the ordinary L-function in terms of the completed one gives the desired zero.
-/
theorem prim_reflect {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) (hψ : ψ.IsPrimitive) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (h : DirichletCharacter.LFunction ψ s = 0) :
    DirichletCharacter.LFunction ψ⁻¹ (1 - s) = 0 := by
  have hs0' : s ≠ 0 := fun e => by rw [e, Complex.zero_re] at hs0; exact lt_irrefl _ hs0
  have ht0 : 0 < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have ht0' : 1 - s ≠ 0 := fun e => by rw [e, Complex.zero_re] at ht0; exact lt_irrefl _ ht0
  have hc : DirichletCharacter.completedLFunction ψ s = 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ s (Or.inl hs0'),
      div_eq_zero_iff] at h
    exact h.resolve_right (gamma_ne_zero ψ hs0)
  have hψ' : (ψ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hψ
  have fe := hψ'.completedLFunction_one_sub s
  rw [inv_inv, hc, mul_zero] at fe
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ⁻¹ (1 - s) (Or.inl ht0'), fe,
    zero_div]

/- English proof (authored)
A zero above the critical line in real part contradicts right half-plane nonvanishing. For a zero below the critical line, first pass to the primitive character using the change-of-level formula. Its functional equation gives a zero at 1 − s for the inverse character. The reflected point has real part greater than 1/2 and is distinct from 1 because Re(s) > 0. This contradicts the same nonvanishing hypothesis, leaving Re(s) = 1/2.
-/
theorem strip (h : HalfPlane) : Strip := by
  unfold HalfPlane at h
  intro N _ χ s hs0 hs1 hz
  have hs : s ≠ 1 := fun e => by rw [e, Complex.one_re] at hs1; exact lt_irrefl _ hs1
  have hs0' : s ≠ 0 := fun e => by rw [e, Complex.zero_re] at hs0; exact lt_irrefl _ hs0
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hp := prim_zero χ hs0 hs1 hz
    have hr := prim_reflect χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hs0 hs1 hp
    have ht : (1 : ℂ) - s ≠ 1 := fun e => hs0' (sub_eq_self.mp e)
    exact h χ.conductor χ.primitiveCharacter⁻¹ (1 - s)
      (by rw [Complex.sub_re, Complex.one_re]; linarith) (Or.inr ht) hr
  · exact heq
  · exact absurd hz (h N χ s hgt (Or.inr hs))

/- English proof (authored)
A zero with real part at least 1 contradicts the usual zeta nonvanishing theorem. When the real part lies strictly between 0 and 1, view zeta as the L-function of the character of modulus 1 and apply the Dirichlet critical-strip result.

It remains to consider Re(s) ≤ 0. The value at zero is nonzero. The exclusions on s also ensure Γℝ(s) is nonzero, since its other zeros are the negative even integers. Thus the completed zeta function vanishes at s. Its functional equation transfers the zero to 1 − s, where the ordinary zeta function would then vanish with real part at least 1. This is impossible.
-/
theorem zeta (h : HalfPlane) : Zeta := by
  intro s hz htriv hs1
  have hs0 : s ≠ 0 := fun e => by rw [e, riemannZeta_zero] at hz; norm_num at hz
  rcases lt_or_ge 0 s.re with hpos | hnpos
  · rcases lt_or_ge s.re 1 with hlt1 | hge1
    · have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = 0 := by
        rw [DirichletCharacter.LFunction_modOne_eq]; exact hz
      exact strip h 1 1 s hpos hlt1 hL
    · exact absurd hz (riemannZeta_ne_zero_of_one_le_re hge1)
  · exfalso
    have hG : Gammaℝ s ≠ 0 := by
      intro hg
      obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hg
      rcases n with _ | n
      · exact hs0 (by simpa using hn)
      · exact htriv ⟨n, by rw [hn]; push_cast; ring⟩
    have hc : completedRiemannZeta s = 0 := by
      rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hz
      exact hz.resolve_right hG
    have h1s : 1 - s ≠ 0 := fun e => by
      have := congrArg Complex.re e
      rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
      linarith
    have hz' : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_def_of_ne_zero h1s, completedRiemannZeta_one_sub, hc, zero_div]
    exact riemannZeta_ne_zero_of_one_le_re (by rw [Complex.sub_re, Complex.one_re]; linarith) hz'

/- English proof (authored)
Both statements say that every zero of the zeta function other than 1 and the negative even integers has real part 1/2. Each direction follows by using the same hypothesis on those zeros.
-/
theorem zeta_iff : Zeta ↔ RiemannHypothesis := Iff.rfl

end Claim
