import Mathlib

namespace GlobalTheory.EsymmOfPowerSums

open MvPolynomial

/- English proof (translation)
Introduce `k`. Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Introduce `hk`. Break down `Nat.eq_zero_or_pos k with rfl | hpos` into its components or cases.

Simplify using the standard rewrite rules. Establish `hk0 : (k : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hpos.ne'`. Apply `mul_left_cancel₀ hk0` to reduce the goal to its premises. Establish `key` using `MvPolynomial.mul_esymm_eq_sum (Fin d) ℂ k`. Establish `ha` using `congrArg (MvPolynomial.aeval a) key`.

Establish `hb` using `congrArg (MvPolynomial.aeval b) key`. Simplify using `only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum] at ha hb`. Rewrite using `[ha, hb]`. Use `congr 1`. Use `Finset.sum_congr rfl ?_` and prove the remaining obligations.

Introduce `p hp`. Rewrite `hp` using `[Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]`. Take `⟨h1, h2⟩` from `hp`. Rewrite using `[ih p.1 h2 (by omega)]`. Use `congr 1`.

Use `h p.2 (by omega) (by omega)` as an intermediate fact. Simplify `this` using `[MvPolynomial.psum]`.
-/
theorem esymm_eq_of_psum_eq {d : ℕ} (a b : Fin d → ℂ)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ d → ∑ i : Fin d, a i ^ k = ∑ i : Fin d, b i ^ k) :
    ∀ k ≤ d, (MvPolynomial.aeval a : MvPolynomial (Fin d) ℂ → ℂ) (MvPolynomial.esymm (Fin d) ℂ k)
      = (MvPolynomial.aeval b : MvPolynomial (Fin d) ℂ → ℂ) (MvPolynomial.esymm (Fin d) ℂ k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp
    have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    apply mul_left_cancel₀ hk0
    have key := MvPolynomial.mul_esymm_eq_sum (Fin d) ℂ k
    have ha := congrArg (MvPolynomial.aeval a) key
    have hb := congrArg (MvPolynomial.aeval b) key
    simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum] at ha hb
    rw [ha, hb]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [ih p.1 h2 (by omega)]
    congr 1
    have := h p.2 (by omega) (by omega)
    simpa [MvPolynomial.psum] using this

end GlobalTheory.EsymmOfPowerSums
