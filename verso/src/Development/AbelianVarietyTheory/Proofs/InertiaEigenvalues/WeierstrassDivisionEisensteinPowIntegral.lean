import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.WDivE

/- English proof (translation)
Rewrite using `[coeff_mul]`. Use `Finset.sum_eq_zero fun p hp => ?_` and prove the remaining obligations. Establish `hp` using `Finset.HasAntidiagonal.mem_antidiagonal.mp hp`. Distinguish the cases in `h : a < p.1`. Rewrite using `[hF _ h, zero_mul]`.

Rewrite using `[hG _ (by omega), mul_zero]`.
-/
theorem coeff_vanish_mul {K : Type} [CommRing K] {F G : K⟦X⟧} {a b : ℕ}
    (hF : ∀ k, a < k → coeff k F = 0) (hG : ∀ k, b < k → coeff k G = 0) (k : ℕ) (hk : a + b < k) :
    coeff k (F * G) = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases h : a < p.1
  · rw [hF _ h, zero_mul]
  · rw [hG _ (by omega), mul_zero]

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[map_sum]`. Simplify using `only [coeff_C_mul_X_pow]`. Distinguish the cases in `hm : m < N`. Rewrite using `[Finset.sum_eq_single ⟨m, hm⟩]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce `h`. Conclude with `hb (Fin.ext h.symm)`.

Simplify using the standard rewrite rules. Rewrite using `[hP m (by omega), Finset.sum_eq_zero]`. Introduce `b _`. Rewrite using `[if_neg]`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_sum_of_vanish {K : Type} [CommRing K] {P : K⟦X⟧} {N : ℕ}
    (hP : ∀ k, N ≤ k → coeff k P = 0) : P = ∑ k : Fin N, C (coeff (k : ℕ) P) * X ^ (k : ℕ) := by
  ext m
  rw [map_sum]
  simp only [coeff_C_mul_X_pow]
  by_cases hm : m < N
  · rw [Finset.sum_eq_single ⟨m, hm⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro h; exact hb (Fin.ext h.symm)
    · simp
  · rw [hP m (by omega), Finset.sum_eq_zero]
    intro b _; rw [if_neg]; omega

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (e : ℕ) [NeZero e]

omit [CompleteSpace K] [NeZero e] in
/- English proof (translation)
Introduce `n` and use `by rw [quotE, coeff_mk] refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun j => ?_ rw [norm_mul, norm_pow, norm_neg] exact mul_le_one₀ (hf _) (by positivity) (pow_le_one₀ (norm_nonneg _) (norm_l_lt_one l).le)`.
-/
theorem quotE_mem_A {f : K⟦X⟧} (hf : f ∈ A O K) : quotE l e f ∈ A O K := fun n => by
  rw [quotE, coeff_mk]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun j => ?_
  rw [norm_mul, norm_pow, norm_neg]
  exact mul_le_one₀ (hf _) (by positivity) (pow_le_one₀ (norm_nonneg _) (norm_l_lt_one l).le)

/- English proof (translation)
Assemble the required witnesses or components as `⟨f - E K l e * quotE l e f, quotE l e f, sub_mem hf (mul_mem (E_mem l e _) (quotE_mem_A l e hf)), fun k hk => by obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk exact coeff_sub_E_mul_quotE l e (A_le_Rpi l e hf) m, quotE_mem_A l e hf, by ring⟩`.
-/
theorem div_E_step {f : K⟦X⟧} (hf : f ∈ A O K) : ∃ P g, P ∈ A O K ∧
    (∀ k, e ≤ k → coeff k P = 0) ∧ g ∈ A O K ∧ f = P + E K l e * g :=
  ⟨f - E K l e * quotE l e f, quotE l e f,
    sub_mem hf (mul_mem (E_mem l e _) (quotE_mem_A l e hf)),
    fun k hk => by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
      exact coeff_sub_E_mul_quotE l e (A_le_Rpi l e hf) m,
    quotE_mem_A l e hf, by ring⟩

omit [IsUltrametricDist K] [CompleteSpace K] [IsUnitBall O K] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro k hk`. Simplify using `[coeff_one]`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih`.

Introduce `k hk`. Rewrite using `[pow_succ]`. Use `coeff_vanish_mul ih (b := e) (fun j hj => ?_) k (by rw [Nat.mul_succ] at hk; exact hk)` and prove the remaining obligations. Rewrite using `[E, map_add, coeff_X_pow, ← map_natCast (C : K →+* K⟦X⟧), coeff_C]`. Rewrite using `[if_neg (by omega), if_neg (by omega), add_zero]`.
-/
theorem coeff_E_pow_vanish (n : ℕ) : ∀ k, e * n < k → coeff k (E K l e ^ n) = 0 := by
  induction n with
  | zero => intro k hk; simp [coeff_one]; omega
  | succ n ih =>
    intro k hk
    rw [pow_succ]
    refine coeff_vanish_mul ih (b := e) (fun j hj => ?_) k (by rw [Nat.mul_succ] at hk; exact hk)
    rw [E, map_add, coeff_X_pow, ← map_natCast (C : K →+* K⟦X⟧), coeff_C]
    rw [if_neg (by omega), if_neg (by omega), add_zero]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, f, zero_mem _, fun _ _ => by simp, hf, by simp⟩`. Consider the case `succ n ih`. Take `⟨P, g, hP, hPv, hg, rfl⟩` from `ih`. Take `⟨Q, h, hQ, hQv, hh, rfl⟩` from `div_E_step l e hg`.

Use `⟨P + E K l e ^ n * Q, h, add_mem hP (mul_mem (pow_mem (E_mem l e _) n) hQ), fun k hk => ?_, hh, by ring⟩` and prove the remaining obligations. Establish `he` using `NeZero.pos e`. Rewrite using `[map_add, hPv k (by rw [Nat.mul_succ] at hk; omega), zero_add]`. Conclude with `coeff_vanish_mul (coeff_E_pow_vanish l e n) (b := e - 1) (fun j hj => hQv j (by omega)) k (by rw [Nat.mul_succ] at hk; omega)`.
-/
theorem div_E_pow (n : ℕ) {f : K⟦X⟧} (hf : f ∈ A O K) : ∃ P g, P ∈ A O K ∧
    (∀ k, e * n ≤ k → coeff k P = 0) ∧ g ∈ A O K ∧ f = P + E K l e ^ n * g := by
  induction n with
  | zero => exact ⟨0, f, zero_mem _, fun _ _ => by simp, hf, by simp⟩
  | succ n ih =>
    obtain ⟨P, g, hP, hPv, hg, rfl⟩ := ih
    obtain ⟨Q, h, hQ, hQv, hh, rfl⟩ := div_E_step l e hg
    refine ⟨P + E K l e ^ n * Q, h, add_mem hP (mul_mem (pow_mem (E_mem l e _) n) hQ),
      fun k hk => ?_, hh, by ring⟩
    have he := NeZero.pos e
    rw [map_add, hPv k (by rw [Nat.mul_succ] at hk; omega), zero_add]
    exact coeff_vanish_mul (coeff_E_pow_vanish l e n) (b := e - 1)
      (fun j hj => hQv j (by omega)) k (by rw [Nat.mul_succ] at hk; omega)

end GlobalTheory.WDivE

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ l e _ _ _ n f hf`. Take `⟨P, g, hP, hPv, hg, rfl⟩` from `GlobalTheory.WDivE.div_E_pow l e n hf`. Use `choose c hc using fun k : Fin (e * n) => (IsUnitBall.mem_range_iff (O := O) (coeff (k : ℕ) P)).2 (hP k)`. Use `⟨c, g, hg, ?_⟩` and prove the remaining obligations. Simplify using `only [hc]`.

Rewrite using `[← GlobalTheory.WDivE.eq_sum_of_vanish hPv]`.
-/
theorem GlobalTheory.weierstrassDiv_E_pow : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (n : ℕ) (f : K⟦X⟧), f ∈ A O K → ∃ (c : Fin (e * n) → O) (g : K⟦X⟧), g ∈ A O K ∧ f = ∑ k : Fin (e * n), C (algebraMap O K (c k)) * X ^ (k : ℕ) + E K l e ^ n * g := by
  intro O K _ _ _ _ _ _ l e _ _ _ n f hf
  obtain ⟨P, g, hP, hPv, hg, rfl⟩ := GlobalTheory.WDivE.div_E_pow l e n hf
  choose c hc using fun k : Fin (e * n) => (IsUnitBall.mem_range_iff (O := O) (coeff (k : ℕ) P)).2 (hP k)
  refine ⟨c, g, hg, ?_⟩
  simp only [hc]
  rw [← GlobalTheory.WDivE.eq_sum_of_vanish hPv]
