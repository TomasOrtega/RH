import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.F

open PowerSeries

namespace TaylorWp

def T (f : ℂ → ℂ) (F : PowerSeries ℂ) : Prop := AnalyticAt ℂ f 0 ∧ taylor0 f = F

/- English proof (translation)
Assemble the required witnesses or components as `⟨hf.1.add hg.1, by rw [(hr.1 f g hf.1 hg.1).1, hf.2, hg.2]⟩`.
-/
theorem T.add (hr : TaylorRing) {f g : ℂ → ℂ} {F G : PowerSeries ℂ} (hf : T f F) (hg : T g G) :
    T (fun z => f z + g z) (F + G) :=
  ⟨hf.1.add hg.1, by rw [(hr.1 f g hf.1 hg.1).1, hf.2, hg.2]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨hf.1.mul hg.1, by rw [(hr.1 f g hf.1 hg.1).2, hf.2, hg.2]⟩`.
-/
theorem T.mul (hr : TaylorRing) {f g : ℂ → ℂ} {F G : PowerSeries ℂ} (hf : T f F) (hg : T g G) :
    T (fun z => f z * g z) (F * G) :=
  ⟨hf.1.mul hg.1, by rw [(hr.1 f g hf.1 hg.1).2, hf.2, hg.2]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨analyticAt_const, hr.2.1 c⟩`.
-/
theorem T.const (hr : TaylorRing) (c : ℂ) : T (fun _ => c) (C c) :=
  ⟨analyticAt_const, hr.2.1 c⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨analyticAt_id, hr.2.2.1⟩`.
-/
theorem T.id (hr : TaylorRing) : T (fun z => z) X :=
  ⟨analyticAt_id, hr.2.2.1⟩

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using T.const hr 1`. Consider the case `succ k ih => simpa only [pow_succ] using T.mul hr ih hf`.
-/
theorem T.pow (hr : TaylorRing) {f : ℂ → ℂ} {F : PowerSeries ℂ} (hf : T f F) (k : ℕ) :
    T (fun z => f z ^ k) (F ^ k) := by
  induction k with
  | zero => simpa using T.const hr 1
  | succ k ih => simpa only [pow_succ] using T.mul hr ih hf

end TaylorWp

open TaylorWp

/- English proof (translation)
Introduce `L n`. Rewrite using `[pSeries, taylor0, coeff_mk, L.iteratedDeriv_weierstrassPExcept_self 0]`. Distinguish the cases in `hn : n = 0`. Simplify using `[hn]`. Simplify using `only [hn, if_false, PeriodPair.sumInvPow_zero]`.

Establish `h : ((n.factorial : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast n.factorial_ne_zero`. Rewrite using `[Nat.factorial_succ]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem weierstrass_p_series_coeff : PSeriesCoeff := by
  intro L n
  rw [pSeries, taylor0, coeff_mk, L.iteratedDeriv_weierstrassPExcept_self 0]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, if_false, PeriodPair.sumInvPow_zero]
    have h : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    rw [Nat.factorial_succ]
    push_cast
    field_simp

/- English proof (translation)
Introduce `L`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, weierstrass_p_series_coeff L 0]`. Simplify using the standard rewrite rules. Introduce `n hn`.

Rewrite using `[weierstrass_p_series_coeff L n, L.G_eq_zero_of_odd (n + 2) (by`. Take `⟨k, rfl⟩` from `hn; exact ⟨k + 1, by ring⟩)]`. Simplify using the standard rewrite rules. Establish `hp : T (L.weierstrassPExcept 0) (pSeries L)` using `⟨L.analyticAt_weierstrassPExcept 0, rfl⟩`. Establish `hp' : T (deriv (L.weierstrassPExcept 0)) (Formalism.L2.Th1.B.dz (pSeries L))` using `⟨hp.1.deriv, hd.1 _ hp.1⟩`.

Establish `hq` using `T.add hr (T.const hr 1) (T.mul hr (T.pow hr (T.id hr) 2) hp)`. Establish `h1` using `T.pow hr (T.add hr (T.const hr (-2)) (T.mul hr (T.pow hr (T.id hr) 3) hp')) 2`. Establish `h2` using `T.add hr (T.add hr (T.mul hr (T.const hr 4) (T.pow hr hq 3)) (T.mul hr (T.mul hr (T.const hr (-L.g₂)) (T.pow hr (T.id hr) 4)) hq)) (T.mul hr (T.const hr (-L.g₃)) (T.pow hr (T.id hr) 6))`. Establish `key` using `hr.2.2.2 _ _ (?_ : (fun z => (-2 + z ^ 3 * deriv (L.weierstrassPExcept 0) z) ^ 2) =ᶠ[nhds 0] fun z => 4 * (1 + z ^ 2 * L.weierstrassPExcept 0 z) ^ 3 + -L.g₂ * z ^ 4 * (1 + z ^ 2 * L.weierstrassPExcept 0 z) + -L.g₃ * z ^ 6)`. Rewrite `key` using `[h1.2, h2.2]`.

Simplify using `only [map_neg, map_ofNat, map_one] at key`. Rewrite using `[key]`. Expand and normalize the polynomial expressions, which then agree. Use `filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz`. Rewrite using `[L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 hz]`.

Distinguish the cases in `hz0 : z = 0`. Simplify using `[hz0]`. Evaluate the numerical expressions. Use `replace hz : z ∉ L.lattice := by simp_all`. Establish `hE` using `L.derivWeierstrassP_sq z hz`.

Establish `e1` using `L.weierstrassPExcept_def 0 z`. Establish `e2` using `L.derivWeierstrassPExcept_def 0 z`. Simplify using `only [ZeroMemClass.coe_zero, sub_zero] at e1 e2`. Rewrite using `[e1, e2]`. Establish `e3 : (z ^ 3 * L.derivWeierstrassP z) ^ 2 = z ^ 6 * (4 * L.weierstrassP z ^ 3 - L.g₂ * L.weierstrassP z - L.g₃)` using `by rw [← hE]; ring`.

Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Take the linear combination `e3`.
-/
theorem taylorIsWp_of (hr : TaylorRing) (hd : TaylorDeriv) : TaylorIsWp := by
  intro L
  refine ⟨?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, weierstrass_p_series_coeff L 0]; simp
  · intro n hn
    rw [weierstrass_p_series_coeff L n, L.G_eq_zero_of_odd (n + 2) (by
      obtain ⟨k, rfl⟩ := hn; exact ⟨k + 1, by ring⟩)]
    simp
  · have hp : T (L.weierstrassPExcept 0) (pSeries L) := ⟨L.analyticAt_weierstrassPExcept 0, rfl⟩
    have hp' : T (deriv (L.weierstrassPExcept 0)) (Formalism.L2.Th1.B.dz (pSeries L)) :=
      ⟨hp.1.deriv, hd.1 _ hp.1⟩
    have hq := T.add hr (T.const hr 1) (T.mul hr (T.pow hr (T.id hr) 2) hp)
    have h1 := T.pow hr (T.add hr (T.const hr (-2)) (T.mul hr (T.pow hr (T.id hr) 3) hp')) 2
    have h2 := T.add hr (T.add hr (T.mul hr (T.const hr 4) (T.pow hr hq 3))
      (T.mul hr (T.mul hr (T.const hr (-L.g₂)) (T.pow hr (T.id hr) 4)) hq))
      (T.mul hr (T.const hr (-L.g₃)) (T.pow hr (T.id hr) 6))
    have key := hr.2.2.2 _ _ (?_ : (fun z => (-2 + z ^ 3 * deriv (L.weierstrassPExcept 0) z) ^ 2)
      =ᶠ[nhds 0] fun z => 4 * (1 + z ^ 2 * L.weierstrassPExcept 0 z) ^ 3
        + -L.g₂ * z ^ 4 * (1 + z ^ 2 * L.weierstrassPExcept 0 z) + -L.g₃ * z ^ 6)
    · rw [h1.2, h2.2] at key
      simp only [map_neg, map_ofNat, map_one] at key
      rw [key]; ring
    · filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
      rw [L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 hz]
      by_cases hz0 : z = 0
      · simp [hz0]; norm_num
      replace hz : z ∉ L.lattice := by simp_all
      have hE := L.derivWeierstrassP_sq z hz
      have e1 := L.weierstrassPExcept_def 0 z
      have e2 := L.derivWeierstrassPExcept_def 0 z
      simp only [ZeroMemClass.coe_zero, sub_zero] at e1 e2
      rw [e1, e2]
      have e3 : (z ^ 3 * L.derivWeierstrassP z) ^ 2 = z ^ 6 * (4 * L.weierstrassP z ^ 3
          - L.g₂ * L.weierstrassP z - L.g₃) := by rw [← hE]; ring
      field_simp
      simp
      linear_combination e3

/- English proof (translation)
Introduce `K _ _ g2 g3 P Q hP hQ`. Take `⟨-, -, hP⟩` from `hP`. Take `⟨-, -, hQ⟩` from `hQ`. Establish `hX : (X : PowerSeries K) ≠ 0` using `X_ne_zero`. Establish `hdX : ∀ n : ℕ, X * derivative K ((X : PowerSeries K) ^ n) = (n : PowerSeries K) * X ^ n`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ, Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivative_X]`.

Use `push_cast`. Take the linear combination `X * ih`. Establish `main : ∀ n : ℕ, X ^ n ∣ P - Q`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp`. Consider the case `succ n ih`. Take `⟨E, hE⟩` from `ih`. Establish `hD : X * (derivative K P - derivative K Q) = X ^ n * ((n : PowerSeries K) * E + X * derivative K E)`. Rewrite using `[← map_sub, hE, Derivation.leibniz, smul_eq_mul, smul_eq_mul]`.

Take the linear combination `E * hdX n`. Establish `hc : ((n : PowerSeries K) * E + X * derivative K E) * (-4 + X ^ 3 * (derivative K P + derivative K Q)) = E * (4 * ((1 + X ^ 2 * P) ^ 2 + (1 + X ^ 2 * P) * (1 + X ^ 2 * Q) + (1 + X ^ 2 * Q) ^ 2) - C g2 * X ^ 4)`. Apply `mul_left_cancel₀ (pow_ne_zero (n + 2) hX)` to reduce the goal to its premises. Establish `hs` using `congrArg₂ (· - ·) hP hQ`. Simplify using `only [Formalism.L2.Th1.B.dz] at hs`.

Take the linear combination `hs - X ^ 2 * (-4 + X ^ 3 * (derivative K P + derivative K Q)) * hD + X ^ 2 * (4 * ((1 + X ^ 2 * P) ^ 2 + (1 + X ^ 2 * P) * (1 + X ^ 2 * Q) + (1 + X ^ 2 * Q) ^ 2) - C g2 * X ^ 4) * hE`. Establish `h0` using `congrArg constantCoeff hc`. Simplify using `only [map_mul, map_add, map_sub, map_neg, map_pow, map_natCast, map_ofNat, map_one, constantCoeff_X, constantCoeff_C] at h0`. Establish `h1 : (4 * (n : K) + 12) * constantCoeff E = 0`. Take the linear combination `-h0`.

Establish `h2 : (4 * (n : K) + 12) ≠ 0`. Establish `: ((4 * n + 12 : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `h3 : constantCoeff E = 0` using `(mul_eq_zero.mp h1).resolve_left h2`.

Take `⟨E', rfl⟩` from `X_dvd_iff.mpr h3`. Conclude with `⟨E', by rw [hE]; ring⟩`. Establish `hz : P - Q = 0`. Use extensionality with `m`. Rewrite using `[map_zero]`.

Conclude with `X_pow_dvd_iff.mp (main (m + 1)) m (Nat.lt_succ_self m)`. Conclude with `sub_eq_zero.mp hz`.
-/
theorem weierstrass_series_unique : IsWpUnique := by
  intro K _ _ g2 g3 P Q hP hQ
  obtain ⟨-, -, hP⟩ := hP
  obtain ⟨-, -, hQ⟩ := hQ
  have hX : (X : PowerSeries K) ≠ 0 := X_ne_zero
  have hdX : ∀ n : ℕ, X * derivative K ((X : PowerSeries K) ^ n) = (n : PowerSeries K) * X ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivative_X]
      push_cast
      linear_combination X * ih
  have main : ∀ n : ℕ, X ^ n ∣ P - Q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨E, hE⟩ := ih
      have hD : X * (derivative K P - derivative K Q)
          = X ^ n * ((n : PowerSeries K) * E + X * derivative K E) := by
        rw [← map_sub, hE, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        linear_combination E * hdX n
      have hc : ((n : PowerSeries K) * E + X * derivative K E)
            * (-4 + X ^ 3 * (derivative K P + derivative K Q))
          = E * (4 * ((1 + X ^ 2 * P) ^ 2 + (1 + X ^ 2 * P) * (1 + X ^ 2 * Q) + (1 + X ^ 2 * Q) ^ 2)
              - C g2 * X ^ 4) := by
        apply mul_left_cancel₀ (pow_ne_zero (n + 2) hX)
        have hs := congrArg₂ (· - ·) hP hQ
        simp only [Formalism.L2.Th1.B.dz] at hs
        linear_combination hs
          - X ^ 2 * (-4 + X ^ 3 * (derivative K P + derivative K Q)) * hD
          + X ^ 2 * (4 * ((1 + X ^ 2 * P) ^ 2 + (1 + X ^ 2 * P) * (1 + X ^ 2 * Q)
              + (1 + X ^ 2 * Q) ^ 2) - C g2 * X ^ 4) * hE
      have h0 := congrArg constantCoeff hc
      simp only [map_mul, map_add, map_sub, map_neg, map_pow, map_natCast, map_ofNat, map_one,
        constantCoeff_X, constantCoeff_C] at h0
      have h1 : (4 * (n : K) + 12) * constantCoeff E = 0 := by
        linear_combination -h0
      have h2 : (4 * (n : K) + 12) ≠ 0 := by
        have : ((4 * n + 12 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast at this
        exact this
      have h3 : constantCoeff E = 0 := (mul_eq_zero.mp h1).resolve_left h2
      obtain ⟨E', rfl⟩ := X_dvd_iff.mpr h3
      exact ⟨E', by rw [hE]; ring⟩
  have hz : P - Q = 0 := by
    ext m
    rw [map_zero]
    exact X_pow_dvd_iff.mp (main (m + 1)) m (Nat.lt_succ_self m)
  exact sub_eq_zero.mp hz

end Formalism.L2.Th1.F
