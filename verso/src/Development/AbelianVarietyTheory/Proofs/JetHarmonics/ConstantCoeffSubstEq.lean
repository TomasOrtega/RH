import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.FeUniq

variable {q : ℕ} [Fact q.Prime]

/- English proof (translation)
Introduce `n`. Rewrite using `[coeff_mul]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hf _) (norm_nonneg _) (hg _)`.
-/
theorem intSer_mul {f g : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (hg : Bd 1 g) : Bd 1 (f * g) := by
  intro n
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

/- English proof (translation)
Introduce `n`. Rewrite using `[coeff_C]`. Use `split_ifs`. Conclude with `hc`. Simplify using the standard rewrite rules.
-/
theorem intSer_C {c : ℂ_[q]} (hc : ‖c‖ ≤ 1) : Bd 1 (C c : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact hc
  · simp

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using intSer_C (q := q) (c := 1) (by simp)`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `intSer_mul ih hf`.
-/
theorem intSer_pow {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (n : ℕ) : Bd 1 (f ^ n) := by
  induction n with
  | zero => simpa using intSer_C (q := q) (c := 1) (by simp)
  | succ n ih => rw [pow_succ]; exact intSer_mul ih hf

/- English proof (translation)
Introduce `n`. Rewrite using `[Polynomial.aeval_eq_sum_range, map_sum]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_smul, smul_eq_mul, norm_mul]`. Conclude with `mul_le_one₀ (hP _) (norm_nonneg _) (intSer_pow hh i n)`.
-/
theorem intSer_aeval {h : ℂ_[q]⟦X⟧} (hh : Bd 1 h) (P : Polynomial ℂ_[q]) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) :
    Bd 1 (Polynomial.aeval h P) := by
  intro n
  rw [Polynomial.aeval_eq_sum_range, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [coeff_smul, smul_eq_mul, norm_mul]
  exact mul_le_one₀ (hP _) (norm_nonneg _) (intSer_pow hh i n)

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using `[hf]`.

Establish `hs : HasSubst h` using `HasSubst.of_constantCoeff_zero' hh0`. Use `set P : Polynomial ℂ_[q] := trunc n f with hP`. Establish `hPi : ∀ i, ‖P.coeff i‖ ≤ 1`. Introduce `i`. Rewrite using `[hP, coeff_trunc]`.

Use `split_ifs with hi`. Conclude with `ih i hi`. Simplify using the standard rewrite rules. Establish `hPs : Bd 1 (P : ℂ_[q]⟦X⟧)` using `fun i => by rw [Polynomial.coeff_coe]; exact hPi i`. Establish `hP0 : constantCoeff (P : ℂ_[q]⟦X⟧) = 1`.

Rewrite using `[← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hP, coeff_trunc, if_pos hn, coeff_zero_eq_constantCoeff_apply, hf]`. Choose the witnesses or unpack the hypotheses as in `⟨Q, hQ⟩ : (X : ℂ_[q]⟦X⟧) ^ n ∣ f - P := by`. Rewrite using `[X_pow_dvd_iff]`. Introduce `m hm`. Rewrite using `[map_sub, Polynomial.coeff_coe, hP, coeff_trunc, if_pos hm, sub_self]`.

Establish `hX : ∀ g : ℂ_[q]⟦X⟧, coeff n (X ^ n * g) = constantCoeff g` using `fun g => by`. Simplify using `using coeff_X_pow_mul g n 0`. Establish `hQ0 : constantCoeff Q = coeff n f`. Rewrite using `[← hX, ← hQ, map_sub, Polynomial.coeff_coe, hP, coeff_trunc, if_neg (lt_irrefl n), sub_zero]`. Take `⟨h', hh'⟩ : (X : ℂ_[q]⟦X⟧) ∣ h` from `X_dvd_iff.2 hh0`.

Establish `h'0 : constantCoeff h' = coeff 1 h`. Rewrite using `[hh', coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]`. Establish `hfe : f = (P : ℂ_[q]⟦X⟧) + X ^ n * Q` using `by rw [← hQ]; ring`. Establish `hsQ : constantCoeff (PowerSeries.subst h Q : ℂ_[q]⟦X⟧) = constantCoeff Q`. Take `⟨Q', hQ'⟩ : (X : ℂ_[q]⟦X⟧) ∣ Q - C (constantCoeff Q)` from `X_dvd_iff.2 (by simp)`.

Establish `: Q = C (constantCoeff Q) + X * Q'` using `by rw [← hQ']; ring`. Use `conv_lhs => rw [this, subst_add hs, subst_mul hs, subst_X hs]`. Establish `hC : (PowerSeries.subst h (C (constantCoeff Q) : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧) = C (constantCoeff Q)`. Rewrite using `[← Polynomial.coe_C, subst_coe hs, Polynomial.aeval_C]`. Simplify using the standard rewrite rules.

Rewrite using `[hC]`. Simplify using `[hh0]`. Establish `hL : (PowerSeries.subst h f : ℂ_[q]⟦X⟧) * A = Polynomial.aeval h P * A + X ^ n * (h' ^ n * PowerSeries.subst h Q * A)` using `by conv_lhs => rw [hfe, subst_add hs, subst_mul hs, subst_pow hs, subst_X hs, subst_coe hs]`. Establish `: h ^ n = X ^ n * h' ^ n` using `by rw [hh', mul_pow]`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hR : f ^ N * B = (P : ℂ_[q]⟦X⟧) ^ N * B + X ^ n * (Q * (∑ i ∈ Finset.range N, f ^ i * (P : ℂ_[q]⟦X⟧) ^ (N - 1 - i)) * B)`. Use `geom_sum₂_mul f (P : ℂ_[q]⟦X⟧) N` as an intermediate fact. Rewrite `this` using `[hQ]`. Take the linear combination `(-B) * this`.

Establish `key` using `congrArg (coeff n) e`. Rewrite `key` using `[hL, hR, map_add, map_add, hX, hX]`. Simplify using `only [map_mul, map_pow, map_sum, hA0, hB0, hf, hP0, hsQ, hQ0, h'0, one_pow, mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at key`. Establish `h1` using `intSer_mul (intSer_aeval hh P hPi) hA n`. Establish `h2` using `intSer_mul (intSer_pow hPs N) hB n`.

Establish `k2 : (coeff 1 h ^ n - N) * coeff n f = coeff n ((P : ℂ_[q]⟦X⟧) ^ N * B) - coeff n (Polynomial.aeval h P * A)`. Take the linear combination `key`. Establish `hu : ‖coeff 1 h ^ n - (N : ℂ_[q])‖ = 1`. Establish `hp : ‖coeff 1 h ^ n‖ = 1` using `by rw [norm_pow, hh1, one_pow]`. Rewrite using `[sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hp, norm_neg]; exact hN.ne'), hp, norm_neg, max_eq_left hN.le]`.

Use `congrArg norm k2` as an intermediate fact. Rewrite `this` using `[norm_mul, hu, one_mul]`. Rewrite using `[this, sub_eq_add_neg]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 (by rwa [norm_neg]))`.
-/
theorem intSer_of_funEq (f h A B : ℂ_[q]⟦X⟧) (N : ℕ) (hf : constantCoeff f = 1) (hh : Bd 1 h)
    (hh0 : constantCoeff h = 0) (hh1 : ‖coeff 1 h‖ = 1) (hN : ‖(N : ℂ_[q])‖ < 1) (hA : Bd 1 A)
    (hA0 : constantCoeff A = 1) (hB : Bd 1 B) (hB0 : constantCoeff B = 1)
    (e : (PowerSeries.subst h f : ℂ_[q]⟦X⟧) * A = f ^ N * B) : Bd 1 f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hf]
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh0
  set P : Polynomial ℂ_[q] := trunc n f with hP
  have hPi : ∀ i, ‖P.coeff i‖ ≤ 1 := by
    intro i
    rw [hP, coeff_trunc]
    split_ifs with hi
    · exact ih i hi
    · simp
  have hPs : Bd 1 (P : ℂ_[q]⟦X⟧) := fun i => by rw [Polynomial.coeff_coe]; exact hPi i
  have hP0 : constantCoeff (P : ℂ_[q]⟦X⟧) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hP, coeff_trunc, if_pos hn,
      coeff_zero_eq_constantCoeff_apply, hf]
  obtain ⟨Q, hQ⟩ : (X : ℂ_[q]⟦X⟧) ^ n ∣ f - P := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, hP, coeff_trunc, if_pos hm, sub_self]
  have hX : ∀ g : ℂ_[q]⟦X⟧, coeff n (X ^ n * g) = constantCoeff g := fun g => by
    simpa using coeff_X_pow_mul g n 0
  have hQ0 : constantCoeff Q = coeff n f := by
    rw [← hX, ← hQ, map_sub, Polynomial.coeff_coe, hP, coeff_trunc, if_neg (lt_irrefl n), sub_zero]
  obtain ⟨h', hh'⟩ : (X : ℂ_[q]⟦X⟧) ∣ h := X_dvd_iff.2 hh0
  have h'0 : constantCoeff h' = coeff 1 h := by
    rw [hh', coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have hfe : f = (P : ℂ_[q]⟦X⟧) + X ^ n * Q := by rw [← hQ]; ring
  have hsQ : constantCoeff (PowerSeries.subst h Q : ℂ_[q]⟦X⟧) = constantCoeff Q := by
    obtain ⟨Q', hQ'⟩ : (X : ℂ_[q]⟦X⟧) ∣ Q - C (constantCoeff Q) := X_dvd_iff.2 (by simp)
    have : Q = C (constantCoeff Q) + X * Q' := by rw [← hQ']; ring
    conv_lhs => rw [this, subst_add hs, subst_mul hs, subst_X hs]
    have hC : (PowerSeries.subst h (C (constantCoeff Q) : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧) = C (constantCoeff Q) := by
      rw [← Polynomial.coe_C, subst_coe hs, Polynomial.aeval_C]; simp
    rw [hC]
    simp [hh0]
  have hL : (PowerSeries.subst h f : ℂ_[q]⟦X⟧) * A =
      Polynomial.aeval h P * A + X ^ n * (h' ^ n * PowerSeries.subst h Q * A) := by
    conv_lhs => rw [hfe, subst_add hs, subst_mul hs, subst_pow hs, subst_X hs, subst_coe hs]
    have : h ^ n = X ^ n * h' ^ n := by rw [hh', mul_pow]
    rw [this]; ring
  have hR : f ^ N * B = (P : ℂ_[q]⟦X⟧) ^ N * B +
      X ^ n * (Q * (∑ i ∈ Finset.range N, f ^ i * (P : ℂ_[q]⟦X⟧) ^ (N - 1 - i)) * B) := by
    have := geom_sum₂_mul f (P : ℂ_[q]⟦X⟧) N
    rw [hQ] at this
    linear_combination (-B) * this
  have key := congrArg (coeff n) e
  rw [hL, hR, map_add, map_add, hX, hX] at key
  simp only [map_mul, map_pow, map_sum, hA0, hB0, hf, hP0, hsQ, hQ0, h'0, one_pow, mul_one,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at key
  have h1 := intSer_mul (intSer_aeval hh P hPi) hA n
  have h2 := intSer_mul (intSer_pow hPs N) hB n
  have k2 : (coeff 1 h ^ n - N) * coeff n f =
      coeff n ((P : ℂ_[q]⟦X⟧) ^ N * B) - coeff n (Polynomial.aeval h P * A) := by
    linear_combination key
  have hu : ‖coeff 1 h ^ n - (N : ℂ_[q])‖ = 1 := by
    have hp : ‖coeff 1 h ^ n‖ = 1 := by rw [norm_pow, hh1, one_pow]
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [hp, norm_neg]; exact hN.ne'), hp, norm_neg, max_eq_left hN.le]
  have := congrArg norm k2
  rw [norm_mul, hu, one_mul] at this
  rw [this, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 (by rwa [norm_neg]))

/- English proof (translation)
Rewrite using `[← Polynomial.coe_C, subst_coe hs, Polynomial.aeval_C]`. Simplify using the standard rewrite rules.
-/
theorem subst_C_eq {h : ℂ_[q]⟦X⟧} (hs : HasSubst h) (c : ℂ_[q]) :
    (PowerSeries.subst h (C c : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧) = C c := by
  rw [← Polynomial.coe_C, subst_coe hs, Polynomial.aeval_C]; simp

/- English proof (translation)
Establish `hs : HasSubst h` using `HasSubst.of_constantCoeff_zero' hh0`. Take `⟨Q', hQ'⟩ : (X : ℂ_[q]⟦X⟧) ∣ Q - C (constantCoeff Q)` from `X_dvd_iff.2 (by simp)`. Establish `: Q = C (constantCoeff Q) + X * Q'` using `by rw [← hQ']; ring`. Use `conv_lhs => rw [this, subst_add hs, subst_mul hs, subst_X hs]`. Rewrite using `[subst_C_eq hs]`.

Simplify using `[hh0]`.
-/
theorem constantCoeff_subst_eq {h : ℂ_[q]⟦X⟧} (hh0 : constantCoeff h = 0) (Q : ℂ_[q]⟦X⟧) :
    constantCoeff (PowerSeries.subst h Q : ℂ_[q]⟦X⟧) = constantCoeff Q := by
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh0
  obtain ⟨Q', hQ'⟩ : (X : ℂ_[q]⟦X⟧) ∣ Q - C (constantCoeff Q) := X_dvd_iff.2 (by simp)
  have : Q = C (constantCoeff Q) + X * Q' := by rw [← hQ']; ring
  conv_lhs => rw [this, subst_add hs, subst_mul hs, subst_X hs]
  rw [subst_C_eq hs]
  simp [hh0]

/- English proof (translation)
Assemble the required witnesses or components as `⟨f.order.toNat, divXPowOrder f, X_pow_order_mul_divXPowOrder.symm, by rw [Ne, constantCoeff_divXPowOrder_eq_zero_iff]; exact hf⟩`.
-/
theorem exists_fac {f : ℂ_[q]⟦X⟧} (hf : f ≠ 0) :
    ∃ (n : ℕ) (Q : ℂ_[q]⟦X⟧), f = X ^ n * Q ∧ constantCoeff Q ≠ 0 :=
  ⟨f.order.toNat, divXPowOrder f, X_pow_order_mul_divXPowOrder.symm, by
    rw [Ne, constantCoeff_divXPowOrder_eq_zero_iff]; exact hf⟩

/- English proof (translation)
Establish `hs : HasSubst e` using `HasSubst.of_constantCoeff_zero' he0`. Take `⟨e', he'⟩ : (X : ℂ_[q]⟦X⟧) ∣ e` from `X_dvd_iff.2 he0`. Establish `h'0 : constantCoeff e' = coeff 1 e`. Rewrite using `[he', coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]`. Establish `ha : coeff 1 e ≠ 0`.

Introduce `h0`. Rewrite `he1` using `[h0, norm_zero]`. Conclude with `zero_ne_one he1`. Establish `hsub : ∀ (n : ℕ) (Q : ℂ_[q]⟦X⟧), (PowerSeries.subst e (X ^ n * Q : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧) = X ^ n * (e' ^ n * PowerSeries.subst e Q)`. Introduce `n Q`.

Rewrite using `[subst_mul hs, subst_pow hs, subst_X hs]`. Establish `: e ^ n = X ^ n * e' ^ n` using `by rw [he', mul_pow]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨k, rfl⟩ : ∃ k, m = k + 2` from `⟨m - 2, by omega⟩`.

Establish `hc : constantCoeff ρ ≠ 0`. Take `⟨n, Q, rfl, hQ⟩` from `exists_fac hρ`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using `using hQ`. It suffices to derive a contradiction.

Rewrite `h` using `[hsub]`. Establish `h3 : e' ^ n * PowerSeries.subst e Q = X ^ n * (Q * Q * (X ^ n * Q) ^ k)`. Apply `mul_left_cancel₀ (pow_ne_zero n (X_ne_zero (R := ℂ_[q])))` to reduce the goal to its premises. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h4` using `congrArg constantCoeff h3`. Rewrite `h4` using `[map_mul, map_mul, map_pow, map_pow, constantCoeff_X, zero_pow hn.ne', zero_mul, h'0, constantCoeff_subst_eq he0]`. Conclude with `mul_ne_zero (pow_ne_zero _ ha) hQ h4`. Use `set c := constantCoeff ρ with hcd`. Establish `hc1 : c ^ (k + 1) = 1`.

Establish `h4` using `congrArg constantCoeff h`. Rewrite `h4` using `[constantCoeff_subst_eq he0, map_pow, ← hcd]`. Apply `mul_left_cancel₀ hc` to reduce the goal to its premises. Rewrite using `[mul_one]`. Take the linear combination `-h4`.

Use `⟨c, ?_, hc1⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨n, Q, hf, hQ⟩` from `exists_fac (sub_ne_zero.2 hne)`. Establish `hn : n ≠ 0`. Introduce and unpack `rfl`.

Apply `hQ` to reduce the goal to its premises. Rewrite `hf` using `[pow_zero, one_mul]`. Rewrite using `[← hf, map_sub, constantCoeff_C, ← hcd, sub_self]`. Establish `hL : (PowerSeries.subst e ρ : ℂ_[q]⟦X⟧) = C c + X ^ n * (e' ^ n * PowerSeries.subst e Q)`. Establish `: ρ = C c + X ^ n * Q` using `by rw [← hf]; ring`.

Use `conv_lhs => rw [this, subst_add hs, hsub, subst_C_eq hs]`. Establish `hR : ρ ^ (k + 2) = C c + X ^ n * (Q * (∑ i ∈ Finset.range (k + 2), ρ ^ i * (C c : ℂ_[q]⟦X⟧) ^ (k + 2 - 1 - i)))`. Use `geom_sum₂_mul ρ (C c : ℂ_[q]⟦X⟧) (k + 2)` as an intermediate fact. Rewrite `this` using `[hf]`. Establish `h5 : (C c : ℂ_[q]⟦X⟧) ^ (k + 2) = C c`.

Rewrite using `[← map_pow, pow_succ, hc1, one_mul]`. Rewrite `this` using `[h5]`. Take the linear combination `-this`. Rewrite `h` using `[hL, hR]`. Establish `h3` using `mul_left_cancel₀ (pow_ne_zero n (X_ne_zero (R := ℂ_[q]))) (add_left_cancel h)`.

Establish `h4` using `congrArg constantCoeff h3`. Rewrite `h4` using `[map_mul, map_mul, map_pow, h'0, constantCoeff_subst_eq he0, map_sum, Finset.sum_congr rfl (g := fun _ => (1 : ℂ_[q])), Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, mul_comm]`. Establish `h5` using `congrArg norm (mul_left_cancel₀ hQ h4)`. Rewrite `h5` using `[norm_pow, he1, one_pow]`. Conclude with `hm.ne' h5`.

Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[map_mul, map_pow, map_pow, constantCoeff_C, ← hcd, ← pow_add, ← hc1]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem const_of_funEq (e : ℂ_[q]⟦X⟧) (m : ℕ) (he0 : constantCoeff e = 0) (he1 : ‖coeff 1 e‖ = 1)
    (hm : ‖(m : ℂ_[q])‖ < 1) (h2 : 2 ≤ m) (ρ : ℂ_[q]⟦X⟧) (hρ : ρ ≠ 0) (h : ρ.subst e = ρ ^ m) :
    ∃ c : ℂ_[q], ρ = C c ∧ c ^ (m - 1) = 1 := by
  have hs : HasSubst e := HasSubst.of_constantCoeff_zero' he0
  obtain ⟨e', he'⟩ : (X : ℂ_[q]⟦X⟧) ∣ e := X_dvd_iff.2 he0
  have h'0 : constantCoeff e' = coeff 1 e := by
    rw [he', coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have ha : coeff 1 e ≠ 0 := by
    intro h0; rw [h0, norm_zero] at he1; exact zero_ne_one he1
  have hsub : ∀ (n : ℕ) (Q : ℂ_[q]⟦X⟧), (PowerSeries.subst e (X ^ n * Q : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧)
      = X ^ n * (e' ^ n * PowerSeries.subst e Q) := by
    intro n Q
    rw [subst_mul hs, subst_pow hs, subst_X hs]
    have : e ^ n = X ^ n * e' ^ n := by rw [he', mul_pow]
    rw [this]; ring
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hc : constantCoeff ρ ≠ 0 := by
    obtain ⟨n, Q, rfl, hQ⟩ := exists_fac hρ
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hQ
    exfalso
    rw [hsub] at h
    have h3 : e' ^ n * PowerSeries.subst e Q = X ^ n * (Q * Q * (X ^ n * Q) ^ k) := by
      apply mul_left_cancel₀ (pow_ne_zero n (X_ne_zero (R := ℂ_[q])))
      rw [h]; ring
    have h4 := congrArg constantCoeff h3
    rw [map_mul, map_mul, map_pow, map_pow, constantCoeff_X, zero_pow hn.ne', zero_mul, h'0,
      constantCoeff_subst_eq he0] at h4
    exact mul_ne_zero (pow_ne_zero _ ha) hQ h4
  set c := constantCoeff ρ with hcd
  have hc1 : c ^ (k + 1) = 1 := by
    have h4 := congrArg constantCoeff h
    rw [constantCoeff_subst_eq he0, map_pow, ← hcd] at h4
    apply mul_left_cancel₀ hc
    rw [mul_one]
    linear_combination -h4
  refine ⟨c, ?_, hc1⟩
  by_contra hne
  obtain ⟨n, Q, hf, hQ⟩ := exists_fac (sub_ne_zero.2 hne)
  have hn : n ≠ 0 := by
    rintro rfl
    apply hQ
    rw [pow_zero, one_mul] at hf
    rw [← hf, map_sub, constantCoeff_C, ← hcd, sub_self]
  have hL : (PowerSeries.subst e ρ : ℂ_[q]⟦X⟧) = C c + X ^ n * (e' ^ n * PowerSeries.subst e Q) := by
    have : ρ = C c + X ^ n * Q := by rw [← hf]; ring
    conv_lhs => rw [this, subst_add hs, hsub, subst_C_eq hs]
  have hR : ρ ^ (k + 2) = C c +
      X ^ n * (Q * (∑ i ∈ Finset.range (k + 2), ρ ^ i * (C c : ℂ_[q]⟦X⟧) ^ (k + 2 - 1 - i))) := by
    have := geom_sum₂_mul ρ (C c : ℂ_[q]⟦X⟧) (k + 2)
    rw [hf] at this
    have h5 : (C c : ℂ_[q]⟦X⟧) ^ (k + 2) = C c := by
      rw [← map_pow, pow_succ, hc1, one_mul]
    rw [h5] at this
    linear_combination -this
  rw [hL, hR] at h
  have h3 := mul_left_cancel₀ (pow_ne_zero n (X_ne_zero (R := ℂ_[q]))) (add_left_cancel h)
  have h4 := congrArg constantCoeff h3
  rw [map_mul, map_mul, map_pow, h'0, constantCoeff_subst_eq he0, map_sum,
    Finset.sum_congr rfl (g := fun _ => (1 : ℂ_[q])), Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, mul_comm] at h4
  · have h5 := congrArg norm (mul_left_cancel₀ hQ h4)
    rw [norm_pow, he1, one_pow] at h5
    exact hm.ne' h5
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow, map_pow, constantCoeff_C, ← hcd, ← pow_add, ← hc1]
    congr 1; omega

/- English proof (translation)
Introduce `q _ e m he0 he1 hm h2`. Use `⟨const_of_funEq e m he0 he1 hm h2, fun g ε he hε hg h => ?_⟩` and prove the remaining obligations. Establish `hε0 : constantCoeff ε = 1`. Establish `h4` using `congrArg constantCoeff h`. Rewrite `h4` using `[constantCoeff_subst_eq he0, map_mul, map_pow, hg, one_pow, one_mul]`.

Conclude with `h4.symm`. Establish `h1 : Bd 1 (1 : ℂ_[q]⟦X⟧)` using `by simpa using intSer_C (q := q) (c := 1) (by simp)`. Conclude with `intSer_of_funEq g e 1 ε m hg he he0 he1 hm h1 (by simp) hε hε0 (by rw [mul_one, h])`.
-/
theorem funEq_unique : ∀ (q : ℕ) [Fact q.Prime] (e : ℂ_[q]⟦X⟧) (m : ℕ), constantCoeff e = 0 → ‖coeff 1 e‖ = 1 → ‖(m : ℂ_[q])‖ < 1 → 2 ≤ m → (∀ ρ : ℂ_[q]⟦X⟧, ρ ≠ 0 → ρ.subst e = ρ ^ m → ∃ c : ℂ_[q], ρ = C c ∧ c ^ (m - 1) = 1) ∧ ∀ g ε : ℂ_[q]⟦X⟧, Bd 1 e → Bd 1 ε → constantCoeff g = 1 → g.subst e = g ^ m * ε → Bd 1 g := by
  intro q _ e m he0 he1 hm h2
  refine ⟨const_of_funEq e m he0 he1 hm h2, fun g ε he hε hg h => ?_⟩
  have hε0 : constantCoeff ε = 1 := by
    have h4 := congrArg constantCoeff h
    rw [constantCoeff_subst_eq he0, map_mul, map_pow, hg, one_pow, one_mul] at h4
    exact h4.symm
  have h1 : Bd 1 (1 : ℂ_[q]⟦X⟧) := by simpa using intSer_C (q := q) (c := 1) (by simp)
  exact intSer_of_funEq g e 1 ε m hg he he0 he1 hm h1 (by simp) hε hε0 (by rw [mul_one, h])

end GlobalTheory.MomOne.FeUniq
