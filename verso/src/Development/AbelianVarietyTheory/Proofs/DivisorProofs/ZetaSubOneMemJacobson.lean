import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff

set_option autoImplicit false

open CategoryTheory WittVector GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published GlobalTheory.PerfdLat
open scoped ChangeOfRings Pointwise

namespace GlobalTheory.PerfdLat.CycElem

/- English proof (translation)
Establish `h` using `(Commute.one_right x).add_pow_prime_eq' hp`. Establish `h1 : 1 ∈ Finset.Ioo 0 p` using `Finset.mem_Ioo.2 ⟨one_pos, hp.one_lt⟩`. Rewrite `h` using `[← Finset.add_sum_erase _ _ h1]`. Establish `h2 : x ^ 2 ∣ ∑ k ∈ (Finset.Ioo 0 p).erase 1, x ^ k * 1 ^ (p - k) * ((p.choose k / p : ℕ) : R)` using `Finset.dvd_sum fun k hk => by`. Establish `h3` using `Finset.mem_erase.1 hk`.

Establish `h4` using `Finset.mem_Ioo.1 h3.2`. Conclude with `((pow_dvd_pow x (by omega)).mul_right _).mul_right _`. Take `⟨s, hs⟩` from `h2`. Rewrite `h` using `[hs, Nat.choose_one_right, Nat.div_self hp.pos]`. Conclude with `⟨s, by rw [h]; simp only [one_pow, Nat.cast_one]; ring⟩`.
-/
theorem exists_add_one_pow {R : Type} [CommRing R] {p : ℕ} (hp : p.Prime) (x : R) :
    ∃ s : R, (x + 1) ^ p = x ^ p + 1 + p * x * (x * s + 1) := by
  have h := (Commute.one_right x).add_pow_prime_eq' hp
  have h1 : 1 ∈ Finset.Ioo 0 p := Finset.mem_Ioo.2 ⟨one_pos, hp.one_lt⟩
  rw [← Finset.add_sum_erase _ _ h1] at h
  have h2 : x ^ 2 ∣ ∑ k ∈ (Finset.Ioo 0 p).erase 1, x ^ k * 1 ^ (p - k) * ((p.choose k / p : ℕ) : R) :=
    Finset.dvd_sum fun k hk => by
      have h3 := Finset.mem_erase.1 hk
      have h4 := Finset.mem_Ioo.1 h3.2
      exact ((pow_dvd_pow x (by omega)).mul_right _).mul_right _
  obtain ⟨s, hs⟩ := h2
  rw [hs, Nat.choose_one_right, Nat.div_self hp.pos] at h
  exact ⟨s, by rw [h]; simp only [one_pow, Nat.cast_one]; ring⟩

variable {p : ℕ} [Fact p.Prime] (S : CycPerfd p)

/- English proof (translation)
Establish `h : phiInv p S.R a ^ p - a ∈ Ideal.span {(p : Ainf p S.R)}`. Rewrite using `[WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← constantCoeff_apply, map_sub, map_pow, sub_eq_zero]`. Use `conv_rhs => rw [← Dieudonne.frobenius_phiInv a]`. Rewrite using `[constantCoeff_apply, constantCoeff_apply, coeff_frobenius_charP]`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 h`.

Rewrite using `[← map_pow, ← map_pow, Ideal.Quotient.eq, ← map_sub, ← hc, map_mul, map_natCast]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)`.
-/
theorem theta_phiInv_pow (a : Ainf p S.R) :
    Ideal.Quotient.mk (Ideal.span {(p : S.R)}) (fontaineTheta S.R p (phiInv p S.R a)) ^ p =
      Ideal.Quotient.mk _ (fontaineTheta S.R p a) := by
  have h : phiInv p S.R a ^ p - a ∈ Ideal.span {(p : Ainf p S.R)} := by
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← constantCoeff_apply, map_sub, map_pow, sub_eq_zero]
    conv_rhs => rw [← Dieudonne.frobenius_phiInv a]
    rw [constantCoeff_apply, constantCoeff_apply, coeff_frobenius_charP]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  rw [← map_pow, ← map_pow, Ideal.Quotient.eq, ← map_sub, ← hc, map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/- English proof (translation)
Rewrite using `[← Ideal.Quotient.eq, map_pow]`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [Function.iterate_succ_apply', pow_succ', pow_mul, theta_phiInv_pow, ih]`.
-/
theorem theta_phiInv_iterate_pow (n : ℕ) (a : Ainf p S.R) :
    fontaineTheta S.R p ((phiInv p S.R)^[n] a) ^ p ^ n - fontaineTheta S.R p a ∈ Ideal.span {(p : S.R)} := by
  rw [← Ideal.Quotient.eq, map_pow]
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', pow_succ', pow_mul, theta_phiInv_pow, ih]

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_add_one_pow (Fact.out : p.Prime) (zeta S.ε (k + 1) - 1)`. Rewrite `hs` using `[sub_add_cancel, zeta_succ_pow]`. Conclude with `⟨s, by linear_combination hs⟩`.
-/
theorem exists_zeta_sub_one (k : ℕ) : ∃ s : S.R, zeta S.ε k - 1 =
    (zeta S.ε (k + 1) - 1) ^ p + p * (zeta S.ε (k + 1) - 1) * ((zeta S.ε (k + 1) - 1) * s + 1) := by
  obtain ⟨s, hs⟩ := exists_add_one_pow (Fact.out : p.Prime) (zeta S.ε (k + 1) - 1)
  rw [sub_add_cancel, zeta_succ_pow] at hs
  exact ⟨s, by linear_combination hs⟩

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [S.zeta_zero]`. Consider the case `succ k ih`. Take `⟨s, hs⟩` from `exists_zeta_sub_one S k`. Establish `hp : (p : S.R) ∈ (⊥ : Ideal S.R).jacobson` using `IsAdicComplete.le_jacobson_bot (Ideal.span {(p : S.R)}) (Ideal.mem_span_singleton_self _)`.

Use `Ideal.isRadical_jacobson ⊥ ⟨p, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_sub_of_add_eq hs.symm, mul_assoc]`. Conclude with `sub_mem ih (Ideal.mul_mem_right _ _ hp)`.
-/
theorem zeta_sub_one_mem_jacobson (k : ℕ) : zeta S.ε k - 1 ∈ (⊥ : Ideal S.R).jacobson := by
  induction k with
  | zero => simp [S.zeta_zero]
  | succ k ih =>
    obtain ⟨s, hs⟩ := exists_zeta_sub_one S k
    have hp : (p : S.R) ∈ (⊥ : Ideal S.R).jacobson :=
      IsAdicComplete.le_jacobson_bot (Ideal.span {(p : S.R)}) (Ideal.mem_span_singleton_self _)
    refine Ideal.isRadical_jacobson ⊥ ⟨p, ?_⟩
    rw [eq_sub_of_add_eq hs.symm, mul_assoc]
    exact sub_mem ih (Ideal.mul_mem_right _ _ hp)

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_zeta_sub_one S 0`. Establish `hu` using `(Ideal.mem_jacobson_bot.1 (zeta_sub_one_mem_jacobson S 1) s).neg`. Rewrite `hs` using `[S.zeta_zero, sub_self, zero_add]`. Establish `h : (zeta S.ε 1 - 1) ^ (p - 1) = p * -((zeta S.ε 1 - 1) * s + 1)`. Apply `isSMulRegular_zeta_sub_one S 0` to reduce the goal to its premises.

Simplify using `only [smul_eq_mul, zero_add]`. Rewrite using `[← pow_succ', Nat.sub_add_cancel (Fact.out : p.Prime).one_le]`. Take the linear combination `-hs`. Rewrite using `[h]`. Conclude with `associated_mul_unit_left _ _ hu`.
-/
theorem associated_zeta_one : Associated ((zeta S.ε 1 - 1) ^ (p - 1)) (p : S.R) := by
  obtain ⟨s, hs⟩ := exists_zeta_sub_one S 0
  have hu := (Ideal.mem_jacobson_bot.1 (zeta_sub_one_mem_jacobson S 1) s).neg
  rw [S.zeta_zero, sub_self, zero_add] at hs
  have h : (zeta S.ε 1 - 1) ^ (p - 1) = p * -((zeta S.ε 1 - 1) * s + 1) := by
    apply isSMulRegular_zeta_sub_one S 0
    simp only [smul_eq_mul, zero_add]
    rw [← pow_succ', Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
    linear_combination -hs
  rw [h]
  exact associated_mul_unit_left _ _ hu

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_zeta_sub_one S (k + 1)`. Take `⟨t, ht⟩` from `(zeta_sub_one_dvd S k).trans (zeta_one_sub_one_dvd S)`. Establish `hu` using `Ideal.mem_jacobson_bot.1 (zeta_sub_one_mem_jacobson S (k + 2)) (-(t * ((zeta S.ε (k + 2) - 1) * s + 1)))`. Establish `h : (zeta S.ε (k + 2) - 1) ^ p = (zeta S.ε (k + 1) - 1) * ((zeta S.ε (k + 2) - 1) * -(t * ((zeta S.ε (k + 2) - 1) * s + 1)) + 1)`. Rewrite `hs` using `[ht]`.

Take the linear combination `-hs`. Rewrite using `[h]`. Conclude with `associated_mul_unit_left _ _ hu`.
-/
theorem associated_zeta_succ (k : ℕ) : Associated ((zeta S.ε (k + 2) - 1) ^ p) (zeta S.ε (k + 1) - 1) := by
  obtain ⟨s, hs⟩ := exists_zeta_sub_one S (k + 1)
  obtain ⟨t, ht⟩ := (zeta_sub_one_dvd S k).trans (zeta_one_sub_one_dvd S)
  have hu := Ideal.mem_jacobson_bot.1 (zeta_sub_one_mem_jacobson S (k + 2))
    (-(t * ((zeta S.ε (k + 2) - 1) * s + 1)))
  have h : (zeta S.ε (k + 2) - 1) ^ p = (zeta S.ε (k + 1) - 1) *
      ((zeta S.ε (k + 2) - 1) * -(t * ((zeta S.ε (k + 2) - 1) * s + 1)) + 1) := by
    rw [ht] at hs
    linear_combination -hs
  rw [h]
  exact associated_mul_unit_left _ _ hu

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ', pow_mul]`. Conclude with `(associated_zeta_succ S k).pow_pow.trans ih`.
-/
theorem associated_zeta_pow (k : ℕ) : Associated ((zeta S.ε (k + 1) - 1) ^ p ^ k) (zeta S.ε 1 - 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul]; exact (associated_zeta_succ S k).pow_pow.trans ih

/- English proof (translation)
Rewrite using `[← theta_muN, ← map_mul, xiN_mul_muN, theta_muN]`.
-/
theorem theta_xiN_mul (n : ℕ) :
    fontaineTheta S.R p (xiN S n) * (zeta S.ε (n + 1) - 1) = zeta S.ε n - 1 := by
  rw [← theta_muN, ← map_mul, xiN_mul_muN, theta_muN]

/- English proof (translation)
Take `⟨u, hu⟩` from `(associated_zeta_succ S n).symm`. Use `⟨u, isSMulRegular_zeta_sub_one S (n + 1) ?_⟩` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`. Rewrite using `[← pow_succ', Nat.sub_add_cancel (Fact.out : p.Prime).one_le, ← hu, ← theta_xiN_mul S (n + 1)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem associated_theta_xiN (n : ℕ) :
    Associated (fontaineTheta S.R p (xiN S (n + 1))) ((zeta S.ε (n + 2) - 1) ^ (p - 1)) := by
  obtain ⟨u, hu⟩ := (associated_zeta_succ S n).symm
  refine ⟨u, isSMulRegular_zeta_sub_one S (n + 1) ?_⟩
  simp only [smul_eq_mul]
  rw [← pow_succ', Nat.sub_add_cancel (Fact.out : p.Prime).one_le, ← hu, ← theta_xiN_mul S (n + 1)]
  ring

/- English proof (translation)
Use `(associated_theta_xiN S n).pow_pow.trans ?_` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm, pow_mul]`. Conclude with `(associated_zeta_pow S (n + 1)).pow_pow.trans (associated_zeta_one S)`.
-/
theorem associated_theta_xiN_pow (n : ℕ) :
    Associated (fontaineTheta S.R p (xiN S (n + 1)) ^ p ^ (n + 1)) (p : S.R) := by
  refine (associated_theta_xiN S n).pow_pow.trans ?_
  rw [← pow_mul, mul_comm, pow_mul]
  exact (associated_zeta_pow S (n + 1)).pow_pow.trans (associated_zeta_one S)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [Function.iterate_succ_apply', ih, phiInv_xiN]`.
-/
theorem phiInv_iterate_xi (n : ℕ) : (phiInv p S.R)^[n] (xi S.ε) = xiN S n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, phiInv_xiN]

/- English proof (translation)
Set `f : Ainf p S.R →+* S.R ⧸ Ideal.span {fontaineTheta S.R p (xiN S n)}` to `(Ideal.Quotient.mk _).comp ((fontaineTheta S.R p).comp (phiInv p S.R ^ n))`. Establish `hf : ∀ a, f a = Ideal.Quotient.mk _ (fontaineTheta S.R p ((phiInv p S.R)^[n] a))` using `fun a => by`. Simplify using `only [f, RingHom.comp_apply, RingHom.coe_pow]`. Establish `hk : RingHom.ker (fontaineTheta S.R p) ≤ RingHom.ker f`. Rewrite using `[S.ker_eq, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, hf, phiInv_iterate_xi, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `Ideal.mem_span_singleton_self _`. Conclude with `⟨(fontaineTheta S.R p).liftOfSurjective S.surj ⟨f, hk⟩, fun a => (RingHom.liftOfRightInverse_comp_apply ..).trans (hf a)⟩`.
-/
theorem exists_ringHom (n : ℕ) : ∃ s : S.R →+* S.R ⧸ Ideal.span {fontaineTheta S.R p (xiN S n)},
    ∀ a : Ainf p S.R, s (fontaineTheta S.R p a) =
      Ideal.Quotient.mk _ (fontaineTheta S.R p ((phiInv p S.R)^[n] a)) := by
  let f : Ainf p S.R →+* S.R ⧸ Ideal.span {fontaineTheta S.R p (xiN S n)} :=
    (Ideal.Quotient.mk _).comp ((fontaineTheta S.R p).comp (phiInv p S.R ^ n))
  have hf : ∀ a, f a = Ideal.Quotient.mk _ (fontaineTheta S.R p ((phiInv p S.R)^[n] a)) := fun a => by
    simp only [f, RingHom.comp_apply, RingHom.coe_pow]
  have hk : RingHom.ker (fontaineTheta S.R p) ≤ RingHom.ker f := by
    rw [S.ker_eq, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, hf, phiInv_iterate_xi,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  exact ⟨(fontaineTheta S.R p).liftOfSurjective S.surj ⟨f, hk⟩, fun a =>
    (RingHom.liftOfRightInverse_comp_apply ..).trans (hf a)⟩

/- English proof (translation)
Introduce `p _ S n`. Use `⟨theta_phiInv_iterate_pow S n, ?_, ?_, exists_ringHom S (n + 1)⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `(associated_theta_xiN_pow S n).symm`. Conclude with `⟨u, by rw [← hu, mul_comm]⟩`. Conclude with `IsSMulRegular.of_mul (a := zeta S.ε (n + 2) - 1) (by rw [mul_comm, theta_xiN_mul]; exact isSMulRegular_zeta_sub_one S n)`.
-/
theorem theta_xiN_facts : ∀ (p : ℕ) [Fact p.Prime] (S : CycPerfd p) (n : ℕ),
    (∀ a : Ainf p S.R, fontaineTheta S.R p ((phiInv p S.R)^[n] a) ^ p ^ n - fontaineTheta S.R p a ∈
      Ideal.span {(p : S.R)}) ∧
    (∃ u : (S.R)ˣ, fontaineTheta S.R p (xiN S (n + 1)) ^ p ^ (n + 1) = u * (p : S.R)) ∧
    IsSMulRegular S.R (fontaineTheta S.R p (xiN S (n + 1))) ∧
    ∃ s : S.R →+* S.R ⧸ Ideal.span {fontaineTheta S.R p (xiN S (n + 1))}, ∀ a : Ainf p S.R,
      s (fontaineTheta S.R p a) = Ideal.Quotient.mk _ (fontaineTheta S.R p ((phiInv p S.R)^[n + 1] a)) := by
  intro p _ S n
  refine ⟨theta_phiInv_iterate_pow S n, ?_, ?_, exists_ringHom S (n + 1)⟩
  · obtain ⟨u, hu⟩ := (associated_theta_xiN_pow S n).symm
    exact ⟨u, by rw [← hu, mul_comm]⟩
  · exact IsSMulRegular.of_mul (a := zeta S.ε (n + 2) - 1)
      (by rw [mul_comm, theta_xiN_mul]; exact isSMulRegular_zeta_sub_one S n)

end GlobalTheory.PerfdLat.CycElem
