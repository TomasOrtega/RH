import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.CrisTheta
import Development.AutomorphicArithmetic.TeichmullerLogarithm.CyclotomicPowSubOneNilpotent

open Ideal Reformulated.AutPerF

universe u

namespace UpperTheory.RingBr

/- English proof (translation)
Establish `h1 : 1 ∈ Finset.Ioo 0 p` using `Finset.mem_Ioo.2 ⟨one_pos, hp.one_lt⟩`. Establish `h` using `add_pow_prime_eq hp x 1`. Rewrite `h` using `[← Finset.add_sum_erase _ _ h1]`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : x ∣ ∑ k ∈ (Finset.Ioo 0 p).erase 1, x ^ (k - 1) * 1 ^ (p - k - 1) * ((p.choose k / p : ℕ) : A) := by`. Use `Finset.dvd_sum fun k hk => ?_` and prove the remaining obligations.

Rewrite `hk` using `[Finset.mem_erase, Finset.mem_Ioo]`. Conclude with `((dvd_pow_self x (by omega)).mul_right _).mul_right _`. Rewrite `h` using `[hy, Nat.choose_one_right, Nat.div_self hp.pos]`. Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `h2 : x ^ p = x * x ^ (p - 1)`.

Rewrite using `[← pow_succ', Nat.sub_add_cancel hp.one_lt.le]`. Rewrite using `[h, h2]`. Simplify using `only [Nat.sub_self, pow_zero, one_pow, Nat.cast_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_add_one_pow {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime) (x : A) :
    ∃ y : A, (x + 1) ^ p - 1 = x * (p + p * x * y + x ^ (p - 1)) := by
  have h1 : 1 ∈ Finset.Ioo 0 p := Finset.mem_Ioo.2 ⟨one_pos, hp.one_lt⟩
  have h := add_pow_prime_eq hp x 1
  rw [← Finset.add_sum_erase _ _ h1] at h
  obtain ⟨y, hy⟩ : x ∣ ∑ k ∈ (Finset.Ioo 0 p).erase 1,
      x ^ (k - 1) * 1 ^ (p - k - 1) * ((p.choose k / p : ℕ) : A) := by
    refine Finset.dvd_sum fun k hk => ?_
    rw [Finset.mem_erase, Finset.mem_Ioo] at hk
    exact ((dvd_pow_self x (by omega)).mul_right _).mul_right _
  rw [hy, Nat.choose_one_right, Nat.div_self hp.pos] at h
  refine ⟨y, ?_⟩
  have h2 : x ^ p = x * x ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hp.one_lt.le]
  rw [h, h2]
  simp only [Nat.sub_self, pow_zero, one_pow, Nat.cast_one]
  ring

/- English proof (translation)
Establish `hp2` using `hp.two_le`. Take `⟨y, hy⟩` from `exists_add_one_pow hp (u ^ p ^ n - 1)`. Rewrite `hy` using `[sub_add_cancel, ← pow_mul, ← pow_succ]`. Establish `hx : θ (u ^ p ^ n - 1) = 0` using `by simp [hu]`. Generalize the expression as in `u ^ p ^ n - 1 = x at h1 hy hx`.

Choose the witnesses or unpack the hypotheses as in `⟨w, hw, hw'⟩ : ∃ w : A, x ^ (p - 1) = p * w ∧ (p : A) ^ (n - 1) ∣ w := by`. Break down `n with _ | n` into its components or cases. Take `⟨w, hw⟩` from `h`. Use `⟨w * V ^ (p - 1), ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[← h1, pow_zero, one_mul, mul_pow, hw, mul_assoc]`.

Use `⟨p ^ n * ((u - 1) * V) * x ^ (p - 2), ?_, (dvd_mul_right _ _).mul_right _⟩` and prove the remaining obligations. Rewrite using `[show p - 1 = (p - 2) + 1 by omega, pow_succ' x]`. Take the linear combination `(-x ^ (p - 2)) * h1`. Establish `hθw : θ w = 0`. Use `congrArg θ hw` as an intermediate fact.

Rewrite `this` using `[map_pow, hx, zero_pow (by omega), map_mul, map_natCast]`. Conclude with `(mul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 hp.ne_zero)`. Use `⟨V * (1 + x * y + w), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hy, hw]`. Take the linear combination `(p + p * x * y + p * w) * h1`.

Simplify using `[h2, hx, hθw]`. Establish `hd : (p : A) ^ (n - 1) ∣ x` using `(pow_dvd_pow _ (Nat.sub_le n 1)).trans ⟨_, h1.symm⟩`. Rewrite using `[show V * (1 + x * y + w) - V = V * (x * y + w) by ring]`. Conclude with `(dvd_add (hd.mul_right _) hw').mul_left _`.
-/
private theorem step {A B : Type*} [CommRing A] [CommRing B] [IsDomain B] [CharZero B] {p : ℕ}
    (hp : p.Prime) (θ : A →+* B) (u : A) (hu : θ u = 1) (h : (p : A) ∣ (u - 1) ^ (p - 1)) (n : ℕ)
    (V : A) (h1 : (p : A) ^ n * ((u - 1) * V) = u ^ p ^ n - 1) (h2 : θ V = 1) :
    ∃ V' : A, ((p : A) ^ (n + 1) * ((u - 1) * V') = u ^ p ^ (n + 1) - 1 ∧ θ V' = 1) ∧
      (p : A) ^ (n - 1) ∣ V' - V := by
  have hp2 := hp.two_le
  obtain ⟨y, hy⟩ := exists_add_one_pow hp (u ^ p ^ n - 1)
  rw [sub_add_cancel, ← pow_mul, ← pow_succ] at hy
  have hx : θ (u ^ p ^ n - 1) = 0 := by simp [hu]
  generalize u ^ p ^ n - 1 = x at h1 hy hx
  obtain ⟨w, hw, hw'⟩ : ∃ w : A, x ^ (p - 1) = p * w ∧ (p : A) ^ (n - 1) ∣ w := by
    rcases n with _ | n
    · obtain ⟨w, hw⟩ := h
      refine ⟨w * V ^ (p - 1), ?_, by simp⟩
      rw [← h1, pow_zero, one_mul, mul_pow, hw, mul_assoc]
    · refine ⟨p ^ n * ((u - 1) * V) * x ^ (p - 2), ?_, (dvd_mul_right _ _).mul_right _⟩
      rw [show p - 1 = (p - 2) + 1 by omega, pow_succ' x]
      linear_combination (-x ^ (p - 2)) * h1
  have hθw : θ w = 0 := by
    have := congrArg θ hw
    rw [map_pow, hx, zero_pow (by omega), map_mul, map_natCast] at this
    exact (mul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 hp.ne_zero)
  refine ⟨V * (1 + x * y + w), ⟨?_, ?_⟩, ?_⟩
  · rw [hy, hw]
    linear_combination (p + p * x * y + p * w) * h1
  · simp [h2, hx, hθw]
  · have hd : (p : A) ^ (n - 1) ∣ x := (pow_dvd_pow _ (Nat.sub_le n 1)).trans ⟨_, h1.symm⟩
    rw [show V * (1 + x * y + w) - V = V * (x * y + w) by ring]
    exact (dvd_add (hd.mul_right _) hw').mul_left _

/- English proof (translation)
Use `choose F hF hF' using step hp θ u hu h`. Set `S : ∀ n : ℕ, {V : A // (p : A) ^ n * ((u - 1) * V) = u ^ p ^ n - 1 ∧ θ V = 1}` to `fun n => Nat.rec ⟨1, by simp, map_one _⟩ (fun n V => ⟨F n V.1 V.2.1 V.2.2, hF _ _ _ _⟩) n`. Establish `hS : ∀ n, (p : A) ^ n ∣ (S (n + 1 + 1)).1 - (S (n + 1)).1` using `fun n => hF' (n + 1) (S (n + 1)).1 (S (n + 1)).2.1 (S (n + 1)).2.2`. Establish `hS' : ∀ m n, m ≤ n → (p : A) ^ m ∣ (S (m + 1)).1 - (S (n + 1)).1`. Introduce `m n hmn`.

Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ n hmn ih`. Use `dvd_sub ih ((pow_dvd_pow _ hmn).trans (hS n))` as an intermediate fact. Rewrite `this` using `[sub_sub, add_sub_cancel]`. Then use the resulting hypothesis.

Take `⟨v, hv⟩` from `IsPrecomplete.prec (I := span {(p : A)}) (M := A) inferInstance (f := fun n => (S (n + 1)).1) (by`. Introduce `m n hmn`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `hS' m n hmn)`. Establish `hv' : ∀ n, (p : A) ^ n ∣ (S (n + 1)).1 - v` using `fun n => by`.

Use `hv n` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Then use the resulting hypothesis. Use `⟨v, ?_, fun n => ⟨_, (S (n + 1)).2.1, hv' n⟩⟩` and prove the remaining obligations. Use `symm`. Rewrite using `[IsHausdorff.eq_iff_smodEq (I := span {(p : B)})]`.

Introduce `n`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Use `map_dvd θ (hv' n)` as an intermediate fact. Rewrite `this` using `[map_pow, map_natCast, map_sub, (S (n + 1)).2.2]`. Then use the resulting hypothesis.
-/
private theorem exists_limit {A B : Type*} [CommRing A] [CommRing B] [IsDomain B] [CharZero B]
    {p : ℕ} (hp : p.Prime) [IsAdicComplete (span {(p : A)}) A] [IsHausdorff (span {(p : B)}) B]
    (θ : A →+* B) (u : A) (hu : θ u = 1) (h : (p : A) ∣ (u - 1) ^ (p - 1)) :
    ∃ v : A, θ v = 1 ∧ ∀ n, ∃ V : A,
      (p : A) ^ (n + 1) * ((u - 1) * V) = u ^ p ^ (n + 1) - 1 ∧ (p : A) ^ n ∣ V - v := by
  choose F hF hF' using step hp θ u hu h
  let S : ∀ n : ℕ, {V : A // (p : A) ^ n * ((u - 1) * V) = u ^ p ^ n - 1 ∧ θ V = 1} := fun n =>
    Nat.rec ⟨1, by simp, map_one _⟩ (fun n V => ⟨F n V.1 V.2.1 V.2.2, hF _ _ _ _⟩) n
  have hS : ∀ n, (p : A) ^ n ∣ (S (n + 1 + 1)).1 - (S (n + 1)).1 := fun n =>
    hF' (n + 1) (S (n + 1)).1 (S (n + 1)).2.1 (S (n + 1)).2.2
  have hS' : ∀ m n, m ≤ n → (p : A) ^ m ∣ (S (m + 1)).1 - (S (n + 1)).1 := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := dvd_sub ih ((pow_dvd_pow _ hmn).trans (hS n))
      rwa [sub_sub, add_sub_cancel] at this
  obtain ⟨v, hv⟩ := IsPrecomplete.prec (I := span {(p : A)}) (M := A) inferInstance
    (f := fun n => (S (n + 1)).1) (by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      exact hS' m n hmn)
  have hv' : ∀ n, (p : A) ^ n ∣ (S (n + 1)).1 - v := fun n => by
    have := hv n
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at this
  refine ⟨v, ?_, fun n => ⟨_, (S (n + 1)).2.1, hv' n⟩⟩
  symm
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : B)})]
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  have := map_dvd θ (hv' n)
  rwa [map_pow, map_natCast, map_sub, (S (n + 1)).2.2] at this

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable [IsDomain R] [ValuationRing R] [CharZero R] [IsAlgClosed (FractionRing R)]

/- English proof (translation)
Establish `hu : Ainf.theta p R (Ainf.teich p η.1) = 1`. Rewrite using `[Ainf.theta_teich]`. Conclude with `η.2`. Establish `hd` using `p_dvd_mu_pow η`. Rewrite `hd`, the goal using `[map_sub, map_one]`.

Take `⟨v, hv, hv'⟩` from `exists_limit (Fact.out : p.Prime) (Acris.theta p R) _ (by rw [Acris.theta_algebraMap, hu]) hd`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Acris.log (Ainf.teich p η.1) hu = _`. Generalize the expression as in `Ainf.teich p η.1 = u at hu hv'`. Rewrite using `[← sub_eq_zero]`.

Use `Acris.eq_zero_of_forall_dvd fun n => ?_` and prove the remaining obligations. Take `⟨V, hV, hV'⟩` from `hv' n`. Take `⟨l, hl, hl'⟩` from `Acris.exists_quot u hu (n + 1)`. Establish `h1 : (p : Acris p R) ^ (n + 1) ∣ Acris.log u hu - algebraMap _ _ l`. Rewrite using `[← Acris.eval_eq_zero_iff, map_sub, hl', Acris.eval_algebraMap, sub_self]`.

Establish `h2` using `congrArg (algebraMap (AcrisZero p R) (Acris p R)) hl`. Rewrite `h2` using `[map_mul, map_pow, map_natCast, map_sub, map_pow, map_one, ← IsScalarTower.algebraMap_apply, ← hV]`. Rewrite `h1` using `[Acris.p_pow_mul_cancel _ h2]`. Establish `h3` using `dvd_add ((pow_dvd_pow _ (Nat.le_succ n)).trans h1) (hV'.mul_left (algebraMap (Ainf p R) (Acris p R) u - 1))`. Use `h3 using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_logTeich_eq_mu_mul (η : tateModule p R) :
    ∃ v : Acris p R, Acris.theta p R v = 1 ∧ Acris.logTeich η = algebraMap (Ainf p R) (Acris p R) (Ainf.teich p η.1 - 1) * v := by
  have hu : Ainf.theta p R (Ainf.teich p η.1) = 1 := by
    rw [Ainf.theta_teich]; exact η.2
  have hd := p_dvd_mu_pow η
  rw [map_sub, map_one] at hd ⊢
  obtain ⟨v, hv, hv'⟩ := exists_limit (Fact.out : p.Prime) (Acris.theta p R) _
    (by rw [Acris.theta_algebraMap, hu]) hd
  refine ⟨v, hv, ?_⟩
  change Acris.log (Ainf.teich p η.1) hu = _
  generalize Ainf.teich p η.1 = u at hu hv'
  rw [← sub_eq_zero]
  refine Acris.eq_zero_of_forall_dvd fun n => ?_
  obtain ⟨V, hV, hV'⟩ := hv' n
  obtain ⟨l, hl, hl'⟩ := Acris.exists_quot u hu (n + 1)
  have h1 : (p : Acris p R) ^ (n + 1) ∣ Acris.log u hu - algebraMap _ _ l := by
    rw [← Acris.eval_eq_zero_iff, map_sub, hl', Acris.eval_algebraMap, sub_self]
  have h2 := congrArg (algebraMap (AcrisZero p R) (Acris p R)) hl
  rw [map_mul, map_pow, map_natCast, map_sub, map_pow, map_one, ← IsScalarTower.algebraMap_apply,
    ← hV] at h2
  rw [Acris.p_pow_mul_cancel _ h2] at h1
  have h3 := dvd_add ((pow_dvd_pow _ (Nat.le_succ n)).trans h1)
    (hV'.mul_left (algebraMap (Ainf p R) (Acris p R) u - 1))
  convert h3 using 1
  ring

end UpperTheory.RingBr
