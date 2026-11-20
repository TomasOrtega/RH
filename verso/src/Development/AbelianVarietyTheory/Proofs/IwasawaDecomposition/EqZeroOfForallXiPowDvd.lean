import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.XiHaus
variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
The claim follows from `PreTilt.isDomain ℂ_[l] Valued.v (Per.OC l) (PadicComplexInt.integers l) l`.
-/
theorem isDomain_Fl : IsDomain (Per.Fl l) :=
  PreTilt.isDomain ℂ_[l] Valued.v (Per.OC l) (PadicComplexInt.integers l) l

/- English proof (translation)
Proceed by induction on `k generalizing x with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, pow_mul, map_pow, PreTilt.coeff_pow_p, ih]`.
-/
theorem coeff_pow_pow (x : Per.Fl l) (k : ℕ) :
    PreTilt.coeff k (x ^ l ^ k) = PreTilt.coeff 0 x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, map_pow, PreTilt.coeff_pow_p, ih]

/- English proof (translation)
Rewrite using `[← WittVector.constantCoeff_apply, xi, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]`.
-/
theorem xi_coeff_zero (e : Per.Fl l) :
    (xi e).coeff 0 = ∑ i ∈ Finset.range l, ((frobeniusEquiv (Per.Fl l) l).symm e) ^ i := by
  rw [← WittVector.constantCoeff_apply, xi, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem root_pow (e : Per.Fl l) : ((frobeniusEquiv (Per.Fl l) l).symm e) ^ l = e := by
  simp

/- English proof (translation)
Introduce `h`. Establish `h1` using `geom_sum_mul ((frobeniusEquiv (Per.Fl l) l).symm e) l`. Rewrite `h1` using `[← xi_coeff_zero, h, zero_mul, root_pow, eq_comm, sub_eq_zero]`. Conclude with `he.2 (by rw [h1, map_one, map_one])`.
-/
theorem xi_coeff_zero_ne {e : Per.Fl l} (he : IsEps e) : (xi e).coeff 0 ≠ 0 := by
  intro h
  have h1 := geom_sum_mul ((frobeniusEquiv (Per.Fl l) l).symm e) l
  rw [← xi_coeff_zero, h, zero_mul, root_pow, eq_comm, sub_eq_zero] at h1
  exact he.2 (by rw [h1, map_one, map_one])

/- English proof (translation)
Use `set u := (frobeniusEquiv (Per.Fl l) l).symm e with hu`. Establish `hy : (u - 1) ∣ (xi e).coeff 0`. Rewrite using `[xi_coeff_zero, ← hu]`. Establish `: ∑ i ∈ Finset.range l, u ^ i = ∑ i ∈ Finset.range l, (u ^ i - 1 ^ i)`. Simplify using `[Finset.sum_sub_distrib]`.

Rewrite using `[this]`. Conclude with `Finset.dvd_sum fun i _ => sub_dvd_pow_sub_pow u 1 i`. Establish `h0 : PreTilt.coeff 0 ((u - 1) ^ l) = 0`. Rewrite using `[sub_pow_char, hu, root_pow, one_pow, map_sub, ← PreTilt.mk_untilt_eq_coeff_zero, he.1, map_one, map_one, sub_self]`. Use `Perfection.ext fun k => ?_` and prove the remaining obligations.

Take `⟨c, hc⟩` from `(pow_dvd_pow_of_dvd hy (l * l ^ k)).trans (hb _)`. Express the relevant statement in the definitionally equal form `PreTilt.coeff k b = PreTilt.coeff k 0`. Rewrite using `[hc, map_mul, pow_mul, coeff_pow_pow, h0, zero_mul, map_zero]`.
-/
theorem eq_zero_of_dvd {e : Per.Fl l} (he : IsEps e) (b : Per.Fl l)
    (hb : ∀ n : ℕ, ((xi e).coeff 0) ^ n ∣ b) : b = 0 := by
  set u := (frobeniusEquiv (Per.Fl l) l).symm e with hu
  have hy : (u - 1) ∣ (xi e).coeff 0 := by
    rw [xi_coeff_zero, ← hu]
    have : ∑ i ∈ Finset.range l, u ^ i = ∑ i ∈ Finset.range l, (u ^ i - 1 ^ i) := by
      simp [Finset.sum_sub_distrib]
    rw [this]
    exact Finset.dvd_sum fun i _ => sub_dvd_pow_sub_pow u 1 i
  have h0 : PreTilt.coeff 0 ((u - 1) ^ l) = 0 := by
    rw [sub_pow_char, hu, root_pow, one_pow, map_sub, ← PreTilt.mk_untilt_eq_coeff_zero, he.1,
      map_one, map_one, sub_self]
  refine Perfection.ext fun k => ?_
  obtain ⟨c, hc⟩ := (pow_dvd_pow_of_dvd hy (l * l ^ k)).trans (hb _)
  change PreTilt.coeff k b = PreTilt.coeff k 0
  rw [hc, map_mul, pow_mul, coeff_pow_pow, h0, zero_mul, map_zero]

/- English proof (translation)
Use `isDomain_Fl (l := l)` as an intermediate fact. Take `⟨c, hc⟩` from `h`. Establish `h1` using `congrArg WittVector.constantCoeff hc`. Rewrite `h1` using `[map_mul, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, map_pow, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply]`. Establish `h2 : c.coeff 0 = 0` using `(mul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ (xi_coeff_zero_ne he))`.

Take `⟨d, rfl⟩` from `Ideal.mem_span_singleton.1 ((WittVector.mem_span_p_iff_coeff_zero_eq_zero c).2 h2)`. Use `⟨d, mul_left_cancel₀ (WittVector.p_nonzero l (Per.Fl l)) ?_⟩` and prove the remaining obligations. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem xi_sat {e : Per.Fl l} (he : IsEps e) (n : ℕ) (a : Per.Ainf l)
    (h : xi e ^ n ∣ (l : Per.Ainf l) * a) : xi e ^ n ∣ a := by
  have := isDomain_Fl (l := l)
  obtain ⟨c, hc⟩ := h
  have h1 := congrArg WittVector.constantCoeff hc
  rw [map_mul, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, map_pow,
    WittVector.constantCoeff_apply, WittVector.constantCoeff_apply] at h1
  have h2 : c.coeff 0 = 0 :=
    (mul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ (xi_coeff_zero_ne he))
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.1
    ((WittVector.mem_span_p_iff_coeff_zero_eq_zero c).2 h2)
  refine ⟨d, mul_left_cancel₀ (WittVector.p_nonzero l (Per.Fl l)) ?_⟩
  rw [hc]; ring

end GlobalTheory.MemLoc.XiHaus

namespace GlobalTheory.MemLoc
open XiHaus in

/- English proof (translation)
Establish `key : ∀ (k : ℕ) (a : Per.Ainf l), (∀ n : ℕ, xi e ^ n ∣ a) → (l : Per.Ainf l) ^ k ∣ a`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro a _`. Simplify using the standard rewrite rules.

Consider the case `succ k ih`. Introduce `a ha`. Establish `h0 : a.coeff 0 = 0` using `eq_zero_of_dvd he _ fun n => by`. Use `map_dvd WittVector.constantCoeff (ha n)` as an intermediate fact. Rewrite `this` using `[map_pow, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply]`. Then use the resulting hypothesis.

Take `⟨d, rfl⟩` from `Ideal.mem_span_singleton.1 ((WittVector.mem_span_p_iff_coeff_zero_eq_zero a).2 h0)`. Rewrite using `[pow_succ']`. Conclude with `mul_dvd_mul_left _ (ih d fun n => xi_sat he n d (ha n))`. Use `IsHausdorff.haus (I := Ideal.span {(l : Per.Ainf l)}) inferInstance a fun k => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.

Conclude with `key k a ha`.
-/
theorem eq_zero_of_forall_xi_pow_dvd (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (he : IsEps e)
    (a : Per.Ainf l) (ha : ∀ n : ℕ, xi e ^ n ∣ a) : a = 0 := by
  have key : ∀ (k : ℕ) (a : Per.Ainf l), (∀ n : ℕ, xi e ^ n ∣ a) → (l : Per.Ainf l) ^ k ∣ a := by
    intro k
    induction k with
    | zero => intro a _; simp
    | succ k ih =>
      intro a ha
      have h0 : a.coeff 0 = 0 := eq_zero_of_dvd he _ fun n => by
        have := map_dvd WittVector.constantCoeff (ha n)
        rwa [map_pow, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply] at this
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.1
        ((WittVector.mem_span_p_iff_coeff_zero_eq_zero a).2 h0)
      rw [pow_succ']
      exact mul_dvd_mul_left _ (ih d fun n => xi_sat he n d (ha n))
  refine IsHausdorff.haus (I := Ideal.span {(l : Per.Ainf l)}) inferInstance a fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact key k a ha
end GlobalTheory.MemLoc
