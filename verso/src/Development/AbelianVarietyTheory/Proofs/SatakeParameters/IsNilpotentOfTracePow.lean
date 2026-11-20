import Mathlib

open Polynomial

namespace GlobalTheory.NilpotentOfTracePowers

/- English proof (translation)
Rewrite using `[Polynomial.aeval_eq_sum_range, Finset.mul_sum, map_sum]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, map_smul, ← pow_succ', h (i + 1) (by omega), smul_zero]`.
-/
theorem trace_mul_aeval {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (f : Module.End K V) (h : ∀ k : ℕ, 1 ≤ k → LinearMap.trace K V (f ^ k) = 0) (p : K[X]) :
    LinearMap.trace K V (f * aeval f p) = 0 := by
  rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mul_smul_comm, map_smul, ← pow_succ', h (i + 1) (by omega), smul_zero]

/- English proof (translation)
Establish `hp : f.charpoly ≠ 0` using `f.charpoly_monic.ne_zero`. Take `⟨q, hq, hnd⟩` from `exists_eq_pow_rootMultiplicity_mul_and_not_dvd f.charpoly hp 0`. Use `set m := rootMultiplicity 0 f.charpoly`. Establish `hc : q.coeff 0 ≠ 0`. Introduce `h0`.

Apply `hnd` to reduce the goal to its premises. Rewrite using `[map_zero, sub_zero]`. Conclude with `X_dvd_iff.mpr h0`. Establish `h0 : aeval f f.charpoly = 0` using `f.aeval_self_charpoly`. Establish `hpoly : (X : K[X]) ^ m = X ^ m * (X * (C (-(q.coeff 0)⁻¹) * q.divX)) + C (q.coeff 0)⁻¹ * f.charpoly`.

Establish `h1 : X * q.divX + C (q.coeff 0) = q` using `X_mul_divX_add q`. Establish `h2 : C (q.coeff 0)⁻¹ * C (q.coeff 0) = (1 : K[X])`. Rewrite using `[← map_mul, inv_mul_cancel₀ hc, map_one]`. Rewrite `hq` using `[map_zero, sub_zero]`. Rewrite using `[map_neg]`.

Take the linear combination `(-C (q.coeff 0)⁻¹) * hq + (C (q.coeff 0)⁻¹ * X ^ m) * h1 - X ^ m * h2`. Use `⟨m, C (-(q.coeff 0)⁻¹) * q.divX, ?_⟩` and prove the remaining obligations. Use `congrArg (aeval f) hpoly` as an intermediate fact. Rewrite `this` using `[map_add, map_mul (aeval f) _ f.charpoly, h0, mul_zero, add_zero, map_mul, map_pow, aeval_X]`. Conclude with `this`.
-/
theorem exists_pow_eq {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) :
    ∃ (m : ℕ) (g : K[X]), f ^ m = f ^ m * aeval f (X * g) := by
  have hp : f.charpoly ≠ 0 := f.charpoly_monic.ne_zero
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd f.charpoly hp 0
  set m := rootMultiplicity 0 f.charpoly
  have hc : q.coeff 0 ≠ 0 := by
    intro h0
    apply hnd
    rw [map_zero, sub_zero]
    exact X_dvd_iff.mpr h0
  have h0 : aeval f f.charpoly = 0 := f.aeval_self_charpoly
  have hpoly : (X : K[X]) ^ m = X ^ m * (X * (C (-(q.coeff 0)⁻¹) * q.divX))
      + C (q.coeff 0)⁻¹ * f.charpoly := by
    have h1 : X * q.divX + C (q.coeff 0) = q := X_mul_divX_add q
    have h2 : C (q.coeff 0)⁻¹ * C (q.coeff 0) = (1 : K[X]) := by
      rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    rw [map_zero, sub_zero] at hq
    rw [map_neg]
    linear_combination (-C (q.coeff 0)⁻¹) * hq + (C (q.coeff 0)⁻¹ * X ^ m) * h1 - X ^ m * h2
  refine ⟨m, C (-(q.coeff 0)⁻¹) * q.divX, ?_⟩
  have := congrArg (aeval f) hpoly
  rw [map_add, map_mul (aeval f) _ f.charpoly, h0, mul_zero, add_zero, map_mul, map_pow,
    aeval_X] at this
  exact this

/- English proof (translation)
Take `⟨m, g, hm⟩` from `exists_pow_eq f`. Establish `hiter : ∀ j : ℕ, f ^ m = f ^ m * aeval f ((X * g) ^ j)`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`.

Consider the case `succ j ih => rw [pow_succ', map_mul, ← mul_assoc, ← hm, ← ih]`. Use `set e : Module.End K V := aeval f ((X * g) ^ (m + 1)) with he`. Establish `he1 : e = aeval f (X * g ^ (m + 1)) * f ^ m`. Establish `: (X * g) ^ (m + 1) = (X * g ^ (m + 1)) * X ^ m` using `by ring`. Rewrite using `[he, this, map_mul (aeval f) _ (X ^ m), map_pow, aeval_X]`.

Establish `hid : IsIdempotentElem e`. Unfold `IsIdempotentElem`. Use `conv_lhs => enter [1]`. Rewrite using `[he1]`. Rewrite using `[mul_assoc, ← hiter (m + 1), ← he1]`.

Establish `htr : LinearMap.trace K V e = 0`. Establish `: (X * g) ^ (m + 1) = X * (g ^ (m + 1) * X ^ m)` using `by ring`. Rewrite using `[he, this, map_mul, aeval_X]`. Conclude with `trace_mul_aeval f h _`. Establish `hproj : LinearMap.IsProj (LinearMap.range e) e` using `{ map_mem := fun x => LinearMap.mem_range_self e x map_id := by`.

Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `LinearMap.congr_fun hid x }`. Establish `hrk : Module.finrank K (LinearMap.range e) = 0`. Use `hproj.trace` as an intermediate fact. Rewrite `this` using `[htr]`.

Conclude with `this.symm` after adjusting the coercions. Establish `he0 : e = 0` using `LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hrk)`. Conclude with `⟨m, by rw [hiter (m + 1), ← he, he0, mul_zero]⟩`.
-/
theorem isNilpotent_of_trace_pow {K : Type} [Field K] [CharZero K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (f : Module.End K V)
    (h : ∀ k : ℕ, 1 ≤ k → LinearMap.trace K V (f ^ k) = 0) : IsNilpotent f := by
  obtain ⟨m, g, hm⟩ := exists_pow_eq f
  have hiter : ∀ j : ℕ, f ^ m = f ^ m * aeval f ((X * g) ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', map_mul, ← mul_assoc, ← hm, ← ih]
  set e : Module.End K V := aeval f ((X * g) ^ (m + 1)) with he
  have he1 : e = aeval f (X * g ^ (m + 1)) * f ^ m := by
    have : (X * g) ^ (m + 1) = (X * g ^ (m + 1)) * X ^ m := by ring
    rw [he, this, map_mul (aeval f) _ (X ^ m), map_pow, aeval_X]
  have hid : IsIdempotentElem e := by
    unfold IsIdempotentElem
    conv_lhs => enter [1]; rw [he1]
    rw [mul_assoc, ← hiter (m + 1), ← he1]
  have htr : LinearMap.trace K V e = 0 := by
    have : (X * g) ^ (m + 1) = X * (g ^ (m + 1) * X ^ m) := by ring
    rw [he, this, map_mul, aeval_X]
    exact trace_mul_aeval f h _
  have hproj : LinearMap.IsProj (LinearMap.range e) e :=
    { map_mem := fun x => LinearMap.mem_range_self e x
      map_id := by
        rintro _ ⟨x, rfl⟩
        exact LinearMap.congr_fun hid x }
  have hrk : Module.finrank K (LinearMap.range e) = 0 := by
    have := hproj.trace
    rw [htr] at this
    exact_mod_cast this.symm
  have he0 : e = 0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hrk)
  exact ⟨m, by rw [hiter (m + 1), ← he, he0, mul_zero]⟩

end GlobalTheory.NilpotentOfTracePowers
