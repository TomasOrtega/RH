import Mathlib

noncomputable section
open ValuativeRel Module

namespace PI.LocDualGen.EpS

variable {K : Type} [Field K] {L : Type} [CommRing L] [Algebra K L]

/- English proof (translation)
Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Establish `hf : IsIdempotentElem (1 - e)` using `he.one_sub`. Establish `hef : e * (1 - e) = 0` using `by rw [mul_sub, mul_one, he.eq, sub_self]`. Establish `h0' : (1 - e) ≠ 0` using `sub_ne_zero.mpr (Ne.symm h1)`.

Establish `hs : s • e = 0`. Use `congrArg (· * e) hst` as an intermediate fact. Simplify using `only [add_mul, smul_mul_assoc, he.eq, zero_mul] at this`. Rewrite `this` using `[mul_comm (1 - e) e, hef, smul_zero, add_zero]`. Then use the resulting hypothesis. Establish `ht : t • (1 - e) = 0`.

Use `congrArg (· * (1 - e)) hst` as an intermediate fact. Simplify using `only [add_mul, smul_mul_assoc, hf.eq, zero_mul, hef, smul_zero, zero_add] at this`. Conclude with `this`. Conclude with `⟨(smul_eq_zero.mp hs).resolve_right h0, (smul_eq_zero.mp ht).resolve_right h0'⟩`.
-/
theorem li (e : L) (he : IsIdempotentElem e) (h0 : e ≠ 0) (h1 : e ≠ 1) :
    LinearIndependent K ![e, 1 - e] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hf : IsIdempotentElem (1 - e) := he.one_sub
  have hef : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have h0' : (1 - e) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hs : s • e = 0 := by
    have := congrArg (· * e) hst
    simp only [add_mul, smul_mul_assoc, he.eq, zero_mul] at this
    rwa [mul_comm (1 - e) e, hef, smul_zero, add_zero] at this
  have ht : t • (1 - e) = 0 := by
    have := congrArg (· * (1 - e)) hst
    simp only [add_mul, smul_mul_assoc, hf.eq, zero_mul, hef, smul_zero, zero_add] at this
    exact this
  exact ⟨(smul_eq_zero.mp hs).resolve_right h0, (smul_eq_zero.mp ht).resolve_right h0'⟩

section V
variable [ValuativeRel K]

/- English proof (translation)
Use `⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Polynomial.monic_X_pow_sub (by simp)`. Simplify using `[pow_two, he.eq]`.
-/
theorem isIntegral_idem (e : L) (he : IsIdempotentElem e) : IsIntegral 𝒪[K] e := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub (by simp)
  · simp [pow_two, he.eq]

/- English proof (translation)
Take `⟨y, hy⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := 𝒪[K]) (K := K)).mp h`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem mem_of_isIntegral {c : K} (h : IsIntegral 𝒪[K] c) : c ∈ 𝒪[K] := by
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝒪[K]) (K := K)).mp h
  rw [← hy]; exact y.2
end V

variable (hr : finrank K L = 2) (e : L) (he : IsIdempotentElem e) (h0 : e ≠ 0) (h1 : e ≠ 1)

def bas : Basis (Fin 2) K L :=
  basisOfLinearIndependentOfCardEqFinrank (li e he h0 h1) (by simp [hr])

/- English proof (translation)
Simplify using `[bas]`.
-/
theorem bas0 : bas hr e he h0 h1 0 = e := by simp [bas]
/- English proof (translation)
Simplify using `[bas]`.
-/
theorem bas1 : bas hr e he h0 h1 1 = 1 - e := by simp [bas]

/- English proof (translation)
Use `conv_lhs => rw [← (bas hr e he h0 h1).sum_repr z]`. Rewrite using `[Fin.sum_univ_two, bas0, bas1]`.
-/
theorem decomp (z : L) :
    z = (bas hr e he h0 h1).repr z 0 • e + (bas hr e he h0 h1).repr z 1 • (1 - e) := by
  conv_lhs => rw [← (bas hr e he h0 h1).sum_repr z]
  rw [Fin.sum_univ_two, bas0, bas1]

/- English proof (translation)
Establish `: s • e + t • (1 - e) = s • bas hr e he h0 h1 0 + t • bas hr e he h0 h1 1`. Rewrite using `[bas0, bas1]`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem repr_pair (s t : K) :
    (bas hr e he h0 h1).repr (s • e + t • (1 - e)) 0 = s ∧
    (bas hr e he h0 h1).repr (s • e + t • (1 - e)) 1 = t := by
  have : s • e + t • (1 - e) = s • bas hr e he h0 h1 0 + t • bas hr e he h0 h1 1 := by
    rw [bas0, bas1]
  rw [this]
  simp

/- English proof (translation)
Establish `hf : IsIdempotentElem (1 - e)` using `he.one_sub`. Establish `hef : e * (1 - e) = 0` using `by rw [mul_sub, mul_one, he.eq, sub_self]`. Establish `hfe : (1 - e) * e = 0` using `by rw [mul_comm, hef]`. Use `conv_lhs => rw [decomp hr e he h0 h1 z, decomp hr e he h0 h1 w]`. Simplify using `only [add_mul, mul_add, smul_mul_smul_comm, he.eq, hf.eq, hef, hfe, smul_zero, add_zero, zero_add]`.
-/
theorem mul_decomp (z w : L) :
    z * w = ((bas hr e he h0 h1).repr z 0 * (bas hr e he h0 h1).repr w 0) • e +
      ((bas hr e he h0 h1).repr z 1 * (bas hr e he h0 h1).repr w 1) • (1 - e) := by
  have hf : IsIdempotentElem (1 - e) := he.one_sub
  have hef : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have hfe : (1 - e) * e = 0 := by rw [mul_comm, hef]
  conv_lhs => rw [decomp hr e he h0 h1 z, decomp hr e he h0 h1 w]
  simp only [add_mul, mul_add, smul_mul_smul_comm, he.eq, hf.eq, hef, hfe, smul_zero, add_zero,
    zero_add]

def pr (i : Fin 2) : L →ₐ[K] K :=
  AlgHom.ofLinearMap ((bas hr e he h0 h1).coord i)
    (by
      have : (1 : L) = (1 : K) • e + (1 : K) • (1 - e) := by simp
      rw [Basis.coord_apply, this]
      fin_cases i
      · exact (repr_pair hr e he h0 h1 1 1).1
      · exact (repr_pair hr e he h0 h1 1 1).2)
    (by
      intro z w
      simp only [Basis.coord_apply]
      rw [mul_decomp hr e he h0 h1 z w]
      fin_cases i
      · exact (repr_pair hr e he h0 h1 _ _).1
      · exact (repr_pair hr e he h0 h1 _ _).2)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pr_apply (i : Fin 2) (z : L) : pr hr e he h0 h1 i z = (bas hr e he h0 h1).repr z i := rfl

/- English proof (translation)
Establish `: e = (1 : K) • e + (0 : K) • (1 - e)` using `by simp`. Establish `key` using `repr_pair hr e he h0 h1 1 0`. Rewrite `key` using `[← this]`. Rewrite using `[pr_apply, pr_apply]`. Conclude with `key`.
-/
theorem pr_e : pr hr e he h0 h1 0 e = 1 ∧ pr hr e he h0 h1 1 e = 0 := by
  have : e = (1 : K) • e + (0 : K) • (1 - e) := by simp
  have key := repr_pair hr e he h0 h1 1 0
  rw [← this] at key
  rw [pr_apply, pr_apply]; exact key

/- English proof (translation)
Rewrite using `[map_sub, map_sub, map_one, map_one, (pr_e hr e he h0 h1).1, (pr_e hr e he h0 h1).2]`. Simplify using the standard rewrite rules.
-/
theorem pr_f : pr hr e he h0 h1 0 (1 - e) = 0 ∧ pr hr e he h0 h1 1 (1 - e) = 1 := by
  rw [map_sub, map_sub, map_one, map_one, (pr_e hr e he h0 h1).1, (pr_e hr e he h0 h1).2]
  simp

/- English proof (translation)
Rewrite using `[Algebra.trace_eq_matrix_trace (bas hr e he h0 h1) z, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, bas0, bas1]`. Establish `a` using `congrArg (fun w => (bas hr e he h0 h1).repr w 0) (mul_decomp hr e he h0 h1 z e)`. Establish `b` using `congrArg (fun w => (bas hr e he h0 h1).repr w 1) (mul_decomp hr e he h0 h1 z (1 - e))`. Rewrite using `[a, b, (repr_pair hr e he h0 h1 _ _).1, (repr_pair hr e he h0 h1 _ _).2]`. Establish `pe` using `pr_e hr e he h0 h1`.

Establish `pf` using `pr_f hr e he h0 h1`. Simplify using `only [pr_apply] at pe pf`. Rewrite using `[pe.1, pf.2, mul_one, mul_one, pr_apply, pr_apply]`.
-/
theorem trace_eq (z : L) : Algebra.trace K L z = pr hr e he h0 h1 0 z + pr hr e he h0 h1 1 z := by
  rw [Algebra.trace_eq_matrix_trace (bas hr e he h0 h1) z, Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, bas0, bas1]
  have a := congrArg (fun w => (bas hr e he h0 h1).repr w 0) (mul_decomp hr e he h0 h1 z e)
  have b := congrArg (fun w => (bas hr e he h0 h1).repr w 1) (mul_decomp hr e he h0 h1 z (1 - e))
  rw [a, b, (repr_pair hr e he h0 h1 _ _).1, (repr_pair hr e he h0 h1 _ _).2]
  have pe := pr_e hr e he h0 h1
  have pf := pr_f hr e he h0 h1
  simp only [pr_apply] at pe pf
  rw [pe.1, pf.2, mul_one, mul_one, pr_apply, pr_apply]

variable [ValuativeRel K]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨mem_of_isIntegral (h.map ((pr hr e he h0 h1 0).restrictScalars 𝒪[K])), mem_of_isIntegral (h.map ((pr hr e he h0 h1 1).restrictScalars 𝒪[K]))⟩`. Introduce and unpack `⟨ha, hb⟩`. Rewrite using `[decomp hr e he h0 h1 z, Algebra.smul_def, Algebra.smul_def]`.

Establish `hie` using `isIntegral_idem (K := K) e he`. Establish `hif : IsIntegral 𝒪[K] (1 - e)` using `isIntegral_one.sub hie`. Establish `ia : IsIntegral 𝒪[K] (algebraMap K L ((bas hr e he h0 h1).repr z 0))` using `isIntegral_algebraMap (R := 𝒪[K]) (x := (⟨_, ha⟩ : 𝒪[K]))`. Establish `ib : IsIntegral 𝒪[K] (algebraMap K L ((bas hr e he h0 h1).repr z 1))` using `isIntegral_algebraMap (R := 𝒪[K]) (x := (⟨_, hb⟩ : 𝒪[K]))`. Conclude with `(ia.mul hie).add (ib.mul hif)`.
-/
theorem int_iff (z : L) :
    IsIntegral 𝒪[K] z ↔ pr hr e he h0 h1 0 z ∈ 𝒪[K] ∧ pr hr e he h0 h1 1 z ∈ 𝒪[K] := by
  constructor
  · intro h
    exact ⟨mem_of_isIntegral (h.map ((pr hr e he h0 h1 0).restrictScalars 𝒪[K])),
      mem_of_isIntegral (h.map ((pr hr e he h0 h1 1).restrictScalars 𝒪[K]))⟩
  · rintro ⟨ha, hb⟩
    rw [decomp hr e he h0 h1 z, Algebra.smul_def, Algebra.smul_def]
    have hie := isIntegral_idem (K := K) e he
    have hif : IsIntegral 𝒪[K] (1 - e) := isIntegral_one.sub hie
    have ia : IsIntegral 𝒪[K] (algebraMap K L ((bas hr e he h0 h1).repr z 0)) :=
      isIntegral_algebraMap (R := 𝒪[K]) (x := (⟨_, ha⟩ : 𝒪[K]))
    have ib : IsIntegral 𝒪[K] (algebraMap K L ((bas hr e he h0 h1).repr z 1)) :=
      isIntegral_algebraMap (R := 𝒪[K]) (x := (⟨_, hb⟩ : 𝒪[K]))
    exact (ia.mul hie).add (ib.mul hif)

include hr he h0 h1 in

/- English proof (translation)
Establish `pe` using `pr_e hr e he h0 h1`. Establish `pf` using `pr_f hr e he h0 h1`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `ha` using `h e (isIntegral_idem e he)`.

Establish `hb` using `h (1 - e) (isIntegral_one.sub (isIntegral_idem e he))`. Rewrite `ha` using `[trace_eq hr e he h0 h1, map_mul, map_mul, pe.1, pe.2]`. Rewrite `hb` using `[trace_eq hr e he h0 h1, map_mul, map_mul, pf.1, pf.2]`. Simplify using `only [mul_one, mul_zero, add_zero, zero_add] at ha hb`. Conclude with `(int_iff hr e he h0 h1 x).mpr ⟨ha, hb⟩`.

Introduce `hx y hy`. Use `(int_iff hr e he h0 h1 (x * y)).mp (hx.mul hy)` as an intermediate fact. Rewrite using `[trace_eq hr e he h0 h1]`. Conclude with `add_mem this.1 this.2`.
-/
theorem selfDual_split (x : L) :
    (∀ y : L, IsIntegral 𝒪[K] y → Algebra.trace K L (x * y) ∈ 𝒪[K]) ↔ IsIntegral 𝒪[K] x := by
  have pe := pr_e hr e he h0 h1
  have pf := pr_f hr e he h0 h1
  constructor
  · intro h
    have ha := h e (isIntegral_idem e he)
    have hb := h (1 - e) (isIntegral_one.sub (isIntegral_idem e he))
    rw [trace_eq hr e he h0 h1, map_mul, map_mul, pe.1, pe.2] at ha
    rw [trace_eq hr e he h0 h1, map_mul, map_mul, pf.1, pf.2] at hb
    simp only [mul_one, mul_zero, add_zero, zero_add] at ha hb
    exact (int_iff hr e he h0 h1 x).mpr ⟨ha, hb⟩
  · intro hx y hy
    have := (int_iff hr e he h0 h1 (x * y)).mp (hx.mul hy)
    rw [trace_eq hr e he h0 h1]
    exact add_mem this.1 this.2

end PI.LocDualGen.EpS
