import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.GelfA
import Formalism.RealPlaceAnalysis.StatementB

noncomputable section

namespace GlobalTheory.Mem.GelfCheck

open MvPolynomial GlobalTheory.Mem.Gelf

open MvPolynomial in
/- English proof (translation)
Simplify using `[_root_.GlobalTheory.Mem.Gelf.rowE, LinearMap.sum_apply]`.
-/
theorem _root_.GlobalTheory.Mem.GelfCheck.rowE_apply (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r)
    (P : MvPolynomial (Fin r × Fin n) R) :
    _root_.GlobalTheory.Mem.Gelf.rowE R r n a b P = ∑ s : Fin n, X (a, s) * pderiv (b, s) P := by
  simp [_root_.GlobalTheory.Mem.Gelf.rowE, LinearMap.sum_apply]

open MvPolynomial in
/- English proof (translation)
Rewrite using `[_root_.GlobalTheory.Mem.GelfCheck.rowE_apply]`. Simplify using `only [pderiv_X, Pi.single_apply, Prod.ext_iff]`. Use `split_ifs with hbc`. Substitute `hbc` using the available equality. Simplify using `[Finset.sum_ite_eq']`.

Establish `hcb : ¬c = b` using `fun h => hbc h.symm`. Simplify using `[hcb]`.
-/
theorem _root_.GlobalTheory.Mem.GelfCheck.rowE_X (R : Type) [CommRing R] (r n : ℕ) (a b c : Fin r) (t : Fin n) :
    _root_.GlobalTheory.Mem.Gelf.rowE R r n a b (X (c, t)) = if b = c then X (a, t) else 0 := by
  rw [_root_.GlobalTheory.Mem.GelfCheck.rowE_apply]
  simp only [pderiv_X, Pi.single_apply, Prod.ext_iff]
  split_ifs with hbc
  · subst hbc
    simp [Finset.sum_ite_eq']
  · have hcb : ¬c = b := fun h => hbc h.symm
    simp [hcb]

open MvPolynomial in
/- English proof (translation)
Simplify using `only [_root_.GlobalTheory.Mem.GelfCheck.rowE_apply, Derivation.leibniz, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.Mem.GelfCheck.rowE_mul (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r)
    (P Q : MvPolynomial (Fin r × Fin n) R) :
    _root_.GlobalTheory.Mem.Gelf.rowE R r n a b (P * Q) =
      _root_.GlobalTheory.Mem.Gelf.rowE R r n a b P * Q + P * _root_.GlobalTheory.Mem.Gelf.rowE R r n a b Q := by
  simp only [_root_.GlobalTheory.Mem.GelfCheck.rowE_apply, Derivation.leibniz, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

open MvPolynomial in
/- English proof (translation)
Simplify using `[_root_.GlobalTheory.Mem.GelfCheck.rowE_apply]`.
-/
theorem _root_.GlobalTheory.Mem.GelfCheck.rowE_C (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (x : R) :
    _root_.GlobalTheory.Mem.Gelf.rowE R r n a b (C x) = 0 := by
  simp [_root_.GlobalTheory.Mem.GelfCheck.rowE_apply]

open MvPolynomial in
/- English proof (translation)
Introduce `a b c d`. Use `set E := _root_.GlobalTheory.Mem.Gelf.rowE R r n with hE`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `P`. Proceed by induction on `P using MvPolynomial.induction_on with`.

Consider the case `C x`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, hE, _root_.GlobalTheory.Mem.GelfCheck.rowE_C, map_zero, sub_zero]`. Apply the tactic sequence `split_ifs <;> simp [_root_.GlobalTheory.Mem.GelfCheck.rowE_C]`. Consider the case `add p q hp hq`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, map_add] at hp hq ⊢`.

Rewrite using `[hp, hq]`. Consider the case `mul_X p v hp`. Take `⟨e, t⟩` from `v`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at hp ⊢`. Simplify using `only [hE, _root_.GlobalTheory.Mem.GelfCheck.rowE_mul, map_add, _root_.GlobalTheory.Mem.GelfCheck.rowE_X, apply_ite, map_zero] at hp ⊢`.

Apply the tactic sequence `split_ifs at hp ⊢ <;> subst_vars <;>`. Apply the tactic sequence `simp_all [_root_.GlobalTheory.Mem.GelfCheck.rowE_mul, _root_.GlobalTheory.Mem.GelfCheck.rowE_X] <;>`. Take the linear combination `hp * X _`.
-/
theorem _root_.GlobalTheory.Mem.GelfCheck.glRel_rowE (R : Type) [CommRing R] (r n : ℕ) :
    _root_.GlobalTheory.Mem.Gelf.GlRel (_root_.GlobalTheory.Mem.Gelf.rowE R r n) := by
  intro a b c d
  set E := _root_.GlobalTheory.Mem.Gelf.rowE R r n with hE
  apply LinearMap.ext
  intro P
  induction P using MvPolynomial.induction_on with
  | C x =>
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hE, _root_.GlobalTheory.Mem.GelfCheck.rowE_C,
      map_zero, sub_zero]
    split_ifs <;> simp [_root_.GlobalTheory.Mem.GelfCheck.rowE_C]
  | add p q hp hq =>
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p v hp =>
    obtain ⟨e, t⟩ := v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at hp ⊢
    simp only [hE, _root_.GlobalTheory.Mem.GelfCheck.rowE_mul, map_add, _root_.GlobalTheory.Mem.GelfCheck.rowE_X,
      apply_ite, map_zero] at hp ⊢
    split_ifs at hp ⊢ <;> subst_vars <;>
      simp_all [_root_.GlobalTheory.Mem.GelfCheck.rowE_mul, _root_.GlobalTheory.Mem.GelfCheck.rowE_X] <;>
      linear_combination hp * X _

open MvPolynomial in
/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C x`. Simplify using `[_root_.Formalism.GradedWeylDivisibility.rowGen, Polynomial.coeff_C]`. Consider the case `add p q hp hq`. Simplify using `only [map_add, Polynomial.coeff_add, hp.1, hp.2, hq.1, hq.2, Finset.sum_add_distrib, mul_add, and_self]`.

Consider the case `mul_X p v hp`. Take `⟨hp1, hp0⟩` from `hp`. Establish `hX : _root_.Formalism.GradedWeylDivisibility.rowGen R a b (X v) = Polynomial.C (X v) + if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0`. Simplify using `[_root_.Formalism.GradedWeylDivisibility.rowGen]`. Rewrite using `[map_mul, hX]`.

Take `⟨i, t⟩` from `v`. Simplify using `only [Derivation.leibniz, pderiv_X, smul_eq_mul, mul_add, Finset.sum_add_distrib]`. Use `split_ifs with hib`. Substitute `hib` using the available equality. Establish `h1 : (1 : ℕ) = 0 + 1` using `rfl`.

Rewrite using `[← mul_assoc]`. Simplify using `only [Polynomial.coeff_add, Polynomial.coeff_mul_C]`. Rewrite using `[h1, Polynomial.coeff_mul_X, ← h1]`. Simplify using `only [Polynomial.coeff_mul_X_zero, zero_mul, add_zero, hp0, hp1]`. Use `⟨?_, trivial⟩` and prove the remaining obligations.

Simplify using `only [Pi.single_apply, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]`. Rewrite using `[add_comm]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.

Simplify using `[Pi.single_apply, Prod.ext_iff, hib, Polynomial.coeff_mul_C, hp0, hp1, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.
-/
private theorem gradedWeyl_gen_coeff_one_and_coeff_zero (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r)
    (P : MvPolynomial (Fin r × Fin n) R) :
    (_root_.Formalism.GradedWeylDivisibility.rowGen R a b P).coeff 1 = ∑ s : Fin n, X (a, s) * pderiv (b, s) P ∧
      (_root_.Formalism.GradedWeylDivisibility.rowGen R a b P).coeff 0 = P := by
  induction P using MvPolynomial.induction_on with
  | C x =>
    simp [_root_.Formalism.GradedWeylDivisibility.rowGen, Polynomial.coeff_C]
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add, hp.1, hp.2, hq.1, hq.2, Finset.sum_add_distrib,
      mul_add, and_self]
  | mul_X p v hp =>
    obtain ⟨hp1, hp0⟩ := hp
    have hX : _root_.Formalism.GradedWeylDivisibility.rowGen R a b (X v) = Polynomial.C (X v) +
        if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0 := by
      simp [_root_.Formalism.GradedWeylDivisibility.rowGen]
    rw [map_mul, hX]
    obtain ⟨i, t⟩ := v
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    split_ifs with hib
    · subst hib
      have h1 : (1 : ℕ) = 0 + 1 := rfl
      rw [← mul_assoc]
      simp only [Polynomial.coeff_add, Polynomial.coeff_mul_C]
      rw [h1, Polynomial.coeff_mul_X, ← h1]
      simp only [Polynomial.coeff_mul_X_zero, zero_mul, add_zero, hp0, hp1]
      refine ⟨?_, trivial⟩
      simp only [Pi.single_apply, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]
      rw [add_comm]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun _ _ => by ring
    · simp [Pi.single_apply, Prod.ext_iff, hib, Polynomial.coeff_mul_C, hp0, hp1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring

open MvPolynomial in
/- English proof (translation)
Take `⟨h1, h0⟩` from `gradedWeyl_gen_coeff_one_and_coeff_zero R r n a b P`. Rewrite using `[_root_.GlobalTheory.Mem.GelfCheck.rowE_apply]`. Conclude with `⟨by unfold _root_.Formalism.GradedWeylDivisibility.rowDiv; exact h1.symm, by unfold _root_.Formalism.GradedWeylDivisibility.rowDiv; exact h0⟩`.
-/
theorem _root_.GlobalTheory.Mem.GelfCheck.rowE_eq_rowDiv (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r)
    (P : MvPolynomial (Fin r × Fin n) R) :
    _root_.GlobalTheory.Mem.Gelf.rowE R r n a b P = _root_.Formalism.GradedWeylDivisibility.rowDiv R a b 1 P ∧ _root_.Formalism.GradedWeylDivisibility.rowDiv R a b 0 P = P := by
  obtain ⟨h1, h0⟩ := gradedWeyl_gen_coeff_one_and_coeff_zero R r n a b P
  rw [_root_.GlobalTheory.Mem.GelfCheck.rowE_apply]
  exact ⟨by unfold _root_.Formalism.GradedWeylDivisibility.rowDiv; exact h1.symm, by unfold _root_.Formalism.GradedWeylDivisibility.rowDiv; exact h0⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem glRel_iff {A : Type} [Ring A] {N : ℕ} (E : Matrix (Fin N) (Fin N) A) :
    GlRel E ↔ Formalism.REAL.GlRel (fun a b => E a b) := Iff.rfl

open MvPolynomial in
/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [_root_.GlobalTheory.Mem.Gelf.gelfA, _root_.Formalism.REAL.Amat, _root_.Formalism.REAL.lsh, Matrix.of_apply]`. Use `split_ifs with hab`. Substitute `hab` using the available equality. Establish `ha` using `a.isLt`.

Establish `h1 : 1 ≤ N` using `by omega`. Establish `h2 : a.val ≤ N - 1` using `by omega`. Rewrite using `[Nat.cast_sub h2, Nat.cast_sub h1, Nat.cast_one]`. Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.Mem.GelfCheck.gelfA_eq_Amat {N : ℕ} (μ : Fin N → ℂ) :
    _root_.GlobalTheory.Mem.Gelf.gelfA μ = _root_.Formalism.REAL.Amat (_root_.Formalism.REAL.lsh μ) := by
  ext a b
  simp only [_root_.GlobalTheory.Mem.Gelf.gelfA, _root_.Formalism.REAL.Amat, _root_.Formalism.REAL.lsh, Matrix.of_apply]
  split_ifs with hab
  · subst hab
    have ha := a.isLt
    have h1 : 1 ≤ N := by omega
    have h2 : a.val ≤ N - 1 := by omega
    rw [Nat.cast_sub h2, Nat.cast_sub h1, Nat.cast_one]
  · rfl
  · rfl

section
variable {A : Type} [Ring A] {N : ℕ} {E : Matrix (Fin N) (Fin N) A}

open MvPolynomial in
variable {A : Type} [Ring A] {N : ℕ} {E : Matrix (Fin N) (Fin N) A} in
/- English proof (translation)
Proceed by induction on `k generalizing a b with`. Consider the case `zero`. Simplify using `only [pow_zero, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> subst_vars <;> simp_all`. Consider the case `succ k ih`.

Establish `key : ∀ m, E c d * ((E ^ k) a m * E m b) - (E ^ k) a m * E m b * E c d = ((if d = a then (E ^ k) c m * E m b else 0) - (if m = c then (E ^ k) a d * E m b else 0)) + ((if d = m then (E ^ k) a m * E c b else 0) - (if b = c then (E ^ k) a m * E m d else 0))`. Introduce `m`. Establish `h1` using `ih a m`. Establish `h2` using `h c d m b`. Rewrite using `[show E c d * ((E ^ k) a m * E m b) - (E ^ k) a m * E m b * E c d = (E c d * (E ^ k) a m - (E ^ k) a m * E c d) * E m b + (E ^ k) a m * (E c d * E m b - E m b * E c d) by noncomm_ring, h1, h2]`.

Simplify using `only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero]`. Simplify using `only [pow_succ, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]`. Rewrite using `[Finset.sum_congr rfl fun m _ => key m]`. Simplify using `only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Apply the tactic sequence `split_ifs <;> simp <;> abel`.
-/
theorem _root_.GlobalTheory.Mem.GelfCheck.pow_cov (h : _root_.GlobalTheory.Mem.Gelf.GlRel E) (k : ℕ)
    (a b c d : Fin N) :
    E c d * (E ^ k) a b - (E ^ k) a b * E c d =
      (if d = a then (E ^ k) c b else 0) - (if b = c then (E ^ k) a d else 0) := by
  induction k generalizing a b with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> subst_vars <;> simp_all
  | succ k ih =>
    have key : ∀ m, E c d * ((E ^ k) a m * E m b) - (E ^ k) a m * E m b * E c d =
        ((if d = a then (E ^ k) c m * E m b else 0) - (if m = c then (E ^ k) a d * E m b else 0)) +
        ((if d = m then (E ^ k) a m * E c b else 0) - (if b = c then (E ^ k) a m * E m d else 0)) := by
      intro m
      have h1 := ih a m
      have h2 := h c d m b
      rw [show E c d * ((E ^ k) a m * E m b) - (E ^ k) a m * E m b * E c d =
        (E c d * (E ^ k) a m - (E ^ k) a m * E c d) * E m b +
          (E ^ k) a m * (E c d * E m b - E m b * E c d) by noncomm_ring, h1, h2]
      simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero]
    simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl fun m _ => key m]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    split_ifs <;> simp <;> abel

end

section
variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] {N : ℕ}
  {E : Matrix (Fin N) (Fin N) (Module.End R V)} {μ : Fin N → R} {v : V}

/- English proof (translation)
Proceed by induction on `k generalizing a b with`. Consider the case `zero => simp [Matrix.one_apply, hab.ne]`. Consider the case `succ k ih`. Rewrite using `[pow_succ', Matrix.mul_apply, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations.

Break down `lt_or_ge c b with hc | hc` into its components or cases. Simplify using `[ih c b hc]`. Use `congrArg (fun f : Module.End R V => f v) (pow_cov h k c b a c)` as an intermediate fact. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, hv a c (hab.trans_le hc), map_zero, sub_zero, if_true, if_neg hab.ne', LinearMap.zero_apply, ih a b hab] at this`. Simplify using `using this`.
-/
theorem upper_kill (h : GlRel E) (hv : ∀ a b, a < b → E a b v = 0) (k : ℕ) (a b : Fin N) (hab : a < b) :
    (E ^ k) a b v = 0 := by
  induction k generalizing a b with
  | zero => simp [Matrix.one_apply, hab.ne]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c b with hc | hc
    · simp [ih c b hc]
    · have := congrArg (fun f : Module.End R V => f v) (pow_cov h k c b a c)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, hv a c (hab.trans_le hc), map_zero, sub_zero,
        if_true, if_neg hab.ne', LinearMap.zero_apply, ih a b hab] at this
      simpa using this

/- English proof (translation)
Proceed by induction on `k generalizing a with`. Consider the case `zero => simp [Matrix.one_apply]`. Consider the case `succ k ih => set e : Fin N → R := fun c => ∑ b, (gelfA μ ^ k) c b with he`. Establish `ih' : ∀ c, (E ^ k) c c v = e c • v` using `ih`. Establish `hr : (∑ b, (gelfA μ ^ (k+1)) a b) = ∑ c, gelfA μ a c * e c`.

Simplify using `only [pow_succ', Matrix.mul_apply, he, Finset.mul_sum]`. Conclude with `Finset.sum_comm`. Establish `hl : (E ^ (k+1)) a a v = (∑ c, (if a = c then μ a * e a else if a < c then e a - e c else 0)) • v`. Rewrite using `[pow_succ', Matrix.mul_apply, LinearMap.sum_apply, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Break down `lt_trichotomy a c with hc | hc | hc` into its components or cases. Use `congrArg (fun f : Module.End R V => f v) (pow_cov h k c a a c)` as an intermediate fact. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, hv a c hc, map_zero, sub_zero, if_true, ih'] at this`. Simplify using `[hc.ne, hc, this, sub_smul]`. Substitute `hc` using the available equality.

Simplify using `[ih', hw, smul_smul, mul_comm]`. Simplify using `[upper_kill h hv k c a hc, hc.ne', not_lt.mpr hc.le]`. Rewrite using `[hl, hr]`. Use `congr 1`. Establish `hcard : (∑ c : Fin N, if a < c then e a else 0) = ((N - 1 - a.val : ℕ) : R) * e a`.

Rewrite using `[← Finset.sum_filter, Finset.sum_const, Finset.filter_lt_eq_Ioi, Fin.card_Ioi, nsmul_eq_mul]`. Establish `h1 : ∀ c, (if a = c then μ a * e a else if a < c then e a - e c else 0) = (gelfA μ a c * e c - if a = c then ((N - 1 - a.val : ℕ) : R) * e a else 0) + (if a < c then e a else 0)`. Introduce `c`. Break down `lt_trichotomy a c with hc | hc | hc` into its components or cases. Simplify using `[gelfA, hc, hc.ne]`.

Expand and normalize the polynomial expressions, which then agree. Substitute `hc` using the available equality. Simplify using `[gelfA]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[gelfA, hc.ne', not_lt.mpr hc.le]`.

Simplify using `only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, hcard, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem diag_pow (h : GlRel E) (hw : ∀ a, E a a v = μ a • v) (hv : ∀ a b, a < b → E a b v = 0) (k : ℕ)
    (a : Fin N) : (E ^ k) a a v = (∑ b, (gelfA μ ^ k) a b) • v := by
  induction k generalizing a with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    set e : Fin N → R := fun c => ∑ b, (gelfA μ ^ k) c b with he
    have ih' : ∀ c, (E ^ k) c c v = e c • v := ih
    have hr : (∑ b, (gelfA μ ^ (k+1)) a b) = ∑ c, gelfA μ a c * e c := by
      simp only [pow_succ', Matrix.mul_apply, he, Finset.mul_sum]
      exact Finset.sum_comm
    have hl : (E ^ (k+1)) a a v =
        (∑ c, (if a = c then μ a * e a else if a < c then e a - e c else 0)) • v := by
      rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply, Finset.sum_smul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rcases lt_trichotomy a c with hc | hc | hc
      · have := congrArg (fun f : Module.End R V => f v) (pow_cov h k c a a c)
        simp only [LinearMap.sub_apply, Module.End.mul_apply, hv a c hc, map_zero, sub_zero,
          if_true, ih'] at this
        simp [hc.ne, hc, this, sub_smul]
      · subst hc
        simp [ih', hw, smul_smul, mul_comm]
      · simp [upper_kill h hv k c a hc, hc.ne', not_lt.mpr hc.le]
    rw [hl, hr]
    congr 1
    have hcard : (∑ c : Fin N, if a < c then e a else 0) = ((N - 1 - a.val : ℕ) : R) * e a := by
      rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_lt_eq_Ioi, Fin.card_Ioi, nsmul_eq_mul]
    have h1 : ∀ c, (if a = c then μ a * e a else if a < c then e a - e c else 0) =
        (gelfA μ a c * e c - if a = c then ((N - 1 - a.val : ℕ) : R) * e a else 0) +
          (if a < c then e a else 0) := by
      intro c
      rcases lt_trichotomy a c with hc | hc | hc
      · simp [gelfA, hc, hc.ne]; ring
      · subst hc; simp [gelfA]; ring
      · simp [gelfA, hc.ne', not_lt.mpr hc.le]
    simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, hcard, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    ring

open MvPolynomial in
variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] {N : ℕ}
  {E : Matrix (Fin N) (Fin N) (Module.End R V)} {μ : Fin N → R} {v : V} in
/- English proof (translation)
Establish `main : ∀ k : ℕ, (∀ a b : Fin N, a < b → (E ^ k) a b v = 0) ∧ ∀ a, (E ^ k) a a v = (∑ b, (_root_.GlobalTheory.Mem.Gelf.gelfA μ ^ k) a b) • v`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Use `⟨fun a b hab => ?_, fun a => ?_⟩` and prove the remaining obligations.

Simplify using `[Matrix.one_apply, hab.ne]`. Simplify using `[Matrix.one_apply]`. Consider the case `succ k ih`. Take `⟨ih1, ih2⟩` from `ih`. Establish `expand : ∀ a b, (E ^ (k + 1)) a b v = ∑ m, (E ^ k) a m (E m b v)`.

Introduce `a b`. Simplify using `[pow_succ, Matrix.mul_apply, LinearMap.sum_apply, Module.End.mul_apply]`. Establish `term : ∀ a b m, a ≤ b → (E ^ k) a m (E m b v) = if m < b then 0 else if m = b then μ b • (E ^ k) a b v else (E ^ k) a b v - (if b = a then (E ^ k) m m v else 0)`. Introduce `a b m hab`. Break down `lt_trichotomy m b with hmb | hmb | hmb` into its components or cases.

Simplify using `[hmb, hv m b hmb]`. Substitute `hmb` using the available equality. Simplify using `[hw]`. Establish `hc` using `congrArg (fun f : Module.End R V => f v) (_root_.GlobalTheory.Mem.GelfCheck.pow_cov h k a m m b)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, if_pos rfl] at hc`.

Rewrite `hc` using `[ih1 a m (lt_of_le_of_lt hab hmb), map_zero, zero_sub]`. Rewrite using `[if_neg (not_lt.mpr hmb.le), if_neg hmb.ne', ← neg_neg ((E ^ k) a m (E m b v)), hc]`. Apply the tactic sequence `split_ifs <;> simp`. Use `⟨fun a b hab => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[expand, Finset.sum_congr rfl fun m _ => term a b m hab.le, ih1 a b hab]`.

Simplify using `[hab.ne']`. Rewrite using `[expand, Finset.sum_congr rfl fun m _ => term a a m le_rfl]`. Take `⟨s, hs_def⟩ : ∃ s : Fin N → R, s = fun m => ∑ b, (_root_.GlobalTheory.Mem.Gelf.gelfA μ ^ k) m b` from `⟨_, rfl⟩`. Establish `ih2' : ∀ m, (E ^ k) m m v = s m • v`. Introduce `m`.

Rewrite using `[ih2, hs_def]`. Establish `hs : ∑ b, (_root_.GlobalTheory.Mem.Gelf.gelfA μ ^ (k + 1)) a b = ∑ m, _root_.GlobalTheory.Mem.Gelf.gelfA μ a m * s m`. Simplify using `only [hs_def, pow_succ', Matrix.mul_apply, Finset.mul_sum]`. Conclude with `Finset.sum_comm`. Establish `hterm : ∀ m, (if m < a then 0 else if m = a then μ a • (E ^ k) a a v else (E ^ k) a a v - (if a = a then (E ^ k) m m v else 0)) = (_root_.GlobalTheory.Mem.Gelf.gelfA μ a m * s m) • v + ((if a < m then s a else 0) - (if m = a then ((N - 1 - a.val : ℕ) : R) * s a else 0)) • v`.

Introduce `m`. Rewrite using `[ih2', ih2', if_pos rfl]`. Break down `lt_trichotomy m a with hma | hma | hma` into its components or cases. Simplify using `[_root_.GlobalTheory.Mem.Gelf.gelfA, hma, hma.ne', not_lt.mpr hma.le, hma.ne]`. Substitute `hma` using the available equality.

Establish `hdiag : _root_.GlobalTheory.Mem.Gelf.gelfA μ m m = μ m + ((N - 1 - m.val : ℕ) : R)`. Simplify using `[_root_.GlobalTheory.Mem.Gelf.gelfA]`. Rewrite using `[hdiag, if_neg (lt_irrefl m), if_pos rfl, if_neg (lt_irrefl m), if_pos rfl]`. Use `module`. Establish `hup : _root_.GlobalTheory.Mem.Gelf.gelfA μ a m = -1`.

Simplify using `[_root_.GlobalTheory.Mem.Gelf.gelfA, hma.ne, hma]`. Rewrite using `[hup, if_neg (not_lt.mpr hma.le), if_neg hma.ne', if_pos hma, if_neg hma.ne']`. Use `module`. Establish `hf : (Finset.univ.filter fun m : Fin N => a < m) = Finset.Ioi a`. Use extensionality with `m`.

Simplify using the standard rewrite rules. Establish `hc : ∑ m : Fin N, (if a < m then s a else 0) = ((N - 1 - a.val : ℕ) : R) * s a`. Rewrite using `[← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hf, Fin.card_Ioi]`. Rewrite using `[Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul, Finset.sum_sub_distrib, hc, Finset.sum_ite_eq', if_pos (Finset.mem_univ a), sub_self, zero_smul, add_zero, hs]`. Simplify using `only [Matrix.trace, Matrix.diag, LinearMap.sum_apply, (main k).2, _root_.GlobalTheory.Mem.Gelf.gelfC, Finset.sum_smul]`.
-/
theorem _root_.GlobalTheory.Mem.GelfCheck.trace_pow_apply (h : _root_.GlobalTheory.Mem.Gelf.GlRel E)
    (hw : ∀ a, E a a v = μ a • v) (hv : ∀ a b, a < b → E a b v = 0)
    (k : ℕ) : (E ^ k).trace v = _root_.GlobalTheory.Mem.Gelf.gelfC μ k • v := by
  have main : ∀ k : ℕ, (∀ a b : Fin N, a < b → (E ^ k) a b v = 0) ∧
      ∀ a, (E ^ k) a a v = (∑ b, (_root_.GlobalTheory.Mem.Gelf.gelfA μ ^ k) a b) • v := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun a b hab => ?_, fun a => ?_⟩
      · simp [Matrix.one_apply, hab.ne]
      · simp [Matrix.one_apply]
    | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have expand : ∀ a b, (E ^ (k + 1)) a b v = ∑ m, (E ^ k) a m (E m b v) := by
        intro a b
        simp [pow_succ, Matrix.mul_apply, LinearMap.sum_apply, Module.End.mul_apply]
      have term : ∀ a b m, a ≤ b → (E ^ k) a m (E m b v) =
          if m < b then 0 else if m = b then μ b • (E ^ k) a b v
            else (E ^ k) a b v - (if b = a then (E ^ k) m m v else 0) := by
        intro a b m hab
        rcases lt_trichotomy m b with hmb | hmb | hmb
        · simp [hmb, hv m b hmb]
        · subst hmb
          simp [hw]
        · have hc := congrArg (fun f : Module.End R V => f v)
            (_root_.GlobalTheory.Mem.GelfCheck.pow_cov h k a m m b)
          simp only [LinearMap.sub_apply, Module.End.mul_apply, if_pos rfl] at hc
          rw [ih1 a m (lt_of_le_of_lt hab hmb), map_zero, zero_sub] at hc
          rw [if_neg (not_lt.mpr hmb.le), if_neg hmb.ne', ← neg_neg ((E ^ k) a m (E m b v)), hc]
          split_ifs <;> simp
      refine ⟨fun a b hab => ?_, fun a => ?_⟩
      · rw [expand, Finset.sum_congr rfl fun m _ => term a b m hab.le, ih1 a b hab]
        simp [hab.ne']
      · rw [expand, Finset.sum_congr rfl fun m _ => term a a m le_rfl]
        obtain ⟨s, hs_def⟩ : ∃ s : Fin N → R,
            s = fun m => ∑ b, (_root_.GlobalTheory.Mem.Gelf.gelfA μ ^ k) m b := ⟨_, rfl⟩
        have ih2' : ∀ m, (E ^ k) m m v = s m • v := by
          intro m
          rw [ih2, hs_def]
        have hs : ∑ b, (_root_.GlobalTheory.Mem.Gelf.gelfA μ ^ (k + 1)) a b =
            ∑ m, _root_.GlobalTheory.Mem.Gelf.gelfA μ a m * s m := by
          simp only [hs_def, pow_succ', Matrix.mul_apply, Finset.mul_sum]
          exact Finset.sum_comm
        have hterm : ∀ m, (if m < a then 0 else if m = a then μ a • (E ^ k) a a v
            else (E ^ k) a a v - (if a = a then (E ^ k) m m v else 0)) =
            (_root_.GlobalTheory.Mem.Gelf.gelfA μ a m * s m) • v +
              ((if a < m then s a else 0) -
                (if m = a then ((N - 1 - a.val : ℕ) : R) * s a else 0)) • v := by
          intro m
          rw [ih2', ih2', if_pos rfl]
          rcases lt_trichotomy m a with hma | hma | hma
          · simp [_root_.GlobalTheory.Mem.Gelf.gelfA, hma, hma.ne', not_lt.mpr hma.le, hma.ne]
          · subst hma
            have hdiag : _root_.GlobalTheory.Mem.Gelf.gelfA μ m m = μ m + ((N - 1 - m.val : ℕ) : R) := by
              simp [_root_.GlobalTheory.Mem.Gelf.gelfA]
            rw [hdiag, if_neg (lt_irrefl m), if_pos rfl, if_neg (lt_irrefl m), if_pos rfl]
            module
          · have hup : _root_.GlobalTheory.Mem.Gelf.gelfA μ a m = -1 := by
              simp [_root_.GlobalTheory.Mem.Gelf.gelfA, hma.ne, hma]
            rw [hup, if_neg (not_lt.mpr hma.le), if_neg hma.ne', if_pos hma, if_neg hma.ne']
            module
        have hf : (Finset.univ.filter fun m : Fin N => a < m) = Finset.Ioi a := by
          ext m
          simp
        have hc : ∑ m : Fin N, (if a < m then s a else 0) = ((N - 1 - a.val : ℕ) : R) * s a := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hf, Fin.card_Ioi]
        rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_add_distrib, ← Finset.sum_smul,
          ← Finset.sum_smul, Finset.sum_sub_distrib, hc, Finset.sum_ite_eq',
          if_pos (Finset.mem_univ a), sub_self, zero_smul, add_zero, hs]
  simp only [Matrix.trace, Matrix.diag, LinearMap.sum_apply, (main k).2,
    _root_.GlobalTheory.Mem.Gelf.gelfC, Finset.sum_smul]

end

/- English proof (translation)
Simplify using `[gelfC, gelfA, pow_two, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
example : gelfC (![1, 0] : Fin 2 → ℤ) 2 = 2 := by
  simp [gelfC, gelfA, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
/- English proof (translation)
Simplify using `[gelfC, gelfA, pow_two, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
example : gelfC (![0, 1] : Fin 2 → ℤ) 2 = 0 := by
  simp [gelfC, gelfA, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Use `trace_pow_apply (glRel_rowE R (r+1) n) (fun a => ?_) (fun a b hab => ?_) k` and prove the remaining obligations. Apply the tactic sequence `rw [rowE_X]; split_ifs with h <;> simp [h]`. Rewrite using `[rowE_X, if_neg (ne_of_gt (lt_of_le_of_lt (Fin.zero_le a) hab))]`.
-/
theorem trace_pow_X (R : Type) [CommRing R] (r n : ℕ) (t : Fin n) (k : ℕ) :
    (rowE R (r+1) n ^ k).trace (X (0, t)) = gelfC (Pi.single (0 : Fin (r+1)) (1 : R)) k • X (0, t) := by
  refine trace_pow_apply (glRel_rowE R (r+1) n) (fun a => ?_) (fun a b hab => ?_) k
  · rw [rowE_X]; split_ifs with h <;> simp [h]
  · rw [rowE_X, if_neg (ne_of_gt (lt_of_le_of_lt (Fin.zero_le a) hab))]

end GlobalTheory.Mem.GelfCheck
