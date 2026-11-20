import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyHW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.LoweringPartRightActionInlInr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.EqZeroOfFockInnerSelfRe

noncomputable section

open MvPolynomial FockH1Action

namespace PI.FJMF

def BlockAntitone : Prop := ∀ (σ : Type) (m n : ℕ) (ι : Fin m × Fin n → σ), Function.Injective ι →
  ∀ (α : Fin m → ℕ) (P : MvPolynomial σ ℂ), P ≠ 0 → (∀ a b : Fin m, a < b → PI.FJM.bRow ι a b P = 0) →
    (∀ e ∈ P.support, ∀ i, ∑ k : Fin n, e (ι (i, k)) = α i) → Antitone α

section Block

variable {σ : Type} {m n : ℕ} (ι : Fin m × Fin n → σ)

/- English proof (translation)
Simplify using `[PI.FJM.bRow, LinearMap.sum_apply, Module.End.mul_apply]`.
-/
theorem bRow_apply' (a b : Fin m) (P : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b P = ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (b, k)) P := by
  simp [PI.FJM.bRow, LinearMap.sum_apply, Module.End.mul_apply]

/- English proof (translation)
Rewrite using `[Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem pd_X_mul [DecidableEq σ] (l v : σ) (Q : MvPolynomial σ ℂ) :
    pderiv l (X v * Q) = X v * pderiv l Q + (if v = l then Q else 0) := by
  rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, Pi.single_apply]
  split_ifs <;> simp

/- English proof (translation)
Simplify using `[hι.eq_iff]`.
-/
theorem sum_ite_row [DecidableEq σ] (hι : Function.Injective ι) (b : Fin m) (k : Fin n) (G : Fin n → MvPolynomial σ ℂ) :
    ∑ j : Fin n, (if ι (b, j) = ι (b, k) then G j else 0) = G k := by
  simp [hι.eq_iff]

/- English proof (translation)
Rewrite using `[bRow_apply' ι a b, bRow_apply' ι b a]`. Simplify using `only [map_sum, pd_X_mul, Finset.sum_add_distrib, sum_ite_row ι hι, mul_add, Finset.mul_sum]`.
-/
theorem EF_expand (hι : Function.Injective ι) (a b : Fin m) (P : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b (PI.FJM.bRow ι b a P) =
      (∑ k : Fin n, ∑ j : Fin n, X (ι (a, k)) * (X (ι (b, j)) * pderiv (ι (b, k)) (pderiv (ι (a, j)) P))) +
        ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (a, k)) P := by
  classical
  rw [bRow_apply' ι a b, bRow_apply' ι b a]
  simp only [map_sum, pd_X_mul, Finset.sum_add_distrib, sum_ite_row ι hι, mul_add, Finset.mul_sum]

/- English proof (translation)
Establish `h : ⁅(pderiv i : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)), (pderiv j : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))⁆ = 0`. Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises. Introduce `k`. Rewrite using `[Derivation.commutator_apply, pderiv_X, pderiv_X, Derivation.zero_apply]`. Simplify using `only [Pi.single_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Use `congrArg (fun D => D p) h` as an intermediate fact. Simplify using `only [Derivation.commutator_apply, Derivation.zero_apply] at this`. Conclude with `sub_eq_zero.1 this`.
-/
private theorem pderiv_pderiv_comm' {σ : Type} (i j : σ) (p : MvPolynomial σ ℂ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  have h : ⁅(pderiv i : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)),
      (pderiv j : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X, Derivation.zero_apply]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have := congrArg (fun D => D p) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at this
  exact sub_eq_zero.1 this

/- English proof (translation)
Rewrite using `[EF_expand ι hι a b, EF_expand ι hι b a]`. Establish `hS : (∑ k : Fin n, ∑ j : Fin n, X (ι (b, k)) * (X (ι (a, j)) * pderiv (ι (a, k)) (pderiv (ι (b, j)) P))) = ∑ k : Fin n, ∑ j : Fin n, X (ι (a, k)) * (X (ι (b, j)) * pderiv (ι (b, k)) (pderiv (ι (a, j)) P))`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[pderiv_pderiv_comm' (ι (a, j)) (ι (b, k)) P]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hS]`. Normalize the expressions using the abelian group laws.
-/
theorem comm_eq (hι : Function.Injective ι) (a b : Fin m) (P : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b (PI.FJM.bRow ι b a P) - PI.FJM.bRow ι b a (PI.FJM.bRow ι a b P) =
      ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (a, k)) P - ∑ k : Fin n, X (ι (b, k)) * pderiv (ι (b, k)) P := by
  rw [EF_expand ι hι a b, EF_expand ι hι b a]
  have hS : (∑ k : Fin n, ∑ j : Fin n,
      X (ι (b, k)) * (X (ι (a, j)) * pderiv (ι (a, k)) (pderiv (ι (b, j)) P))) =
      ∑ k : Fin n, ∑ j : Fin n, X (ι (a, k)) * (X (ι (b, j)) * pderiv (ι (b, k)) (pderiv (ι (a, j)) P)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [pderiv_pderiv_comm' (ι (a, j)) (ι (b, k)) P]
    ring
  rw [hS]
  abel

/- English proof (translation)
Use `conv_lhs => rw [P.as_sum]`. Use `conv_rhs => rw [P.as_sum]`. Simplify using `only [map_sum, Finset.mul_sum, X_mul_pderiv_monomial]`. Rewrite using `[Finset.sum_comm, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun e he => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_smul, hP e he]`. Conclude with `(Nat.cast_smul_eq_nsmul ℂ c _).symm`.
-/
theorem euler_row (a : Fin m) (c : ℕ) (P : MvPolynomial σ ℂ)
    (hP : ∀ e ∈ P.support, ∑ k : Fin n, e (ι (a, k)) = c) :
    ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (a, k)) P = (c : ℂ) • P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum, Finset.mul_sum, X_mul_pderiv_monomial]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [← Finset.sum_smul, hP e he]
  exact (Nat.cast_smul_eq_nsmul ℂ c _).symm

end Block

section Inner

variable {σ : Type}

/- English proof (translation)
Unfold `fockInner`. Simplify using the standard rewrite rules.
-/
theorem inner_zero_right (P : MvPolynomial σ ℂ) : fockInner P 0 = 0 := by
  unfold fockInner
  simp

/- English proof (translation)
Proceed by induction on `t using Finset.cons_induction with`. Consider the case `empty => rw [Finset.sum_empty, Finset.sum_empty, inner_zero_right]`. Consider the case `cons i t hi ih`. Rewrite using `[Finset.sum_cons, Finset.sum_cons, FockRaiseLowInner.fockInner_add_right, ih]`.
-/
theorem inner_sum_right {ι : Type*} (t : Finset ι) (P : MvPolynomial σ ℂ) (f : ι → MvPolynomial σ ℂ) :
    fockInner P (∑ i ∈ t, f i) = ∑ i ∈ t, fockInner P (f i) := by
  induction t using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, inner_zero_right]
  | cons i t hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons, FockRaiseLowInner.fockInner_add_right, ih]

/- English proof (translation)
Rewrite using `[FockRaiseLowInner.fockInner_eq_sum_left Q P (P.support ∪ Q.support) Finset.subset_union_right, FockRaiseLowInner.fockInner_eq_sum_left P Q (P.support ∪ Q.support) Finset.subset_union_left, map_sum]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, Complex.conj_conj, FockRaiseLowInner.wt_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inner_conj (P Q : MvPolynomial σ ℂ) : fockInner Q P = starRingEnd ℂ (fockInner P Q) := by
  classical
  rw [FockRaiseLowInner.fockInner_eq_sum_left Q P (P.support ∪ Q.support) Finset.subset_union_right,
    FockRaiseLowInner.fockInner_eq_sum_left P Q (P.support ∪ Q.support) Finset.subset_union_left, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_mul, map_mul, Complex.conj_conj, FockRaiseLowInner.wt_conj]
  ring

/- English proof (translation)
Proceed by induction on `t using Finset.cons_induction with`. Consider the case `empty => rw [Finset.sum_empty, Finset.sum_empty, FockRaiseLowInner.fockInner_zero_left]`. Consider the case `cons i t hi ih`. Rewrite using `[Finset.sum_cons, Finset.sum_cons, FockRaiseLowInner.fockInner_add_left, ih]`.
-/
theorem inner_sum_left {ι : Type*} (t : Finset ι) (f : ι → MvPolynomial σ ℂ) (Q : MvPolynomial σ ℂ) :
    fockInner (∑ i ∈ t, f i) Q = ∑ i ∈ t, fockInner (f i) Q := by
  induction t using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, FockRaiseLowInner.fockInner_zero_left]
  | cons i t hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons, FockRaiseLowInner.fockInner_add_left, ih]

/- English proof (translation)
Rewrite using `[inner_conj Q (X l * P), FockRaiseLowInner.fockInner_mul_X, inner_conj P (pderiv l Q), Complex.conj_conj]`.
-/
theorem inner_X_left (l : σ) (P Q : MvPolynomial σ ℂ) :
    fockInner (X l * P) Q = fockInner P (pderiv l Q) := by
  rw [inner_conj Q (X l * P), FockRaiseLowInner.fockInner_mul_X, inner_conj P (pderiv l Q), Complex.conj_conj]

/- English proof (translation)
Rewrite using `[inner_conj Q (pderiv l P), ← inner_X_left l Q P, inner_conj P (X l * Q), Complex.conj_conj]`.
-/
theorem inner_pd_left (l : σ) (P Q : MvPolynomial σ ℂ) :
    fockInner (pderiv l P) Q = fockInner P (X l * Q) := by
  rw [inner_conj Q (pderiv l P), ← inner_X_left l Q P, inner_conj P (X l * Q), Complex.conj_conj]

end Inner

/- English proof (translation)
Rewrite using `[bRow_apply' ι b a x, bRow_apply' ι a b y, inner_sum_left, inner_sum_right]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[inner_X_left, inner_pd_left]`.
-/
theorem bRow_adj {σ : Type} {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) (x y : MvPolynomial σ ℂ) :
    fockInner (PI.FJM.bRow ι b a x) y = fockInner x (PI.FJM.bRow ι a b y) := by
  rw [bRow_apply' ι b a x, bRow_apply' ι a b y, inner_sum_left, inner_sum_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_X_left, inner_pd_left]

/- English proof (translation)
Introduce `σ m n ι hι α P hP hE hdeg a b hab`. Break down `eq_or_lt_of_le hab with h | h` into its components or cases. Rewrite using `[h]`. Establish `hc` using `comm_eq ι hι a b P`. Rewrite `hc` using `[hE a b h, map_zero, sub_zero, euler_row ι a (α a) P (fun e he => hdeg e he a), euler_row ι b (α b) P (fun e he => hdeg e he b)]`.

Establish `hadj` using `bRow_adj ι a b P (PI.FJM.bRow ι b a P)`. Rewrite `hadj` using `[hc, ← sub_smul, FockRaiseLowInner.fockInner_smul_right]`. Establish `h1` using `PI.FockOneDegW.Inner.fockInner_self_re_nonneg (PI.FJM.bRow ι b a P)`. Rewrite `h1` using `[hadj]`. Establish `hre` using `PI.FockOneDegW.Inner.fockInner_self_re_nonneg P`.

Establish `him` using `PI.FockOneDegW.Inner.fockInner_self_im P`. Establish `hpos : 0 < (fockInner P P).re` using `lt_of_le_of_ne hre (fun h0 => hP (PI.FockOneDegW.Inner.eq_zero_of_fockInner_self_re P h0.symm))`. Rewrite `h1` using `[Complex.mul_re, him, mul_zero, sub_zero]`. Simplify using `only [Complex.sub_re, Complex.natCast_re] at h1`. Establish `hlt : (α b : ℝ) ≤ α a` using `by nlinarith`.

Conclude with `hlt` after adjusting the coercions.
-/
theorem block_degree_antitone : BlockAntitone := by
  intro σ m n ι hι α P hP hE hdeg a b hab
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · have hc := comm_eq ι hι a b P
    rw [hE a b h, map_zero, sub_zero, euler_row ι a (α a) P (fun e he => hdeg e he a),
      euler_row ι b (α b) P (fun e he => hdeg e he b)] at hc
    have hadj := bRow_adj ι a b P (PI.FJM.bRow ι b a P)
    rw [hc, ← sub_smul, FockRaiseLowInner.fockInner_smul_right] at hadj
    have h1 := PI.FockOneDegW.Inner.fockInner_self_re_nonneg (PI.FJM.bRow ι b a P)
    rw [hadj] at h1
    have hre := PI.FockOneDegW.Inner.fockInner_self_re_nonneg P
    have him := PI.FockOneDegW.Inner.fockInner_self_im P
    have hpos : 0 < (fockInner P P).re := lt_of_le_of_ne hre
      (fun h0 => hP (PI.FockOneDegW.Inner.eq_zero_of_fockInner_self_re P h0.symm))
    rw [Complex.mul_re, him, mul_zero, sub_zero] at h1
    simp only [Complex.sub_re, Complex.natCast_re] at h1
    have hlt : (α b : ℝ) ≤ α a := by nlinarith
    exact_mod_cast hlt

end PI.FJMF
