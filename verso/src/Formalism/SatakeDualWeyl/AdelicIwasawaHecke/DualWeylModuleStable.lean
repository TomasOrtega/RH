import Formalism.SatakeDualWeyl.StatementW
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

noncomputable section

open MvPolynomial

namespace Formalism.UG.P

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨i, j⟩`. Simplify using `only [Formalism.GradedWeylDivisibility.rowAct, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Use `first`. Consider the case `exact Finset.sum_comm`.

Consider the case `(rw [Finset.sum_comm])`.
-/
theorem wact_rowAct_mul (R : Type) [CommRing R] (r n : ℕ) (A B : Matrix (Fin r) (Fin r) R) :
    Formalism.GradedWeylDivisibility.rowAct R (n := n) (A * B) = (Formalism.GradedWeylDivisibility.rowAct R (n := n) B).comp (Formalism.GradedWeylDivisibility.rowAct R A) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  simp only [Formalism.GradedWeylDivisibility.rowAct, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  first
  | exact Finset.sum_comm
  | (rw [Finset.sum_comm])

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨i, j⟩`. Simplify using `[Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply, apply_ite C, ite_mul]`.
-/
theorem wact_rowAct_one (R : Type) [CommRing R] (r n : ℕ) :
    Formalism.GradedWeylDivisibility.rowAct R (n := n) (1 : Matrix (Fin r) (Fin r) R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply, apply_ite C, ite_mul]

/- English proof (translation)
Introduce `R _ r n g h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Formalism.UG.dwAct]`. Rewrite using `[mul_inv_rev, Units.val_mul, wact_rowAct_mul]`. Simplify using `only [Formalism.UG.dwAct, inv_one, Units.val_one]`.

Conclude with `wact_rowAct_one R r n`.
-/
theorem dual_weyl_action_mul : Formalism.UG.DwActMul := by
  intro R _ r n g h
  refine ⟨?_, ?_⟩
  · simp only [Formalism.UG.dwAct]
    rw [mul_inv_rev, Units.val_mul, wact_rowAct_mul]
  · simp only [Formalism.UG.dwAct, inv_one, Units.val_one]
    exact wact_rowAct_one R r n

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => first`. Consider the case `simpa using isWeightedHomogeneous_C w (1 : R)`. Consider the case `simpa using isWeightedHomogeneous_one R w`. Consider the case `succ k ih`.

Rewrite using `[pow_succ, succ_nsmul]`. Conclude with `ih.mul h`.
-/
private theorem isWeightedHomogeneous_pow' {σ R M : Type*} [CommRing R] [AddCommMonoid M] {w : σ → M}
    {φ : MvPolynomial σ R} {m : M} (h : IsWeightedHomogeneous w φ m) (k : ℕ) :
    IsWeightedHomogeneous w (φ ^ k) (k • m) := by
  induction k with
  | zero =>
    first
    | simpa using isWeightedHomogeneous_C w (1 : R)
    | simpa using isWeightedHomogeneous_one R w
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact ih.mul h

/- English proof (translation)
Rewrite using `[← mem_weightedHomogeneousSubmodule, f.as_sum, map_sum]`. Use `Submodule.sum_mem _ fun d hd => ?_` and prove the remaining obligations. Rewrite using `[mem_weightedHomogeneousSubmodule]`. Establish `hdw : Finsupp.weight w d = m` using `hf (mem_support_iff.mp hd)`. Establish `hprod : IsWeightedHomogeneous w (φ (d.prod fun n e => X n ^ e)) (Finsupp.weight w d)`.

Rewrite using `[Finsupp.prod, map_prod, Finsupp.weight_apply, Finsupp.sum]`. Apply `IsWeightedHomogeneous.prod` to reduce the goal to its premises. Introduce `v _`. Rewrite using `[map_pow]`. Conclude with `isWeightedHomogeneous_pow' (hφ v) (d v)`.

Establish `hC : φ (C (coeff d f)) = C (coeff d f)`. Rewrite using `[← MvPolynomial.algebraMap_eq]`. Conclude with `φ.commutes _`. Rewrite using `[monomial_eq, map_mul, hC, ← hdw, ← zero_add (Finsupp.weight w d)]`. Conclude with `(isWeightedHomogeneous_C w _).mul hprod`.
-/
private theorem isWeightedHomogeneous_algHom_apply {σ R M : Type*} [CommRing R] [AddCommMonoid M] (w : σ → M)
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hφ : ∀ v, IsWeightedHomogeneous w (φ (X v)) (w v)) (f : MvPolynomial σ R) (m : M)
    (hf : IsWeightedHomogeneous w f m) : IsWeightedHomogeneous w (φ f) m := by
  rw [← mem_weightedHomogeneousSubmodule, f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [mem_weightedHomogeneousSubmodule]
  have hdw : Finsupp.weight w d = m := hf (mem_support_iff.mp hd)
  have hprod : IsWeightedHomogeneous w (φ (d.prod fun n e => X n ^ e)) (Finsupp.weight w d) := by
    rw [Finsupp.prod, map_prod, Finsupp.weight_apply, Finsupp.sum]
    apply IsWeightedHomogeneous.prod
    intro v _
    rw [map_pow]
    exact isWeightedHomogeneous_pow' (hφ v) (d v)
  have hC : φ (C (coeff d f)) = C (coeff d f) := by
    rw [← MvPolynomial.algebraMap_eq]
    exact φ.commutes _
  rw [monomial_eq, map_mul, hC, ← hdw, ← zero_add (Finsupp.weight w d)]
  exact (isWeightedHomogeneous_C w _).mul hprod

/- English proof (translation)
Introduce `R _ r n ν g f hf`. Unfold `Formalism.UG.dwAct`. Generalize the expression as in `((g⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) = M`. Unfold `Formalism.GradedWeylDivisibility.dualWeyl at hf ⊢`. Rewrite `hf`, the goal using `[Submodule.mem_inf]`.

Take `⟨hw, hk⟩` from `hf`. Prove the components needed by the constructor for the conclusion. Rewrite `hw`, the goal using `[mem_weightedHomogeneousSubmodule]`. Apply `isWeightedHomogeneous_algHom_apply _ _ _ f ν hw` to reduce the goal to its premises. Introduce `v`.

Simplify using `only [Formalism.GradedWeylDivisibility.rowAct, aeval_X]`. Rewrite using `[← mem_weightedHomogeneousSubmodule]`. Use `Submodule.sum_mem _ fun b _ => ?_` and prove the remaining obligations. Rewrite using `[mem_weightedHomogeneousSubmodule]`. Establish `h1` using `(isWeightedHomogeneous_C (Formalism.GradedWeylDivisibility.colW r n) (M v.1 b)).mul (isWeightedHomogeneous_X R (Formalism.GradedWeylDivisibility.colW r n) (b, v.2))`.

Rewrite `h1` using `[zero_add]`. Conclude with `h1`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero] at hk ⊢`. Introduce `l j hlj`. Establish `h1 : (Formalism.GradedWeylDivisibility.colAddGen R (r` using `r) l j).comp (Formalism.GradedWeylDivisibility.rowAct R (n := n) M) = (aeval (fun o : Option (Fin r × Fin n) => o.elim (X none) (fun v => ∑ b : Fin r, C (M v.1 b) * X (some (b, v.2))))).comp (Formalism.GradedWeylDivisibility.colAddGen R (r := r) l j) := by`.

Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨i, k⟩`. Distinguish the cases in `hkj : k = j`. Substitute `hkj` using the available equality. Simplify using `only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.colAddGen, aeval_X, map_sum, map_mul, aeval_C, map_add, if_true, Option.elim, algebraMap_eq]`.

Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `b _`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.colAddGen, hkj]`.

Establish `h2 : (aeval (fun o : Option (Fin r × Fin n) => o.elim (X none) (fun v => ∑ b : Fin r, C (M v.1 b) * X (some (b, v.2))))).comp (rename (R` using `R) (some : Fin r × Fin n → Option (Fin r × Fin n))) = (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).comp (Formalism.GradedWeylDivisibility.rowAct R (n := n) M) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨i, k⟩`. Simplify using `[Formalism.GradedWeylDivisibility.rowAct]`. Establish `e1` using `DFunLike.congr_fun h1 f`.

Establish `e2` using `DFunLike.congr_fun h2 f`. Simplify using `only [AlgHom.comp_apply] at e1 e2`. Rewrite using `[e1, hk l j hlj, e2]`.
-/
theorem dual_weyl_module_stable : Formalism.UG.DwStable := by
  intro R _ r n ν g f hf
  unfold Formalism.UG.dwAct
  generalize ((g⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) = M
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf ⊢
  rw [Submodule.mem_inf] at hf ⊢
  obtain ⟨hw, hk⟩ := hf
  constructor
  · rw [mem_weightedHomogeneousSubmodule] at hw ⊢
    apply isWeightedHomogeneous_algHom_apply _ _ _ f ν hw
    intro v
    simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_X]
    rw [← mem_weightedHomogeneousSubmodule]
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [mem_weightedHomogeneousSubmodule]
    have h1 := (isWeightedHomogeneous_C (Formalism.GradedWeylDivisibility.colW r n) (M v.1 b)).mul
      (isWeightedHomogeneous_X R (Formalism.GradedWeylDivisibility.colW r n) (b, v.2))
    rw [zero_add] at h1
    exact h1
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      AlgHom.toLinearMap_apply, sub_eq_zero] at hk ⊢
    intro l j hlj
    have h1 : (Formalism.GradedWeylDivisibility.colAddGen R (r := r) l j).comp (Formalism.GradedWeylDivisibility.rowAct R (n := n) M) =
        (aeval (fun o : Option (Fin r × Fin n) => o.elim (X none)
          (fun v => ∑ b : Fin r, C (M v.1 b) * X (some (b, v.2))))).comp
          (Formalism.GradedWeylDivisibility.colAddGen R (r := r) l j) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, k⟩
      by_cases hkj : k = j
      · subst hkj
        simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.colAddGen, aeval_X, map_sum, map_mul,
          aeval_C, map_add, if_true, Option.elim, algebraMap_eq]
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro b _
        ring
      · simp [Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.colAddGen, hkj]
    have h2 : (aeval (fun o : Option (Fin r × Fin n) => o.elim (X none)
          (fun v => ∑ b : Fin r, C (M v.1 b) * X (some (b, v.2))))).comp
          (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))) =
        (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).comp
          (Formalism.GradedWeylDivisibility.rowAct R (n := n) M) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, k⟩
      simp [Formalism.GradedWeylDivisibility.rowAct]
    have e1 := DFunLike.congr_fun h1 f
    have e2 := DFunLike.congr_fun h2 f
    simp only [AlgHom.comp_apply] at e1 e2
    rw [e1, hk l j hlj, e2]

end Formalism.UG.P
