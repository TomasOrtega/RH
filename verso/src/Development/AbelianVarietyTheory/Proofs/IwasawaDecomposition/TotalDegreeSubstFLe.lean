import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeAevalLeOfLinear

noncomputable section

open MvPolynomial

namespace GlobalTheory.CompactHowe

variable {ι : Type} {N n : ℕ}

def subst2 (h : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (Fin N × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin N × Fin n) ℂ :=
  aeval fun p => ∑ k, ∑ l, C (h k p.1 * g l p.2) * X (k, l)

def substF (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (ι × Fin N × Fin n) ℂ →ₐ[ℂ] MvPolynomial (ι × Fin N × Fin n) ℂ :=
  aeval fun p => ∑ k, ∑ l, C (h p.1 k p.2.1 * g p.1 l p.2.2) * X (p.1, k, l)

/- English proof (translation)
The claim follows from `aeval_X _ _`.
-/
theorem subst2_X (h : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin n) (Fin n) ℂ) (p : Fin N × Fin n) :
    subst2 h g (X p) = ∑ k, ∑ l, C (h k p.1 * g l p.2) * X (k, l) := aeval_X _ _

/- English proof (translation)
The claim follows from `aeval_X _ _`.
-/
theorem substF_X (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (p : ι × Fin N × Fin n) :
    substF h g (X p) = ∑ k, ∑ l, C (h p.1 k p.2.1 * g p.1 l p.2.2) * X (p.1, k, l) := aeval_X _ _

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.AevalTotalDegreeLinear.main`. Consider the case `exact _root_.GlobalTheory.AevalTotalDegreeLinear.main`. Consider the case `(apply _root_.GlobalTheory.AevalTotalDegreeLinear.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.AevalTotalDegreeLinear.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.AevalTotalDegreeLinear.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.AevalTotalDegreeLinear.main ..)`.
-/
theorem totalDegree_aeval_le {κ : Type} (f : κ → MvPolynomial κ ℂ) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (P : MvPolynomial κ ℂ) : (aeval f P).totalDegree ≤ P.totalDegree := by
  first
  | exact @_root_.GlobalTheory.AevalTotalDegreeLinear.main
  | exact _root_.GlobalTheory.AevalTotalDegreeLinear.main
  | (apply _root_.GlobalTheory.AevalTotalDegreeLinear.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AevalTotalDegreeLinear.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AevalTotalDegreeLinear.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AevalTotalDegreeLinear.main ..)

/- English proof (translation)
The claim follows from `totalDegree_aeval_le _ (fun _ => totalDegree_finsetSum_le fun _ _ => totalDegree_finsetSum_le fun _ _ => (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])) P`.
-/
theorem totalDegree_substF_le (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) : (substF h g P).totalDegree ≤ P.totalDegree :=
  totalDegree_aeval_le _ (fun _ => totalDegree_finsetSum_le fun _ _ => totalDegree_finsetSum_le fun _ _ =>
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])) P

/- English proof (translation)
Establish `key : (subst2 h g).comp (subst2 h' g') = subst2 (h * h') (g * g')`. Use `algHom_ext fun p => ?_` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, subst2_X, subst2_X]`. Simplify using `only [map_sum, map_mul, subst2_X, algHom_C, algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm' (s := Finset.univ) (t := fun _ => Finset.univ) (t' := Finset.univ) (s' := fun _ => Finset.univ) (by simp)]`.

Simplify using `only [← Finset.sum_product', Finset.univ_product_univ]`. Use `Fintype.sum_equiv ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun y => (y.2.2.1, y.2.2.2, y.1, y.2.1), fun _ => rfl, fun _ => rfl⟩ _ _ fun x => ?_` and prove the remaining obligations. Simplify using `only [Equiv.coe_fn_mk]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `congrArg (fun f => f P) key`.
-/
theorem subst2_mul (h h' : Matrix (Fin N) (Fin N) ℂ) (g g' : Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (Fin N × Fin n) ℂ) : subst2 h g (subst2 h' g' P) = subst2 (h * h') (g * g') P := by
  have key : (subst2 h g).comp (subst2 h' g') = subst2 (h * h') (g * g') := by
    refine algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, subst2_X, subst2_X]
    simp only [map_sum, map_mul, subst2_X, algHom_C, algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun _ => Finset.univ) (t' := Finset.univ) (s' := fun _ => Finset.univ) (by simp)]
    simp only [← Finset.sum_product', Finset.univ_product_univ]
    refine Fintype.sum_equiv ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun y => (y.2.2.1, y.2.2.2, y.1, y.2.1), fun _ => rfl, fun _ => rfl⟩ _ _ fun x => ?_
    simp only [Equiv.coe_fn_mk]
    ring
  exact congrArg (fun f => f P) key

/- English proof (translation)
Establish `key : subst2 (1 : Matrix (Fin N) (Fin N) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ) = AlgHom.id ℂ _`. Use `algHom_ext fun p => ?_` and prove the remaining obligations. Rewrite using `[subst2_X, Finset.sum_eq_single p.1, Finset.sum_eq_single p.2]`. Simplify using the standard rewrite rules. Introduce `l _ hl`.

Simplify using `[Matrix.one_apply_ne hl]`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Simplify using `[Matrix.one_apply_ne hk]`. Simplify using the standard rewrite rules.

Rewrite using `[key]`. Both sides reduce to the same expression.
-/
theorem subst2_one (P : MvPolynomial (Fin N × Fin n) ℂ) : subst2 1 1 P = P := by
  have key : subst2 (1 : Matrix (Fin N) (Fin N) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ) = AlgHom.id ℂ _ := by
    refine algHom_ext fun p => ?_
    rw [subst2_X, Finset.sum_eq_single p.1, Finset.sum_eq_single p.2]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
    · intro k _ hk; simp [Matrix.one_apply_ne hk]
    · simp
  rw [key]; rfl

end GlobalTheory.CompactHowe

end
