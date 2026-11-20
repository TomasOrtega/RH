import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt

noncomputable section

open MeasureTheory MvPolynomial
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.FFTSteps.AsmA

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp only [aeval_C, MvPolynomial.algebraMap_eq, eval_C]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp => simp only [map_mul, aeval_X, eval_X, hp]`.
-/
theorem eval_aeval' {σ τ : Type} (φ : σ → MvPolynomial τ ℂ) (z : τ → ℂ) (p : MvPolynomial σ ℂ) :
    eval z (aeval φ p) = eval (fun v => eval z (φ v)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, MvPolynomial.algebraMap_eq, eval_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp only [map_mul, aeval_X, eval_X, hp]

variable {ι A B : Type} [Fintype ι]

def act (g h : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) : (ι × A) ⊕ (ι × B) → ℂ :=
  Sum.elim (fun x => ∑ j, g x.1 j * z (Sum.inl (j, x.2))) (fun y => ∑ j, h y.1 j * z (Sum.inr (j, y.2)))

/- English proof (translation)
Unfold `sub`. Rewrite using `[eval_aeval']`. Establish `e : (fun v => eval z (Sum.elim (fun x : ι × A => ∑ j, C (g x.1 j) * (X (Sum.inl (j, x.2)) : PV ι A B)) (fun y : ι × B => ∑ j, C (h y.1 j) * X (Sum.inr (j, y.2))) v)) = act g h z`. Use function extensionality and compare the values at `v`. Apply the tactic sequence `rcases v with ⟨i, a⟩ | ⟨i, b⟩ <;> simp [act, map_sum]`.

Rewrite using `[e]`.
-/
theorem eval_sub (g h : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) (p : PV ι A B) :
    eval z (sub g h p) = eval (act g h z) p := by
  unfold sub
  rw [eval_aeval']
  have e : (fun v => eval z (Sum.elim (fun x : ι × A => ∑ j, C (g x.1 j) * (X (Sum.inl (j, x.2)) : PV ι A B))
      (fun y : ι × B => ∑ j, C (h y.1 j) * X (Sum.inr (j, y.2))) v)) = act g h z := by
    funext v
    rcases v with ⟨i, a⟩ | ⟨i, b⟩ <;> simp [act, map_sum]
  rw [e]

/- English proof (translation)
Use function extensionality and compare the values at `v`. Break down `v with ⟨i, a⟩ | ⟨i, b⟩` into its components or cases. Simplify using `only [act, Sum.elim_inl, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]`. Conclude with `Finset.sum_comm`. Simplify using `only [act, Sum.elim_inr, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]`.

Conclude with `Finset.sum_comm`.
-/
theorem act_act (g h g' h' : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    act g h (act g' h' z) = act (g * g') (h * h') z := by
  funext v
  rcases v with ⟨i, a⟩ | ⟨i, b⟩
  · simp only [act, Sum.elim_inl, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  · simp only [act, Sum.elim_inr, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm

/- English proof (translation)
Use function extensionality and compare the values at `v`. Apply the tactic sequence `rcases v with ⟨i, a⟩ | ⟨i, b⟩ <;> simp [act, Matrix.one_apply]`.
-/
theorem act_one_one (z : (ι × A) ⊕ (ι × B) → ℂ) [DecidableEq ι] : act (1 : Matrix ι ι ℂ) 1 z = z := by
  funext v
  rcases v with ⟨i, a⟩ | ⟨i, b⟩ <;> simp [act, Matrix.one_apply]

/- English proof (translation)
Use `(MvPolynomial.continuous_eval p).comp (continuous_pi fun v => ?_)` and prove the remaining obligations. Break down `v with ⟨i, a⟩ | ⟨i, b⟩` into its components or cases. Simplify using `only [act, Sum.elim_inl]`. Conclude with `continuous_finsetSum _ fun j _ => (hF.matrix_elem i j).mul continuous_const`. Simplify using `only [act, Sum.elim_inr]`.

Conclude with `continuous_finsetSum _ fun j _ => (hG.matrix_elem i j).mul continuous_const`.
-/
theorem continuous_act_eval {X : Type} [TopologicalSpace X] {F G : X → Matrix ι ι ℂ} (hF : Continuous F)
    (hG : Continuous G) (z : (ι × A) ⊕ (ι × B) → ℂ) (p : PV ι A B) :
    Continuous fun x => eval (act (F x) (G x) z) p := by
  refine (MvPolynomial.continuous_eval p).comp (continuous_pi fun v => ?_)
  rcases v with ⟨i, a⟩ | ⟨i, b⟩
  · simp only [act, Sum.elim_inl]
    exact continuous_finsetSum _ fun j _ => (hF.matrix_elem i j).mul continuous_const
  · simp only [act, Sum.elim_inr]
    exact continuous_finsetSum _ fun j _ => (hG.matrix_elem i j).mul continuous_const

/- English proof (translation)
Use `conv_lhs => rw [p.as_sum]`. Rewrite using `[map_sum]`. Use `(totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)` and prove the remaining obligations. Rewrite using `[aeval_monomial]`. Use `(totalDegree_mul _ _).trans ?_` and prove the remaining obligations.

Establish `h1 : (algebraMap ℂ (MvPolynomial τ ℂ) (coeff m p)).totalDegree = 0`. Rewrite using `[MvPolynomial.algebraMap_eq]`. Conclude with `totalDegree_C _`. Rewrite using `[h1, zero_add, Finsupp.prod]`. Use `(totalDegree_finsetProd _ _).trans ?_` and prove the remaining obligations.

Use `le_trans (Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (h i))) ?_` and prove the remaining obligations. Simplify using `only [mul_one]`. Conclude with `le_totalDegree hm`.
-/
theorem totalDegree_aeval_le {σ τ : Type} (φ : σ → MvPolynomial τ ℂ) (h : ∀ v, (φ v).totalDegree ≤ 1)
    (p : MvPolynomial σ ℂ) : (aeval φ p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  have h1 : (algebraMap ℂ (MvPolynomial τ ℂ) (coeff m p)).totalDegree = 0 := by
    rw [MvPolynomial.algebraMap_eq]; exact totalDegree_C _
  rw [h1, zero_add, Finsupp.prod]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left _ (h i))) ?_
  simp only [mul_one]
  exact le_totalDegree hm

/- English proof (translation)
Use `totalDegree_aeval_le _ (fun v => ?_) p` and prove the remaining obligations. Break down `v with ⟨i, a⟩ | ⟨i, b⟩` into its components or cases. Simplify using `only [Sum.elim_inl]`. Use `(totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)` and prove the remaining obligations. Conclude with `(totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])`.

Simplify using `only [Sum.elim_inr]`. Use `(totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)` and prove the remaining obligations. Conclude with `(totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])`.
-/
theorem totalDegree_sub_le (g h : Matrix ι ι ℂ) (p : PV ι A B) : (sub g h p).totalDegree ≤ p.totalDegree := by
  refine totalDegree_aeval_le _ (fun v => ?_) p
  rcases v with ⟨i, a⟩ | ⟨i, b⟩
  · simp only [Sum.elim_inl]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])
  · simp only [Sum.elim_inr]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])

/- English proof (translation)
Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `z`. Rewrite using `[eval_sub, act_one_one]`.
-/
theorem sub_one_one [DecidableEq ι] (p : PV ι A B) : sub (1 : Matrix ι ι ℂ) 1 p = p := by
  apply MvPolynomial.funext
  intro z
  rw [eval_sub, act_one_one]

end PositivityTheory.Rg.Sw.FFTSteps.AsmA
