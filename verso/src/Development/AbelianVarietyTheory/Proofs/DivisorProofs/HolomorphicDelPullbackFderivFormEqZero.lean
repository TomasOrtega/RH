import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelAtEqSumDOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtReprPullbackHolomorphicFderiv
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm.DelVanish

variable {n : ℕ}

/- English proof (translation)
Simplify using `[delAt, coefwise]`.
-/
theorem delAt_const (c : Alt n) (v : V n) : delAt (fun _ => c) v = 0 := by
  simp [delAt, coefwise]

/- English proof (translation)
Establish `key (a : Fin n) : coefwise (fun f => del f v (coordVec a)) (fun x => F x + G x) = coefwise (fun f => del f v (coordVec a)) F + coefwise (fun f => del f v (coordVec a)) G`. Simplify using `only [coefwise, ← Finset.sum_add_distrib, ← add_smul]`. Use `Finset.sum_congr rfl fun S _ => ?_` and prove the remaining obligations. Simplify using `only [map_add, Finsupp.add_apply]`. Rewrite using `[del_add (hF S) (hG S), ContinuousLinearMap.add_apply]`.

Simplify using `only [delAt, key, mul_add, Finset.sum_add_distrib]`.
-/
theorem delAt_add {F G : V n → Alt n} {v : V n}
    (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    delAt (fun x => F x + G x) v = delAt F v + delAt G v := by
  have key (a : Fin n) : coefwise (fun f => del f v (coordVec a)) (fun x => F x + G x) =
      coefwise (fun f => del f v (coordVec a)) F + coefwise (fun f => del f v (coordVec a)) G := by
    simp only [coefwise, ← Finset.sum_add_distrib, ← add_smul]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [map_add, Finsupp.add_apply]
    rw [del_add (hF S) (hG S), ContinuousLinearMap.add_apply]
  simp only [delAt, key, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Use `conv_lhs => rw [← Finset.univ_sum_single x]`. Simplify using `only [map_sum, Finsupp.finset_sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[show (Pi.single i (x i) : Fin n ⊕ Fin n → ℂ) = x i • Pi.single i 1 by`. Use extensionality with `j`.

Simplify using `[Pi.single_apply]]`. Simplify using the standard rewrite rules.
-/
theorem repr_ι (x : Fin n ⊕ Fin n → ℂ) (S : Finset (Fin (n + n))) :
    (bas n).repr (ExteriorAlgebra.ι ℂ x) S =
      ∑ i, x i * (bas n).repr (ExteriorAlgebra.ι ℂ (Pi.single i 1)) S := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  simp only [map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (Pi.single i (x i) : Fin n ⊕ Fin n → ℂ) = x i • Pi.single i 1 by
    ext j; simp [Pi.single_apply]]
  simp

/- English proof (translation)
Rewrite using `[del_mul hf (differentiableAt_const k), del_const]`. Simplify using the standard rewrite rules.
-/
theorem del_mul_const {f : V n → ℂ} {v : V n} (hf : DifferentiableAt ℝ f v) (k : ℂ) (e : V n) :
    del (fun w => f w * k) v e = del f v e * k := by
  rw [del_mul hf (differentiableAt_const k), del_const]; simp

/- English proof (translation)
Use `Finset.sum_congr rfl fun a _ => congrArg _ ((bas n).ext_elem fun S => ?_)` and prove the remaining obligations. Establish `e : (fun x => (bas n).repr (ExteriorAlgebra.ι ℂ (u x)) S) = fun x => ∑ i, u x i * (bas n).repr (ExteriorAlgebra.ι ℂ (Pi.single i 1)) S` using `funext fun x => repr_ι _ _`. Rewrite using `[FormMul.repr_coefwise, repr_ι, e]`. Rewrite using `[del_sum (fun i _ => (hu i).mul_const _), ContinuousLinearMap.sum_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => del_mul_const (hu i) _ _`.
-/
theorem delAt_ι {u : V n → (Fin n ⊕ Fin n → ℂ)} {v : V n}
    (hu : ∀ i, DifferentiableAt ℝ (fun w => u w i) v) :
    delAt (fun w => ExteriorAlgebra.ι ℂ (u w)) v =
      ∑ a, dz a * ExteriorAlgebra.ι ℂ (fun i => del (fun w => u w i) v (coordVec a)) := by
  refine Finset.sum_congr rfl fun a _ => congrArg _ ((bas n).ext_elem fun S => ?_)
  have e : (fun x => (bas n).repr (ExteriorAlgebra.ι ℂ (u x)) S) = fun x =>
      ∑ i, u x i * (bas n).repr (ExteriorAlgebra.ι ℂ (Pi.single i 1)) S := funext fun x => repr_ι _ _
  rw [FormMul.repr_coefwise, repr_ι, e]
  rw [del_sum (fun i _ => (hu i).mul_const _), ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => del_mul_const (hu i) _ _

/- English proof (translation)
Use `set X := ∑ a, ∑ b, s a b • (dz a * dz b) with hX`. Establish `h : X = -X` using `by conv_lhs => rw [hX, Finset.sum_comm]`. Simplify using `only [hX, ← Finset.sum_neg_distrib, ← smul_neg]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hs, dz, dz, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)]`.

Establish `h2 : (2 : ℂ) • X = 0`. Rewrite using `[two_smul]`. Use `nth_rewrite 2 [h]`. Conclude with `add_neg_cancel X`. Conclude with `(smul_eq_zero.1 h2).resolve_left two_ne_zero`.
-/
theorem sum_symm_dz_mul (s : Fin n → Fin n → ℂ) (hs : ∀ a b, s a b = s b a) :
    ∑ a, ∑ b, s a b • (dz a * dz b) = 0 := by
  set X := ∑ a, ∑ b, s a b • (dz a * dz b) with hX
  have h : X = -X := by
    conv_lhs => rw [hX, Finset.sum_comm]
    simp only [hX, ← Finset.sum_neg_distrib, ← smul_neg]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hs, dz, dz, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)]
  have h2 : (2 : ℂ) • X = 0 := by
    rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel X
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/- English proof (translation)
Establish `hJ : DifferentiableAt ℂ (fderiv ℂ φ) v` using `(hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Establish `hE (b c : Fin n) : DifferentiableAt ℂ (fun w => fderiv ℂ φ w (coordVec b) c) v`. Use `(EuclideanSpace.proj (𝕜 := ℂ) c).differentiableAt.comp v (hJ.clm_apply (differentiableAt_const (coordVec b)))` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Establish `hEr (b c : Fin n) : DifferentiableAt ℝ (fun w => fderiv ℂ φ w (coordVec b) c) v` using `(hE b c).restrictScalars ℝ`.

Establish `hEc (b c : Fin n) : DifferentiableAt ℝ (fun w => conj (fderiv ℂ φ w (coordVec b) c)) v`. Use `Complex.conjCLE.differentiableAt.comp v (hEr b c)` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Establish `hdel (a b c : Fin n) : del (fun w => fderiv ℂ φ w (coordVec b) c) v (coordVec a) = fderiv ℂ (fderiv ℂ φ) v (coordVec a) (coordVec b) c`. Use `del_clm_comp ((EuclideanSpace.proj c).comp (ContinuousLinearMap.apply ℂ (V n) (coordVec b))) (hJ.restrictScalars ℝ) (coordVec a)` as an intermediate fact.

Rewrite `this` using `[del_eq_fderiv hJ]`. Conclude with `this`. Establish `hdelc (a b c : Fin n) : del (fun w => conj (fderiv ℂ φ w (coordVec b) c)) v (coordVec a) = 0`. Rewrite using `[del_conj, dbar_eq_zero (hE b c)]`. Simplify using the standard rewrite rules.

Establish `hsymm : IsSymmSndFDerivAt ℂ φ v` using `hφ.isSymmSndFDerivAt (by simp)`. Establish `hF : (fun w => pull (fderiv ℂ φ w) (ExteriorAlgebra.ι ℂ m)) = fun w => ExteriorAlgebra.ι ℂ (Sum.elim (fun b => ∑ c, fderiv ℂ φ w (coordVec b) c * m (.inl c)) (fun b => ∑ c, conj (fderiv ℂ φ w (coordVec b) c) * m (.inr c)))`. Use function extensionality and compare the values at `w`. Rewrite using `[pull, ExteriorAlgebra.map_apply_ι]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `rcases i with b | b <;> simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]`. Establish `hu : ∀ i, DifferentiableAt ℝ (fun w => Sum.elim (fun b => ∑ c, fderiv ℂ φ w (coordVec b) c * m (.inl c)) (fun b => ∑ c, conj (fderiv ℂ φ w (coordVec b) c) * m (.inr c)) i) v`. Introduce and unpack `(b | b)`. Simplify using `using DifferentiableAt.fun_sum (u := Finset.univ) fun c _ => (hEr b c).mul_const (m (.inl c))`.

Simplify using `using DifferentiableAt.fun_sum (u := Finset.univ) fun c _ => (hEc b c).mul_const (m (.inr c))`. Use `set s : Fin n → Fin n → ℂ := fun a b => ∑ c, fderiv ℂ (fderiv ℂ φ) v (coordVec a) (coordVec b) c * m (.inl c) with hs`. Establish `hw (a : Fin n) : (fun i => del (fun w => Sum.elim (fun b => ∑ c, fderiv ℂ φ w (coordVec b) c * m (.inl c)) (fun b => ∑ c, conj (fderiv ℂ φ w (coordVec b) c) * m (.inr c)) i) v (coordVec a)) = ∑ b, s a b • Pi.single (Sum.inl b) 1`. Use function extensionality and compare the values at `i`. Break down `i with b | b` into its components or cases.

Simplify using `only [Sum.elim_inl]`. Rewrite using `[del_sum (fun c _ => (hEr b c).mul_const _), ContinuousLinearMap.sum_apply]`. Simplify using `[del_mul_const (hEr _ _), hdel, Finset.sum_apply, Pi.single_apply, hs]`. Simplify using `only [Sum.elim_inr]`. Rewrite using `[del_sum (fun c _ => (hEc b c).mul_const _), ContinuousLinearMap.sum_apply]`.

Simplify using `[del_mul_const (hEc _ _), hdelc, Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hF, delAt_ι hu]`. Simplify using `only [hw, map_sum, map_smul, Finset.mul_sum, mul_smul_comm]`. Conclude with `sum_symm_dz_mul s fun a b => by simp only [hs, hsymm (coordVec a) (coordVec b)]`.
-/
theorem delAt_pull_fderiv_ι {φ : V n → V n} {v : V n} (hφ : ContDiffAt ℂ 2 φ v) (m : Fin n ⊕ Fin n → ℂ) :
    delAt (fun w => pull (fderiv ℂ φ w) (ExteriorAlgebra.ι ℂ m)) v = 0 := by
  have hJ : DifferentiableAt ℂ (fderiv ℂ φ) v :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hE (b c : Fin n) : DifferentiableAt ℂ (fun w => fderiv ℂ φ w (coordVec b) c) v :=
    by
      have := (EuclideanSpace.proj (𝕜 := ℂ) c).differentiableAt.comp v
        (hJ.clm_apply (differentiableAt_const (coordVec b)))
      simpa [Function.comp_def] using this
  have hEr (b c : Fin n) : DifferentiableAt ℝ (fun w => fderiv ℂ φ w (coordVec b) c) v :=
    (hE b c).restrictScalars ℝ
  have hEc (b c : Fin n) : DifferentiableAt ℝ (fun w => conj (fderiv ℂ φ w (coordVec b) c)) v := by
    have := Complex.conjCLE.differentiableAt.comp v (hEr b c)
    simpa [Function.comp_def] using this
  have hdel (a b c : Fin n) : del (fun w => fderiv ℂ φ w (coordVec b) c) v (coordVec a) =
      fderiv ℂ (fderiv ℂ φ) v (coordVec a) (coordVec b) c := by
    have := del_clm_comp ((EuclideanSpace.proj c).comp (ContinuousLinearMap.apply ℂ (V n) (coordVec b)))
      (hJ.restrictScalars ℝ) (coordVec a)
    rw [del_eq_fderiv hJ] at this
    exact this
  have hdelc (a b c : Fin n) : del (fun w => conj (fderiv ℂ φ w (coordVec b) c)) v (coordVec a) = 0 := by
    rw [del_conj, dbar_eq_zero (hE b c)]; simp
  have hsymm : IsSymmSndFDerivAt ℂ φ v := hφ.isSymmSndFDerivAt (by simp)
  have hF : (fun w => pull (fderiv ℂ φ w) (ExteriorAlgebra.ι ℂ m)) = fun w => ExteriorAlgebra.ι ℂ
      (Sum.elim (fun b => ∑ c, fderiv ℂ φ w (coordVec b) c * m (.inl c))
        (fun b => ∑ c, conj (fderiv ℂ φ w (coordVec b) c) * m (.inr c))) := by
    funext w
    rw [pull, ExteriorAlgebra.map_apply_ι]
    congr 1
    funext i
    rcases i with b | b <;> simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  have hu : ∀ i, DifferentiableAt ℝ (fun w => Sum.elim (fun b => ∑ c, fderiv ℂ φ w (coordVec b) c * m (.inl c))
      (fun b => ∑ c, conj (fderiv ℂ φ w (coordVec b) c) * m (.inr c)) i) v := by
    rintro (b | b)
    · simpa using DifferentiableAt.fun_sum (u := Finset.univ) fun c _ => (hEr b c).mul_const (m (.inl c))
    · simpa using DifferentiableAt.fun_sum (u := Finset.univ) fun c _ => (hEc b c).mul_const (m (.inr c))
  set s : Fin n → Fin n → ℂ := fun a b => ∑ c, fderiv ℂ (fderiv ℂ φ) v (coordVec a) (coordVec b) c * m (.inl c)
    with hs
  have hw (a : Fin n) : (fun i => del (fun w => Sum.elim (fun b => ∑ c, fderiv ℂ φ w (coordVec b) c * m (.inl c))
      (fun b => ∑ c, conj (fderiv ℂ φ w (coordVec b) c) * m (.inr c)) i) v (coordVec a)) =
      ∑ b, s a b • Pi.single (Sum.inl b) 1 := by
    funext i
    rcases i with b | b
    · simp only [Sum.elim_inl]
      rw [del_sum (fun c _ => (hEr b c).mul_const _), ContinuousLinearMap.sum_apply]
      simp [del_mul_const (hEr _ _), hdel, Finset.sum_apply, Pi.single_apply, hs]
    · simp only [Sum.elim_inr]
      rw [del_sum (fun c _ => (hEc b c).mul_const _), ContinuousLinearMap.sum_apply]
      simp [del_mul_const (hEc _ _), hdelc, Finset.sum_apply, Pi.single_apply]
  rw [hF, delAt_ι hu]
  simp only [hw, map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
  exact sum_symm_dz_mul s fun a b => by simp only [hs, hsymm (coordVec a) (coordVec b)]

/- English proof (translation)
Introduce `n φ v hφ γ`. Establish `hD` using `fun γ S => GlobalTheory.CxForm.differentiableAt_repr_pull_fderiv hφ γ S`. Proceed by induction on `γ using ExteriorAlgebra.induction with`. Consider the case `algebraMap r => simp only [AlgHom.commutes]`. Conclude with `delAt_const _ _`.

Consider the case `ι m => exact delAt_pull_fderiv_ι hφ m`. Consider the case `mul a b ha hb`. Take `⟨y, hy⟩` from `FormMul.delAt_mul (hD a) (hD b)`. Simplify using `only [map_mul]`. Rewrite using `[hy, ha, hb, zero_mul, mul_zero, add_zero]`.

Consider the case `add a b ha hb`. Simplify using `only [map_add]`. Rewrite using `[delAt_add (hD a) (hD b), ha, hb, add_zero]`.
-/
theorem delAt_pull_fderiv : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n} {v : ReciprocityTheory.L2DbarEstimates.V n},
    ContDiffAt ℂ 2 φ v → ∀ γ : GlobalTheory.CxForm.Alt n,
      GlobalTheory.CxForm.delAt (fun w => GlobalTheory.CxForm.pull (fderiv ℂ φ w) γ) v = 0 := by
  intro n φ v hφ γ
  have hD := fun γ S => GlobalTheory.CxForm.differentiableAt_repr_pull_fderiv hφ γ S
  induction γ using ExteriorAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes]; exact delAt_const _ _
  | ι m => exact delAt_pull_fderiv_ι hφ m
  | mul a b ha hb =>
    obtain ⟨y, hy⟩ := FormMul.delAt_mul (hD a) (hD b)
    simp only [map_mul]
    rw [hy, ha, hb, zero_mul, mul_zero, add_zero]
  | add a b ha hb =>
    simp only [map_add]
    rw [delAt_add (hD a) (hD b), ha, hb, add_zero]

end GlobalTheory.CxForm.DelVanish
