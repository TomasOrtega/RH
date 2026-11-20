import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.LongestElementTranspose

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

section

variable {n : ℕ}

/- English proof (translation)
Use `letI : Invertible U.val := U.invertible`. Rewrite using `[Matrix.coe_units_inv]`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hU`.
-/
theorem upper_inv (U : GL (Fin n) ℂ) (hU : U.val.BlockTriangular id) : (U⁻¹).val.BlockTriangular id := by
  letI : Invertible U.val := U.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hU

/- English proof (translation)
Establish `h1` using `upper_inv U hU`. Establish `key : ((U⁻¹).val * U.val) i i = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]`. Rewrite `key` using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Conclude with `key`.

Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[h1 (show id k < id i from h), zero_mul]`. Rewrite using `[hU (show id i < id k from h), mul_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem inv_diag (U : GL (Fin n) ℂ) (hU : U.val.BlockTriangular id) (i : Fin n) :
    (U⁻¹).val i i * U.val i i = 1 := by
  have h1 := upper_inv U hU
  have key : ((U⁻¹).val * U.val) i i = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at key
  · exact key
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [h1 (show id k < id i from h), zero_mul]
    · rw [hU (show id i < id k from h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

def swapB (U : GL (Fin n) ℂ) : GL (Fin n) ℂ :=
  ⟨((U⁻¹).val)ᵀ.submatrix Fin.rev Fin.rev, (U.val)ᵀ.submatrix Fin.rev Fin.rev,
    by
      rw [show ((U⁻¹).val)ᵀ.submatrix Fin.rev Fin.rev * (U.val)ᵀ.submatrix Fin.rev Fin.rev =
        (((U⁻¹).val)ᵀ * (U.val)ᵀ).submatrix Fin.rev Fin.rev from
          Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm _]
      rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
      exact Matrix.submatrix_one_equiv Fin.revPerm,
    by
      rw [show (U.val)ᵀ.submatrix Fin.rev Fin.rev * ((U⁻¹).val)ᵀ.submatrix Fin.rev Fin.rev =
        ((U.val)ᵀ * ((U⁻¹).val)ᵀ).submatrix Fin.rev Fin.rev from
          Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm _]
      rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]
      exact Matrix.submatrix_one_equiv Fin.revPerm⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem swapB_val (U : GL (Fin n) ℂ) (i j : Fin n) : (swapB U).val i j = (U⁻¹).val (Fin.rev j) (Fin.rev i) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem swapB_inv_val (U : GL (Fin n) ℂ) (i j : Fin n) : ((swapB U)⁻¹).val i j = U.val (Fin.rev j) (Fin.rev i) := rfl

/- English proof (translation)
Introduce `i j hij`. Rewrite using `[swapB_val]`. Apply `upper_inv U hU` to reduce the goal to its premises. Conclude with `Fin.rev_lt_rev.mpr hij`.
-/
theorem swapB_upper (U : GL (Fin n) ℂ) (hU : U.val.BlockTriangular id) : (swapB U).val.BlockTriangular id := by
  intro i j hij
  rw [swapB_val]
  apply upper_inv U hU
  exact Fin.rev_lt_rev.mpr hij

/- English proof (translation)
Establish `hd : ∀ i, (swapB U).val i i = (U.val (Fin.rev i) (Fin.rev i))⁻¹`. Introduce `i`. Rewrite using `[swapB_val]`. Conclude with `eq_inv_of_mul_eq_one_left (inv_diag U hU (Fin.rev i))`. Simplify using `only [hd, _root_.inv_zpow']`.

Conclude with `Fintype.prod_equiv Fin.revPerm _ _ (fun i => by simp)`.
-/
theorem swapB_prod (U : GL (Fin n) ℂ) (hU : U.val.BlockTriangular id) (lam' : Fin n → ℤ) :
    ∏ i, (swapB U).val i i ^ lam' i = ∏ i, U.val i i ^ (-lam' (Fin.rev i)) := by
  have hd : ∀ i, (swapB U).val i i = (U.val (Fin.rev i) (Fin.rev i))⁻¹ := by
    intro i
    rw [swapB_val]
    exact eq_inv_of_mul_eq_one_left (inv_diag U hU (Fin.rev i))
  simp only [hd, _root_.inv_zpow']
  exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => by simp)

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

def ren : (L →+* ℂ) × Fin n × Fin n → (L →+* ℂ) × Fin n × Fin n := fun p => (p.1, Fin.rev p.2.1, Fin.rev p.2.2)

/- English proof (translation)
Establish `hne : ComplexEmbedding.conjugate τ ≠ τ` using `fun h => (InfinitePlace.isComplex_mk_iff.mp (IsTotallyComplex.isComplex (InfinitePlace.mk τ))) (ComplexEmbedding.isReal_iff.mpr h)`. Establish `hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ` using `star_star τ`. Use function extensionality and compare the values at `p`. Take `⟨σ, i, j⟩` from `p`. Simplify using `only [evPt, ren, Function.comp_apply, swapB_val, swapB_inv_val, hcc, Fin.rev_inj]`.

Establish `hne' : ¬ τ = ComplexEmbedding.conjugate τ` using `fun h => hne h.symm`. Apply the tactic sequence `split_ifs <;> first | rfl | (simp_all <;> rfl)`.
-/
theorem evPt_swap (τ : L →+* ℂ) (U : GL (Fin n) ℂ) :
    evPt τ U ∘ ren = evPt (ComplexEmbedding.conjugate τ) (swapB U) := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    (InfinitePlace.isComplex_mk_iff.mp (IsTotallyComplex.isComplex (InfinitePlace.mk τ)))
      (ComplexEmbedding.isReal_iff.mpr h)
  have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := star_star τ
  funext p
  obtain ⟨σ, i, j⟩ := p
  simp only [evPt, ren, Function.comp_apply, swapB_val, swapB_inv_val, hcc, Fin.rev_inj]
  have hne' : ¬ τ = ComplexEmbedding.conjugate τ := fun h => hne h.symm
  split_ifs <;> first | rfl | (simp_all <;> rfl)

end

/- English proof (translation)
Introduce `L _ _ _ n a τ lam' h`. Take `⟨ι, hι, hd, b, P, hP, v, hv0, hv⟩` from `h`. Set `w : GQ L n` to `toGQ w0L longest_element_mem`. Set `e : a.W ≃ₗ[ℂ] a.W` to `LinearEquiv.ofLinear (a.ρ w) (a.ρ w⁻¹) (by ext x; rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl) (by ext x; rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl)`. Use `⟨ι, hι, hd, b.map e, fun i j => MvPolynomial.rename ren (P i j), ?_, v, hv0, ?_⟩` and prove the remaining obligations.

Introduce `γ γ₀ hγ`. Set `γ₀' : GL (Fin n) L` to `w0L⁻¹ * γ₀ * w0L`. Establish `hγ' : ((((w⁻¹ * γ * w : GQ L n) : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (γ₀' : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom`. Establish `e1 : (((w⁻¹ * γ * w : GQ L n) : GAf L n) : GL (Fin n) (AL L)) = Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) (w0L⁻¹) * ((γ : GAf L n) : GL (Fin n) (AL L)) * Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL …`. Rewrite using `[map_inv]`.

Both sides reduce to the same expression. Rewrite using `[e1, Units.val_mul, Units.val_mul, hγ]`. Simplify using `only [γ₀', Units.val_mul, Matrix.map_mul]`. Both sides reduce to the same expression. Establish `hq` using `hP _ _ hγ'`.

Use extensionality with `i j`. Establish `hq'` using `congrFun (congrFun hq i) j`. Rewrite `hq'` using `[LinearMap.toMatrix_apply]`. Rewrite using `[LinearMap.toMatrix_apply, Module.Basis.map_apply, Module.Basis.map_repr, LinearEquiv.trans_apply]`. Establish `e2 : e.symm (a.ρ γ (e (b j))) = a.ρ (w⁻¹ * γ * w) (b j)`.

Rewrite using `[map_mul, map_mul]`. Both sides reduce to the same expression. Rewrite using `[e2, hq', MvPolynomial.eval_rename]`. Use `congrArg (fun f => MvPolynomial.eval f (P i j)) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `p`.

Simplify using `only [Function.comp, ren, γ₀', Units.val_mul]`. Establish `e3 : ((w0L⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = W0 L n` using `rfl`. Establish `e4 : ((w0L : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = W0 L n` using `rfl`. Rewrite using `[e3, e4, longest_element_conj]`. Both sides reduce to the same expression.

Introduce `U hU`. Establish `hB` using `hv (swapB U) (swapB_upper U hU)`. Rewrite `hB` using `[swapB_prod U hU]`. Rewrite using `[← hB]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, MvPolynomial.eval_rename, evPt_swap]`.
-/
theorem conjugation_swap : ConjSwap := by
  intro L _ _ _ n a τ lam' h
  obtain ⟨ι, hι, hd, b, P, hP, v, hv0, hv⟩ := h
  let w : GQ L n := toGQ w0L longest_element_mem
  let e : a.W ≃ₗ[ℂ] a.W := LinearEquiv.ofLinear (a.ρ w) (a.ρ w⁻¹)
    (by ext x; rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by ext x; rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl)
  refine ⟨ι, hι, hd, b.map e, fun i j => MvPolynomial.rename ren (P i j), ?_, v, hv0, ?_⟩
  · intro γ γ₀ hγ
    let γ₀' : GL (Fin n) L := w0L⁻¹ * γ₀ * w0L
    have hγ' : ((((w⁻¹ * γ * w : GQ L n) : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀' : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
      have e1 : (((w⁻¹ * γ * w : GQ L n) : GAf L n) : GL (Fin n) (AL L)) =
          Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) (w0L⁻¹) *
            ((γ : GAf L n) : GL (Fin n) (AL L)) *
            Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) w0L := by
        rw [map_inv]; rfl
      rw [e1, Units.val_mul, Units.val_mul, hγ]
      simp only [γ₀', Units.val_mul, Matrix.map_mul]
      rfl
    have hq := hP _ _ hγ'
    ext i j
    have hq' := congrFun (congrFun hq i) j
    rw [LinearMap.toMatrix_apply] at hq'
    rw [LinearMap.toMatrix_apply, Module.Basis.map_apply, Module.Basis.map_repr, LinearEquiv.trans_apply]
    have e2 : e.symm (a.ρ γ (e (b j))) = a.ρ (w⁻¹ * γ * w) (b j) := by
      rw [map_mul, map_mul]; rfl
    rw [e2, hq', MvPolynomial.eval_rename]
    refine congrArg (fun f => MvPolynomial.eval f (P i j)) ?_
    funext p
    simp only [Function.comp, ren, γ₀', Units.val_mul]
    have e3 : ((w0L⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = W0 L n := rfl
    have e4 : ((w0L : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = W0 L n := rfl
    rw [e3, e4, longest_element_conj]
    rfl
  · intro U hU
    have hB := hv (swapB U) (swapB_upper U hU)
    rw [swapB_prod U hU] at hB
    rw [← hB]
    congr 1
    ext i j
    simp only [Matrix.of_apply, MvPolynomial.eval_rename, evPt_swap]

end PI.UnitaryGroupMassFormula.HwConjInf
