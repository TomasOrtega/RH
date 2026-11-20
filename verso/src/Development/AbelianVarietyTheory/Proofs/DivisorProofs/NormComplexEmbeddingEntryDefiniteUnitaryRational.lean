import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SuppFin

/- English proof (translation)
Establish `h : (γ.1.val.map (IsCMField.complexConj E).toRingEquiv.toRingHom)ᵀ * 1 * γ.1.val = 1` using `γ.2`. Establish `hjj` using `congrFun (congrFun h j) j`. Simplify using `only [Matrix.mul_one, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply_eq] at hjj`. Establish `h2 : ∑ k, ((‖τ (γ.1.val k j)‖ ^ 2 : ℝ) : ℂ) = 1`. Use `congrArg τ hjj` as an intermediate fact.

Rewrite `this` using `[map_sum, map_one]`. Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Express the relevant statement in the definitionally equal form `_ = τ ((IsCMField.complexConj E) (γ.1.val k j)) * _`.

Rewrite using `[IsCMField.complexEmbedding_complexConj, Complex.conj_mul']`. Use `push_cast`. Both sides reduce to the same expression. Establish `h3 : ∑ k, ‖τ (γ.1.val k j)‖ ^ 2 = 1` using `by exact_mod_cast h2`. Establish `h4 : ‖τ (γ.1.val i j)‖ ^ 2 ≤ 1`.

Rewrite using `[← h3]`. Conclude with `Finset.single_le_sum (f := fun k => ‖τ (γ.1.val k j)‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)`. Use polynomial arithmetic with `[norm_nonneg (τ (γ.1.val i j))]`.
-/
theorem norm_emb_entry_le_one (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n)
    (τ : E →+* ℂ) (i j : Fin n) : ‖τ (γ.1.val i j)‖ ≤ 1 := by
  have h : (γ.1.val.map (IsCMField.complexConj E).toRingEquiv.toRingHom)ᵀ * 1 * γ.1.val = 1 := γ.2
  have hjj := congrFun (congrFun h j) j
  simp only [Matrix.mul_one, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.one_apply_eq] at hjj
  have h2 : ∑ k, ((‖τ (γ.1.val k j)‖ ^ 2 : ℝ) : ℂ) = 1 := by
    have := congrArg τ hjj
    rw [map_sum, map_one] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    change _ = τ ((IsCMField.complexConj E) (γ.1.val k j)) * _
    rw [IsCMField.complexEmbedding_complexConj, Complex.conj_mul']
    push_cast; rfl
  have h3 : ∑ k, ‖τ (γ.1.val k j)‖ ^ 2 = 1 := by exact_mod_cast h2
  have h4 : ‖τ (γ.1.val i j)‖ ^ 2 ≤ 1 := by
    rw [← h3]
    exact Finset.single_le_sum (f := fun k => ‖τ (γ.1.val k j)‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)
  nlinarith [norm_nonneg (τ (γ.1.val i j))]

end GlobalTheory.BCT.SuppFin
