import Mathlib

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial

/- English proof (translation)
Use `letI := ι.toAlgebra`. Establish `hs : LinearIndepOn k id (Set.range f)` using `(linearIndepOn_id_range_iff hf.injective).2 hf`. Set `b` to `Module.Basis.extend hs`. Set `B` to `(Algebra.TensorProduct.basis L b).map (MvPolynomial.algebraTensorAlgEquiv k L).toLinearEquiv`. Establish `hB : ∀ x, B x = MvPolynomial.map ι (x : MvPolynomial σ k)`.

Introduce `x`. Simplify using `only [B, b, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, Module.Basis.coe_extend, AlgEquiv.toLinearEquiv_apply, MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]`. Both sides reduce to the same expression. Establish `hsub : Set.range f ⊆ hs.extend (Set.subset_univ _)` using `hs.subset_extend _`. Establish `hinj : Function.Injective (fun i => (⟨f i, hsub (Set.mem_range_self i)⟩ : hs.extend (Set.subset_univ _)))`.

Introduce `i j hij`. Conclude with `hf.injective (congrArg Subtype.val hij)`. Use `B.linearIndependent.comp _ hinj` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first`.

Consider the case `rfl`. Consider the case `(funext i; simp only [Function.comp_apply, hB])`.
-/
theorem li_map {k L : Type*} [Field k] [Field L] (ι : k →+* L) {σ κ : Type*} (f : κ → MvPolynomial σ k)
    (hf : LinearIndependent k f) : LinearIndependent L (fun i => MvPolynomial.map ι (f i)) := by
  classical
  letI := ι.toAlgebra
  have hs : LinearIndepOn k id (Set.range f) := (linearIndepOn_id_range_iff hf.injective).2 hf
  let b := Module.Basis.extend hs
  let B := (Algebra.TensorProduct.basis L b).map
    (MvPolynomial.algebraTensorAlgEquiv k L).toLinearEquiv
  have hB : ∀ x, B x = MvPolynomial.map ι (x : MvPolynomial σ k) := by
    intro x
    simp only [B, b, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
      Module.Basis.coe_extend, AlgEquiv.toLinearEquiv_apply,
      MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
    rfl
  have hsub : Set.range f ⊆ hs.extend (Set.subset_univ _) := hs.subset_extend _
  have hinj : Function.Injective
      (fun i => (⟨f i, hsub (Set.mem_range_self i)⟩ : hs.extend (Set.subset_univ _))) := by
    intro i j hij
    exact hf.injective (congrArg Subtype.val hij)
  have := B.linearIndependent.comp _ hinj
  convert this using 1
  all_goals first
    | rfl
    | (funext i; simp only [Function.comp_apply, hB])

end Formalism.MainNotions.G.SymmetricFormBlocks
