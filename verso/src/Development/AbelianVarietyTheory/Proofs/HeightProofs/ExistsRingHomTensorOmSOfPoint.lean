import Mathlib
import Development.AbelianVarietyTheory.Proofs.AlgebraicCurves.AlgebraicIndependentFreeVar

open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `K Ω K' U _ _ _ _ _ D N j₀ x _ _ κ τ T hD hS hT hC hrel`. Use `letI : Algebra K U := (τ.comp (algebraMap K Ω)).toAlgebra`. Establish `hKU : ∀ a : K, algebraMap K U a = τ (algebraMap K Ω a)` using `fun _ => rfl`. Set `φ : Ω →ₐ[K] U` to `{ τ with commutes' := fun _ => rfl }`. Set `g : ReciprocityTheory.ChartRestriction.G.T0.KTp K D N →+* U` to `κ.comp ((algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K').comp (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N)))`.

Establish `hg : Function.Injective g` using `κ.injective.comp ((algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K').injective.comp (IsFractionRing.injective (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N)))`. Establish `hgC : ∀ a : K, g (MvPolynomial.C a) = τ (algebraMap K Ω a)` using `fun a => (hC a).symm`. Establish `hgX : ∀ p, g (MvPolynomial.X p) = κ (T p)` using `fun p => congrArg κ (hT p)`. Establish `hind : AlgebraicIndependent K (fun p => κ (T p))`. Rewrite using `[algebraicIndependent_iff_injective_aeval]`.

Establish `: (MvPolynomial.aeval (fun p => κ (T p)) : ReciprocityTheory.ChartRestriction.G.T0.KTp K D N →ₐ[K] U).toRingHom = g`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Rewrite using `[hgC]`. Simplify using `[hKU]`.

Introduce `p`. Rewrite using `[hgX]`. Simplify using the standard rewrite rules. Establish `h2 : Function.Injective (MvPolynomial.aeval (fun p => κ (T p)) : ReciprocityTheory.ChartRestriction.G.T0.KTp K D N →ₐ[K] U).toRingHom` using `this ▸ hg`. Conclude with `h2`.

Take `⟨P, ⟨hP1, hP2⟩, -⟩` from `GlobalTheory.existsUnique_ringHom_OmS K Ω U D N j₀ x (fun p => κ (T p)) φ hD hind hrel`. Establish `hP1' : ∀ a : Ω, P (algebraMap Ω (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) a) = τ a` using `hP1`. Establish `key : P.comp (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N)) = κ.comp (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K')`. Apply `IsFractionRing.ringHom_ext (A := ReciprocityTheory.ChartRestriction.G.T0.KTp K D N)` to reduce the goal to its premises. Introduce `q`.

Establish `: P.comp (ReciprocityTheory.ChartRestriction.G.T0.sHom (K` using `K) (D := D) j₀ x).toRingHom = g := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Rewrite using `[hgC, ← hP1', ← IsScalarTower.algebraMap_apply]`. Simplify using `[ReciprocityTheory.ChartRestriction.G.T0.sHom]`.

Introduce `p`. Rewrite using `[hgX, ← hP2]`. Simplify using `[ReciprocityTheory.ChartRestriction.G.T0.sHom]`. Rewrite using `[RingHom.comp_apply, hS]`. Conclude with `DFunLike.congr_fun this q`.

Use `letI : Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) U := (κ.comp (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K')).toAlgebra`. Set `κ' : K' →ₐ[ReciprocityTheory.ChartRestriction.G.T0.KTf K D N] U` to `{ κ with commutes' := fun _ => rfl }`. Set `P' : ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N →ₐ[ReciprocityTheory.ChartRestriction.G.T0.KTf K D N] U` to `{ P with commutes' := fun r => DFunLike.congr_fun key r }`. Use `⟨(Algebra.TensorProduct.productMap κ' P').toRingHom, fun a => ?_, fun ω => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.productMap κ' P' (a ⊗ₜ 1) = κ a`.

Rewrite using `[Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.productMap κ' P' (1 ⊗ₜ _) = τ ω`. Rewrite using `[Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]`. Conclude with `hP1' ω`.
-/
theorem exists_ringHom_tensor_OmS_of_point :
    ∀ (K Ω K' U : Type) [Field K] [Field Ω] [Algebra K Ω] [Field K'] [Field U] (D N : ℕ) (j₀ : Fin (N + 1)) (x : Fin N → Ω) [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N)] [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K'] (κ : K' →+* U) (τ : Ω →+* U) (T : ReciprocityTheory.ChartRestriction.G.T0.TVar D N → K'), Algebra.trdeg K Ω = D → (∀ p : ReciprocityTheory.ChartRestriction.G.T0.KTp K D N, algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) p) = ReciprocityTheory.ChartRestriction.G.T0.sHom j₀ x p) → (∀ p, algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K' (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (MvPolynomial.X p)) = T p) → (∀ a : K, τ (algebraMap K Ω a) = κ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K' (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (MvPolynomial.C a)))) → (∀ i : Fin D, κ (T (i.succ, j₀)) + ∑ k, κ (T (i.succ, j₀.succAbove k)) * τ (x k) = 0) → ∃ χ : K' ⊗[ReciprocityTheory.ChartRestriction.G.T0.KTf K D N] ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N →+* U, (∀ a : K', χ (a ⊗ₜ 1) = κ a) ∧ ∀ ω : Ω, χ (1 ⊗ₜ algebraMap Ω (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) ω) = τ ω := by
  intro K Ω K' U _ _ _ _ _ D N j₀ x _ _ κ τ T hD hS hT hC hrel
  classical
  letI : Algebra K U := (τ.comp (algebraMap K Ω)).toAlgebra
  have hKU : ∀ a : K, algebraMap K U a = τ (algebraMap K Ω a) := fun _ => rfl
  let φ : Ω →ₐ[K] U := { τ with commutes' := fun _ => rfl }
  let g : ReciprocityTheory.ChartRestriction.G.T0.KTp K D N →+* U :=
    κ.comp ((algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K').comp
      (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N)))
  have hg : Function.Injective g :=
    κ.injective.comp ((algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K').injective.comp
      (IsFractionRing.injective (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N)))
  have hgC : ∀ a : K, g (MvPolynomial.C a) = τ (algebraMap K Ω a) := fun a => (hC a).symm
  have hgX : ∀ p, g (MvPolynomial.X p) = κ (T p) := fun p => congrArg κ (hT p)
  have hind : AlgebraicIndependent K (fun p => κ (T p)) := by
    rw [algebraicIndependent_iff_injective_aeval]
    have : (MvPolynomial.aeval (fun p => κ (T p)) :
        ReciprocityTheory.ChartRestriction.G.T0.KTp K D N →ₐ[K] U).toRingHom = g := by
      apply MvPolynomial.ringHom_ext
      · intro a
        rw [hgC]
        simp [hKU]
      · intro p
        rw [hgX]
        simp
    have h2 : Function.Injective (MvPolynomial.aeval (fun p => κ (T p)) :
        ReciprocityTheory.ChartRestriction.G.T0.KTp K D N →ₐ[K] U).toRingHom := this ▸ hg
    exact h2
  obtain ⟨P, ⟨hP1, hP2⟩, -⟩ :=
    GlobalTheory.existsUnique_ringHom_OmS K Ω U D N j₀ x (fun p => κ (T p)) φ hD hind hrel
  have hP1' : ∀ a : Ω, P (algebraMap Ω (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) a) = τ a := hP1
  have key : P.comp (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N)) =
      κ.comp (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K') := by
    apply IsFractionRing.ringHom_ext (A := ReciprocityTheory.ChartRestriction.G.T0.KTp K D N)
    intro q
    have : P.comp (ReciprocityTheory.ChartRestriction.G.T0.sHom (K := K) (D := D) j₀ x).toRingHom = g := by
      apply MvPolynomial.ringHom_ext
      · intro a
        rw [hgC, ← hP1', ← IsScalarTower.algebraMap_apply]
        simp [ReciprocityTheory.ChartRestriction.G.T0.sHom]
      · intro p
        rw [hgX, ← hP2]
        simp [ReciprocityTheory.ChartRestriction.G.T0.sHom]
    rw [RingHom.comp_apply, hS]
    exact DFunLike.congr_fun this q
  letI : Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) U :=
    (κ.comp (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K')).toAlgebra
  let κ' : K' →ₐ[ReciprocityTheory.ChartRestriction.G.T0.KTf K D N] U := { κ with commutes' := fun _ => rfl }
  let P' : ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N →ₐ[ReciprocityTheory.ChartRestriction.G.T0.KTf K D N] U :=
    { P with commutes' := fun r => DFunLike.congr_fun key r }
  refine ⟨(Algebra.TensorProduct.productMap κ' P').toRingHom, fun a => ?_, fun ω => ?_⟩
  · change Algebra.TensorProduct.productMap κ' P' (a ⊗ₜ 1) = κ a
    rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
    rfl
  · change Algebra.TensorProduct.productMap κ' P' (1 ⊗ₜ _) = τ ω
    rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
    exact hP1' ω

end GlobalTheory
