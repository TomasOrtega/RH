import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LinDesc

/- English proof (translation)
Introduce `F E _ _ _ _ hU A r τ p hG`. Use `haveI : LocallyCompactSpace F := hU.lcF`. Use `haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F`. Set `e : A.K ≃ₗ[F] (Fin r → F)` to `(bas A hG).equivFun`. Establish `he : Continuous e` using `IsModuleTopology.continuous_of_linearMap e.toLinearMap`.

Establish `he' : Continuous e.symm` using `IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap`. Set `eh : A.K ≃ₜ (Fin r → F)` to `{ e.toEquiv with continuous_toFun := he, continuous_invFun := he' }`. Set `g : (Fin r → F) →ₗ[F] Matrix (Fin r) (Fin r) F` to `(Algebra.leftMulMatrix (bas A hG)).toLinearMap ∘ₗ e.symm.toLinearMap`. Establish `hg : IsClosedEmbedding g`. Use `LinearMap.isClosedEmbedding_of_injective ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.ker_eq_bot]`. Introduce `x y hxy`. Establish `h1` using `Algebra.leftMulMatrix_injective (bas A hG) hxy`. Conclude with `e.symm.injective h1`. Set `f : A.K → Matrix (Fin r) (Fin r) F` to `fun x => Algebra.leftMulMatrix (bas A hG) x`.

Establish `hf : IsClosedEmbedding f`. Establish `: f = g ∘ eh`. Use function extensionality and compare the values at `x`. Simplify using `[f, g, eh, e]`. Rewrite using `[this]`.

Conclude with `hg.comp eh.isClosedEmbedding`. Use `haveI : T2Space A.K := eh.isEmbedding.t2Space`. Establish `hfo : IsClosedEmbedding (fun x : A.Kᵐᵒᵖ => MulOpposite.op (f (MulOpposite.unop x)))` using `MulOpposite.opHomeomorph.isClosedEmbedding.comp (hf.comp MulOpposite.opHomeomorph.symm.isClosedEmbedding)`. Establish `hP : IsClosedEmbedding (Prod.map f (fun x : A.Kᵐᵒᵖ => MulOpposite.op (f (MulOpposite.unop x))))` using `hf.prodMap hfo`. Establish `hK : IsClosedEmbedding (Units.embedProduct A.K)` using `Units.isClosedEmbedding_embedProduct`.

Establish `hM : IsClosedEmbedding (Units.embedProduct (Matrix (Fin r) (Fin r) F))` using `Units.isClosedEmbedding_embedProduct`. Establish `hcomp : (Units.embedProduct (Matrix (Fin r) (Fin r) F)) ∘ (LinDesc.tm A hG) = (Prod.map f (fun x : A.Kᵐᵒᵖ => MulOpposite.op (f (MulOpposite.unop x)))) ∘ Units.embedProduct A.K`. Use function extensionality and compare the values at `t`. Simplify using `only [Function.comp_apply, Units.embedProduct_apply, Prod.map_apply, MulOpposite.unop_op]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Conclude with `tm_coe A hG t`. Simplify using `only`. Rewrite using `[tm_inv_coe]`. Establish `hc : IsClosedEmbedding ((Units.embedProduct (Matrix (Fin r) (Fin r) F)) ∘ (LinDesc.tm A hG))`. Rewrite using `[hcomp]`.

Conclude with `hP.comp hK`. Establish `hcont : Continuous (LinDesc.tm A hG)`. Rewrite using `[hM.isInducing.continuous_iff]`. Conclude with `hc.continuous`. Use `⟨⟨Topology.IsInducing.of_comp hcont hM.continuous hc.isInducing, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `x y hxy`. Conclude with `hc.injective (by simp [Function.comp_apply, hxy])`. Establish `: Set.range (LinDesc.tm A hG) = (Units.embedProduct (Matrix (Fin r) (Fin r) F)) ⁻¹' Set.range ((Units.embedProduct (Matrix (Fin r) (Fin r) F)) ∘ (LinDesc.tm A hG))`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨t, rfl⟩`. Conclude with `⟨t, rfl⟩`. Introduce and unpack `⟨t, ht⟩`. Conclude with `⟨t, hM.injective ht⟩`. Rewrite using `[this]`.

Conclude with `hc.isClosed_range.preimage hM.continuous`.
-/
theorem tm_isClosedEmbedding : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p), Topology.IsClosedEmbedding (LinDesc.tm A hG) := by
  intro F E _ _ _ _ hU A r τ p hG
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let e : A.K ≃ₗ[F] (Fin r → F) := (bas A hG).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he' : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let eh : A.K ≃ₜ (Fin r → F) :=
    { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  let g : (Fin r → F) →ₗ[F] Matrix (Fin r) (Fin r) F :=
    (Algebra.leftMulMatrix (bas A hG)).toLinearMap ∘ₗ e.symm.toLinearMap
  have hg : IsClosedEmbedding g := by
    refine LinearMap.isClosedEmbedding_of_injective ?_
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    have h1 := Algebra.leftMulMatrix_injective (bas A hG) hxy
    exact e.symm.injective h1
  let f : A.K → Matrix (Fin r) (Fin r) F := fun x => Algebra.leftMulMatrix (bas A hG) x
  have hf : IsClosedEmbedding f := by
    have : f = g ∘ eh := by
      funext x; simp [f, g, eh, e]
    rw [this]; exact hg.comp eh.isClosedEmbedding
  haveI : T2Space A.K := eh.isEmbedding.t2Space
  have hfo : IsClosedEmbedding (fun x : A.Kᵐᵒᵖ => MulOpposite.op (f (MulOpposite.unop x))) :=
    MulOpposite.opHomeomorph.isClosedEmbedding.comp (hf.comp MulOpposite.opHomeomorph.symm.isClosedEmbedding)
  have hP : IsClosedEmbedding (Prod.map f (fun x : A.Kᵐᵒᵖ => MulOpposite.op (f (MulOpposite.unop x)))) :=
    hf.prodMap hfo
  have hK : IsClosedEmbedding (Units.embedProduct A.K) := Units.isClosedEmbedding_embedProduct
  have hM : IsClosedEmbedding (Units.embedProduct (Matrix (Fin r) (Fin r) F)) := Units.isClosedEmbedding_embedProduct
  have hcomp : (Units.embedProduct (Matrix (Fin r) (Fin r) F)) ∘ (LinDesc.tm A hG) =
      (Prod.map f (fun x : A.Kᵐᵒᵖ => MulOpposite.op (f (MulOpposite.unop x)))) ∘ Units.embedProduct A.K := by
    funext t
    simp only [Function.comp_apply, Units.embedProduct_apply, Prod.map_apply, MulOpposite.unop_op]
    refine Prod.ext ?_ ?_
    · exact tm_coe A hG t
    · simp only
      rw [tm_inv_coe]
  have hc : IsClosedEmbedding ((Units.embedProduct (Matrix (Fin r) (Fin r) F)) ∘ (LinDesc.tm A hG)) := by
    rw [hcomp]; exact hP.comp hK
  have hcont : Continuous (LinDesc.tm A hG) := by
    rw [hM.isInducing.continuous_iff]; exact hc.continuous
  refine ⟨⟨Topology.IsInducing.of_comp hcont hM.continuous hc.isInducing, ?_⟩, ?_⟩
  · intro x y hxy
    exact hc.injective (by simp [Function.comp_apply, hxy])
  · have : Set.range (LinDesc.tm A hG) = (Units.embedProduct (Matrix (Fin r) (Fin r) F)) ⁻¹' Set.range ((Units.embedProduct (Matrix (Fin r) (Fin r) F)) ∘ (LinDesc.tm A hG)) := by
      ext x; constructor
      · rintro ⟨t, rfl⟩; exact ⟨t, rfl⟩
      · rintro ⟨t, ht⟩; exact ⟨t, hM.injective ht⟩
    rw [this]; exact hc.isClosed_range.preimage hM.continuous

end GlobalTheory.JR.LinDesc
