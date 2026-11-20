import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

/- English proof (translation)
Introduce `F E _ _ _ _ _ c h2 hc _ _`. Take `⟨-, -, ⟨δ, -, hδ⟩, -⟩` from `hT F E c h2 hc`. Establish `: ContinuousAdd (AE F E)` using `IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AE F E)`. Set `φ : FiniteAdeleRing (𝓞 F) F × FiniteAdeleRing (𝓞 F) F → AE F E` to `fun p => p.1 • (1 : AE F E) + p.2 • inclA F E δ`. Establish `hφc : Continuous φ` using `by unfold φ; fun_prop`.

Establish `hφs : Function.Surjective φ` using `fun a => by`. Take `⟨p, hp, -⟩` from `hδ a`. Conclude with `⟨p, hp.symm⟩`. Establish `hK : DenseRange (algebraMap F (FiniteAdeleRing (𝓞 F) F))` using `denseRange_finiteAdele (R := 𝓞 F) (K := F)`. Establish `hD : DenseRange (φ ∘ Prod.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) (algebraMap F (FiniteAdeleRing (𝓞 F) F)))` using `hφs.denseRange.comp (hK.prodMap hK) hφc`.

Use `hD.mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨x, y⟩, rfl⟩`. Use `⟨algebraMap F E x + algebraMap F E y * δ, ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Prod.map_apply, φ, algebraMap_smul, map_add, map_mul]`. Establish `hinc : ∀ z : F, inclA F E (algebraMap F E z) = z • (1 : AE F E)` using `fun z => by`.

Rewrite using `[← Algebra.algebraMap_eq_smul_one]`. Conclude with `(Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E).commutes z`. Rewrite using `[hinc, hinc, smul_one_mul]`.
-/
theorem EDenseInAE.proof (hT : AETopologicalRing.Statement) : EDenseInAE.Statement := by
  intro F E _ _ _ _ _ c h2 hc _ _
  obtain ⟨-, -, ⟨δ, -, hδ⟩, -⟩ := hT F E c h2 hc
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AE F E)
  let φ : FiniteAdeleRing (𝓞 F) F × FiniteAdeleRing (𝓞 F) F → AE F E :=
    fun p => p.1 • (1 : AE F E) + p.2 • inclA F E δ
  have hφc : Continuous φ :=
    by unfold φ; fun_prop
  have hφs : Function.Surjective φ := fun a => by
    obtain ⟨p, hp, -⟩ := hδ a
    exact ⟨p, hp.symm⟩
  have hK : DenseRange (algebraMap F (FiniteAdeleRing (𝓞 F) F)) :=
    denseRange_finiteAdele (R := 𝓞 F) (K := F)
  have hD : DenseRange (φ ∘ Prod.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))
      (algebraMap F (FiniteAdeleRing (𝓞 F) F))) :=
    hφs.denseRange.comp (hK.prodMap hK) hφc
  refine hD.mono ?_
  rintro _ ⟨⟨x, y⟩, rfl⟩
  refine ⟨algebraMap F E x + algebraMap F E y * δ, ?_⟩
  simp only [Function.comp_apply, Prod.map_apply, φ, algebraMap_smul, map_add, map_mul]
  have hinc : ∀ z : F, inclA F E (algebraMap F E z) = z • (1 : AE F E) := fun z => by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E).commutes z
  rw [hinc, hinc, smul_one_mul]

end StrongApprox

end GroundTheory.Heights₂.Heights
