import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LevLin
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

/- English proof (translation)
Rewrite using `[← sum_cmp m]`. Simplify using `only [map_sum, LinearMap.rTensor_tmul, TensorProduct.map_tmul]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [h _ (hm i)]`.
-/
private theorem rT_map_on {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (N : Submodule ℂ W) (T A : Module.End ℂ W)
    (B : Module.End ℂ (Fin d → ℂ)) (h : ∀ φ ∈ N, A (T φ) = T (A φ)) (m : W ⊗[ℂ] (Fin d → ℂ)) (hm : ∀ i, cmp i m ∈ N) :
    T.rTensor _ (TensorProduct.map A B m) = TensorProduct.map A B (T.rTensor _ m) := by
  rw [← sum_cmp m]
  simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.map_tmul]
  exact Finset.sum_congr rfl fun i _ => by rw [h _ (hm i)]

/- English proof (translation)
Establish `h1` using `rT_map_on N T (lie E a X) LinearMap.id (hT.lie X) m hm`. Establish `h2` using `rT_map_on N T LinearMap.id (Matrix.toLin' (Ξ.dmat X)) (fun _ _ => rfl) m hm`. Express the relevant statement in the definitionally equal form `TensorProduct.map (lie E a X) LinearMap.id (T.rTensor _ m) + TensorProduct.map LinearMap.id (Matrix.toLin' (Ξ.dmat X)) (T.rTensor _ m) = T.rTensor _ (TensorProduct.map (lie E a X) LinearMap.id m + TensorProduct.map LinearMap.id (Matrix.toLin' (Ξ.dmat X)) m)`. Rewrite using `[map_add, h1, h2]`.
-/
private theorem rT_smLie {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a)
    (N : Submodule ℂ (Sm E a)) (T : Module.End ℂ (Sm E a)) (hT : IsOp N T) (X : Lie E a)
    (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) (hm : ∀ i, cmp i m ∈ N) :
    smLie Ξ X (T.rTensor _ m) = T.rTensor _ (smLie Ξ X m) := by
  have h1 := rT_map_on N T (lie E a X) LinearMap.id (hT.lie X) m hm
  have h2 := rT_map_on N T LinearMap.id (Matrix.toLin' (Ξ.dmat X)) (fun _ _ => rfl) m hm
  change TensorProduct.map (lie E a X) LinearMap.id (T.rTensor _ m) +
      TensorProduct.map LinearMap.id (Matrix.toLin' (Ξ.dmat X)) (T.rTensor _ m) =
    T.rTensor _ (TensorProduct.map (lie E a X) LinearMap.id m + TensorProduct.map LinearMap.id (Matrix.toLin' (Ξ.dmat X)) m)
  rw [map_add, h1, h2]

/- English proof (translation)
Introduce `E _ _ _ a U Ξ r hr N hN T hT q ω hω hv`. Take `⟨-, -, hl, hc⟩` from `levLin E a U Ξ q`. Establish `hone : ∀ X i, ∀ m : ℂ, Ξ.dmat (oneL E a) = m • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) → lie E a (oneL E a) (T (cmp i (ω X))) = -m • T (cmp i (ω X))` using `fun X i m hm => by`. Rewrite using `[hT.lie _ _ (hv X i), (hl ω hω X i).2.2 m hm, map_smul]`. Establish `hsq : ∀ X i, IsSq r (T (cmp i (ω X)))` using `fun X i => hN.sq _ (hT.maps _ (hv X i)) (hone X i _ hr)`.

Use `⟨⟨?_, fun X i h => ?_, fun X => mem_span_of_cmp fun i => ?_⟩, fun X i => ?_, fun X i => ?_, ?_⟩` and prove the remaining obligations. Introduce `k X`. Rewrite using `[app_apply, app_apply, hω.equiv k X]`. Conclude with `rT_map_on N T _ _ (hT.rt _) _ (hv X)`. Rewrite using `[app_apply, hω.basic X i h, map_zero]`.

Rewrite using `[hc]`. Use `⟨(hsq X i).left, fun u hu => ?_, hone X i⟩` and prove the remaining obligations. Conclude with `(hT.rt _ _ (hv X i)).trans (congrArg T ((hl ω hω X i).2.1 u hu))`. Rewrite using `[hc]`. Conclude with `hT.maps _ (hv X i)`.

Rewrite using `[hc]`. Conclude with `Submodule.subset_span (hsq X i)`. Use `AlternatingMap.ext fun X => ?_` and prove the remaining obligations. Rewrite using `[app_apply]`. Simplify using `only [dCo, AlternatingMap.alternatizeUncurryFin_apply, map_sum, map_zsmul]`.

Use `Finset.sum_congr rfl fun i _ => congrArg _ ?_` and prove the remaining obligations. Conclude with `rT_smLie Ξ N T hT _ _ (hv _)`.
-/
theorem UpperTheory.V.Cj.H.appFacts :
    UpperTheory.V.Cj.H.AppFacts := by
  intro E _ _ _ a U Ξ r hr N hN T hT q ω hω hv
  obtain ⟨-, -, hl, hc⟩ := levLin E a U Ξ q
  have hone : ∀ X i, ∀ m : ℂ, Ξ.dmat (oneL E a) = m • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) →
      lie E a (oneL E a) (T (cmp i (ω X))) = -m • T (cmp i (ω X)) := fun X i m hm => by
    rw [hT.lie _ _ (hv X i), (hl ω hω X i).2.2 m hm, map_smul]
  have hsq : ∀ X i, IsSq r (T (cmp i (ω X))) := fun X i => hN.sq _ (hT.maps _ (hv X i)) (hone X i _ hr)
  refine ⟨⟨?_, fun X i h => ?_, fun X => mem_span_of_cmp fun i => ?_⟩, fun X i => ?_, fun X i => ?_, ?_⟩
  · intro k X
    rw [app_apply, app_apply, hω.equiv k X]
    exact rT_map_on N T _ _ (hT.rt _) _ (hv X)
  · rw [app_apply, hω.basic X i h, map_zero]
  · rw [hc]
    refine ⟨(hsq X i).left, fun u hu => ?_, hone X i⟩
    exact (hT.rt _ _ (hv X i)).trans (congrArg T ((hl ω hω X i).2.1 u hu))
  · rw [hc]
    exact hT.maps _ (hv X i)
  · rw [hc]
    exact Submodule.subset_span (hsq X i)
  · refine AlternatingMap.ext fun X => ?_
    rw [app_apply]
    simp only [dCo, AlternatingMap.alternatizeUncurryFin_apply, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
    exact rT_smLie Ξ N T hT _ _ (hv _)
