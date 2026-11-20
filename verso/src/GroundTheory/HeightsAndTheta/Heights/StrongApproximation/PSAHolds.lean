import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

/- English proof (translation)
Introduce `F E _ _ _ _ _ c hrk hc N J hJ hdet hiso _ _ x hx`. Establish `: ContinuousAdd (AE F E)` using `IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AE F E)`. Take `⟨hN1, hN2⟩` from `hNb F E c hrk hc`. Express the relevant statement in the definitionally equal form `x ∈ Cl c J`. Rewrite using `[Cl, ← closure_closure, mem_closure_iff_nhds]`.

Introduce `U hU`. Establish `hU' : (fun M => x + M) ⁻¹' U ∈ 𝓝 (0 : Matrix (Fin N) (Fin N) (AE F E))`. Establish `hcont : Continuous (fun M : Matrix (Fin N) (Fin N) (AE F E) => x + M)` using `continuous_const.add continuous_id`. Apply `hcont.continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Simplify using `using hU`.

Take `⟨S₀, hS₀⟩` from `hN1 N _ hU'`. Use `choose T hT using fun p : Fin N × Fin N => hN2 (x p.1 p.2)`. Use `set S : Finset (HeightOneSpectrum (𝓞 F)) := S₀ ∪ Finset.univ.biUnion T with hSdef`. Take `⟨t1, t2, -, t4⟩` from `hTr F E c hrk hc N J hJ hdet hiso S x`. Use `⟨trunc E S x, ?_, t4 hx⟩` and prove the remaining obligations.

Establish `hmem : x + (trunc E S x - x) ∈ U`. Apply `hS₀` to reduce the goal to its premises. Introduce `i j`. Establish `hS : ∀ v ∈ S, compAt E v ((trunc E S x - x) i j) = 0`. Introduce `v hv`.

Establish `h` using `congrFun (congrFun (t1 v hv) i) j`. Simplify using `only [Matrix.map_apply] at h`. Rewrite using `[Matrix.sub_apply, map_sub, h, sub_self]`. Use `⟨fun v hv => hS v (Finset.mem_union_left _ hv), fun v hv => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hvS : v ∈ S`.

Rewrite using `[hS v hvS]`. Conclude with `zero_mem _`. Establish `h` using `congrFun (congrFun (t2 v hvS) i) j`. Simplify using `only [Matrix.map_apply] at h`. Establish `hvT : v ∉ T (i, j)` using `fun h' => hvS (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, h'⟩))`.

Establish `hx' : compAt E v (x i j) ∈ intAt E v` using `hT (i, j) v hvT`. Rewrite using `[Matrix.sub_apply, map_sub, h]`. Use `sub_mem ?_ hx'` and prove the remaining obligations. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`.

Conclude with `AddSubgroup.subset_closure ⟨1, one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩`. Conclude with `zero_mem _`. Simplify using `using hmem`.
-/
theorem SAHolds.of_neighbourhoods_truncation (hNb : AENeighbourhoods.Statement)
    (hTr : Truncation.Statement) : SAHolds.Statement := by
  classical
  intro F E _ _ _ _ _ c hrk hc N J hJ hdet hiso _ _ x hx
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AE F E)
  obtain ⟨hN1, hN2⟩ := hNb F E c hrk hc
  change x ∈ Cl c J
  rw [Cl, ← closure_closure, mem_closure_iff_nhds]
  intro U hU
  have hU' : (fun M => x + M) ⁻¹' U ∈ 𝓝 (0 : Matrix (Fin N) (Fin N) (AE F E)) := by
    have hcont : Continuous (fun M : Matrix (Fin N) (Fin N) (AE F E) => x + M) :=
      continuous_const.add continuous_id
    apply hcont.continuousAt.preimage_mem_nhds
    simpa using hU
  obtain ⟨S₀, hS₀⟩ := hN1 N _ hU'
  choose T hT using fun p : Fin N × Fin N => hN2 (x p.1 p.2)
  set S : Finset (HeightOneSpectrum (𝓞 F)) := S₀ ∪ Finset.univ.biUnion T with hSdef
  obtain ⟨t1, t2, -, t4⟩ := hTr F E c hrk hc N J hJ hdet hiso S x
  refine ⟨trunc E S x, ?_, t4 hx⟩
  have hmem : x + (trunc E S x - x) ∈ U := by
    apply hS₀
    intro i j
    have hS : ∀ v ∈ S, compAt E v ((trunc E S x - x) i j) = 0 := by
      intro v hv
      have h := congrFun (congrFun (t1 v hv) i) j
      simp only [Matrix.map_apply] at h
      rw [Matrix.sub_apply, map_sub, h, sub_self]
    refine ⟨fun v hv => hS v (Finset.mem_union_left _ hv), fun v hv => ?_⟩
    by_cases hvS : v ∈ S
    · rw [hS v hvS]; exact zero_mem _
    · have h := congrFun (congrFun (t2 v hvS) i) j
      simp only [Matrix.map_apply] at h
      have hvT : v ∉ T (i, j) := fun h' =>
        hvS (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, h'⟩))
      have hx' : compAt E v (x i j) ∈ intAt E v := hT (i, j) v hvT
      rw [Matrix.sub_apply, map_sub, h]
      refine sub_mem ?_ hx'
      rw [Matrix.one_apply]
      split_ifs
      · exact AddSubgroup.subset_closure
          ⟨1, one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩
      · exact zero_mem _
  simpa using hmem

/- English proof (translation)
The claim follows from `SAHolds.of_neighbourhoods_truncation hNb hTr`.
-/
theorem SAHolds.proof (_hHyp : HypPairExists.Statement) (hNb : AENeighbourhoods.Statement)
    (hTr : Truncation.Statement) : SAHolds.Statement :=
  SAHolds.of_neighbourhoods_truncation hNb hTr

end StrongApprox

end GroundTheory.Heights₂.Heights
