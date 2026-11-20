import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LatTop

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Distinguish the cases in `hx : x ∈ W`. Use `filter_upwards [hW.isOpen.mem_nhds hx] with y hy`. Simplify using `[Set.indicator_of_mem hy, Set.indicator_of_mem hx]`.

Use `filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy`. Simplify using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]`.
-/
theorem isLocallyConstant_indicator_one' {Z : Type} [TopologicalSpace Z] {W : Set Z} (hW : IsClopen W) :
    IsLocallyConstant (W.indicator (1 : Z → ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ W
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

/- English proof (translation)
Introduce `F E _ _ _ _ hU A r j`. Use `haveI : IsUltrametricDist E := hU.ultraE`. Use `haveI : LocallyCompactSpace F := hU.lcF`. Use `haveI : LocallyCompactSpace E := hU.lcE`. Use `haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F`.

Use `haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)`. Use `haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional`. Use `haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi`. Use `haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L`.

Use `haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L`. Set `jF : A.L ≃ₗ[F] (Fin r → E)` to `j.restrictScalars F`. Establish `hc : Continuous jF` using `IsModuleTopology.continuous_of_linearMap jF.toLinearMap`. Establish `hcs : Continuous jF.symm` using `IsModuleTopology.continuous_of_linearMap jF.symm.toLinearMap`. Use `set B : Set E := Metric.closedBall 0 1 with hB`.

Establish `hBo : IsOpen B` using `IsUltrametricDist.isOpen_closedBall _ one_ne_zero`. Establish `hBc : IsClosed B` using `Metric.isClosed_closedBall`. Establish `hBk : IsCompact B` using `isCompact_closedBall 0 1`. Use `set V : Set (Fin r → E) := Set.univ.pi fun _ => B with hV`. Establish `hVo : IsOpen V` using `isOpen_set_pi Set.finite_univ fun _ _ => hBo`.

Establish `hVc : IsClosed V` using `isClosed_set_pi fun _ _ => hBc`. Establish `hVk : IsCompact V` using `isCompact_univ_pi fun _ => hBk`. Establish `hS : {y : A.L | ∀ i, ‖j y i‖ ≤ 1} = jF ⁻¹' V`. Use extensionality with `y`. Simplify using `[hV, hB, jF]`.

Establish `hS' : jF ⁻¹' V = jF.symm '' V` using `(jF.toEquiv.image_symm_eq_preimage V).symm`. Establish `hSo : IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1}` using `hS ▸ hVo.preimage hc`. Establish `hSc : IsClosed {y : A.L | ∀ i, ‖j y i‖ ≤ 1}` using `hS ▸ hVc.preimage hc`. Establish `hSk : IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1}`. Rewrite using `[hS, hS']`.

Conclude with `hVk.image hcs`. Conclude with `⟨hSo, hSk, isLocallyConstant_indicator_one' ⟨hSc, hSo⟩, HasCompactSupport.intro' hSk hSc fun x hx => Set.indicator_of_notMem hx _⟩`.
-/
theorem lattice_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)),
    IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} ∧ IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} ∧
      IsTest (Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} (1 : A.L → ℂ)) := by
  intro F E _ _ _ _ hU A r j
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  let jF : A.L ≃ₗ[F] (Fin r → E) := j.restrictScalars F
  have hc : Continuous jF := IsModuleTopology.continuous_of_linearMap jF.toLinearMap
  have hcs : Continuous jF.symm := IsModuleTopology.continuous_of_linearMap jF.symm.toLinearMap
  set B : Set E := Metric.closedBall 0 1 with hB
  have hBo : IsOpen B := IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hBc : IsClosed B := Metric.isClosed_closedBall
  have hBk : IsCompact B := isCompact_closedBall 0 1
  set V : Set (Fin r → E) := Set.univ.pi fun _ => B with hV
  have hVo : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => hBo
  have hVc : IsClosed V := isClosed_set_pi fun _ _ => hBc
  have hVk : IsCompact V := isCompact_univ_pi fun _ => hBk
  have hS : {y : A.L | ∀ i, ‖j y i‖ ≤ 1} = jF ⁻¹' V := by
    ext y
    simp [hV, hB, jF]
  have hS' : jF ⁻¹' V = jF.symm '' V := (jF.toEquiv.image_symm_eq_preimage V).symm
  have hSo : IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} := hS ▸ hVo.preimage hc
  have hSc : IsClosed {y : A.L | ∀ i, ‖j y i‖ ≤ 1} := hS ▸ hVc.preimage hc
  have hSk : IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} := by
    rw [hS, hS']; exact hVk.image hcs
  exact ⟨hSo, hSk, isLocallyConstant_indicator_one' ⟨hSc, hSo⟩,
    HasCompactSupport.intro' hSk hSc fun x hx => Set.indicator_of_notMem hx _⟩

end GlobalTheory.JR.LatTop
