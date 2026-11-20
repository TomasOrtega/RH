import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.UnitTest

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Distinguish the cases in `hx : x ∈ W`. Use `filter_upwards [hW.isOpen.mem_nhds hx] with y hy`. Simplify using `[Set.indicator_of_mem hy, Set.indicator_of_mem hx]`.

Use `filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy`. Simplify using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]`.
-/
theorem isLocallyConstant_indicator_one {Z : Type} [TopologicalSpace Z] {W : Set Z} (hW : IsClopen W) :
    IsLocallyConstant (W.indicator (1 : Z → ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ W
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

/- English proof (translation)
Use `haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F`. Use `set B : Set F := Metric.closedBall 0 1 with hB`. Establish `hBo : IsOpen B` using `IsUltrametricDist.isOpen_closedBall _ one_ne_zero`. Establish `hBc : IsClosed B` using `Metric.isClosed_closedBall`. Establish `hBk : IsCompact B` using `isCompact_closedBall 0 1`.

Use `set A : Set (Matrix (Fin r) (Fin r) F) := Set.univ.pi fun _ => Set.univ.pi fun _ => B with hA`. Use `set V : Set (Fin r → F) := Set.univ.pi fun _ => B with hV`. Establish `hVo : IsOpen V` using `isOpen_set_pi Set.finite_univ fun _ _ => hBo`. Establish `hVc : IsClosed V` using `isClosed_set_pi fun _ _ => hBc`. Establish `hVk : IsCompact V` using `isCompact_univ_pi fun _ => hBk`.

Establish `hAo : IsOpen A` using `isOpen_set_pi Set.finite_univ fun _ _ => hVo`. Establish `hAc : IsClosed A` using `isClosed_set_pi fun _ _ => hVc`. Establish `hAk : IsCompact A` using `isCompact_univ_pi (X := fun _ : Fin r => Fin r → F) fun _ => hVk`. Use `set S : Set (Gl r F) := A ×ˢ (V ×ˢ (V ×ˢ B)) with hS`. Establish `hSeq : {Y : Gl r F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1} = S`.

Use extensionality with `Y`. Rewrite using `[Set.mem_setOf_eq, hS, hA, hV, hB]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3, h4⟩`. Use `⟨fun i _ j _ => ?_, fun i _ => ?_, fun i _ => ?_, ?_⟩` and prove the remaining obligations.

Simplify `h1 i j` using `only [Metric.mem_closedBall, dist_zero_right]`. Simplify `h2 i` using `only [Metric.mem_closedBall, dist_zero_right]`. Simplify `h3 i` using `only [Metric.mem_closedBall, dist_zero_right]`. Simplify `h4` using `only [Metric.mem_closedBall, dist_zero_right]`. Introduce and unpack `⟨h1, h2, h3, h4⟩`.

Use `⟨fun i j => ?_, fun i => ?_, fun i => ?_, ?_⟩` and prove the remaining obligations. Simplify `h1 i trivial j trivial` using `only [Metric.mem_closedBall, dist_zero_right]`. Simplify `h2 i trivial` using `only [Metric.mem_closedBall, dist_zero_right]`. Simplify `h3 i trivial` using `only [Metric.mem_closedBall, dist_zero_right]`. Simplify `h4` using `only [Metric.mem_closedBall, dist_zero_right]`.

Establish `hSo : IsOpen S` using `hAo.prod (hVo.prod (hVo.prod hBo))`. Establish `hSc : IsClosed S` using `hAc.prod (hVc.prod (hVc.prod hBc))`. Establish `hSk : IsCompact S` using `hAk.prod (hVk.prod (hVk.prod hBk))`. Unfold `unitG`. Rewrite using `[hSeq]`.

Conclude with `⟨isLocallyConstant_indicator_one ⟨hSc, hSo⟩, HasCompactSupport.intro' hSk hSc fun x hx => Set.indicator_of_notMem hx _⟩`.
-/
theorem unitG_isTest (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
    (r : ℕ) : IsTest (unitG r F) := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  set B : Set F := Metric.closedBall 0 1 with hB
  have hBo : IsOpen B := IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hBc : IsClosed B := Metric.isClosed_closedBall
  have hBk : IsCompact B := isCompact_closedBall 0 1
  set A : Set (Matrix (Fin r) (Fin r) F) := Set.univ.pi fun _ => Set.univ.pi fun _ => B with hA
  set V : Set (Fin r → F) := Set.univ.pi fun _ => B with hV
  have hVo : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => hBo
  have hVc : IsClosed V := isClosed_set_pi fun _ _ => hBc
  have hVk : IsCompact V := isCompact_univ_pi fun _ => hBk
  have hAo : IsOpen A := isOpen_set_pi Set.finite_univ fun _ _ => hVo
  have hAc : IsClosed A := isClosed_set_pi fun _ _ => hVc
  have hAk : IsCompact A := isCompact_univ_pi (X := fun _ : Fin r => Fin r → F) fun _ => hVk
  set S : Set (Gl r F) := A ×ˢ (V ×ˢ (V ×ˢ B)) with hS
  have hSeq : {Y : Gl r F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1}
      = S := by
    ext Y
    rw [Set.mem_setOf_eq, hS, hA, hV, hB]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun i _ j _ => ?_, fun i _ => ?_, fun i _ => ?_, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h1 i j
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h2 i
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h3 i
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h4
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun i j => ?_, fun i => ?_, fun i => ?_, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h1 i trivial j trivial
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h2 i trivial
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h3 i trivial
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h4
  have hSo : IsOpen S := hAo.prod (hVo.prod (hVo.prod hBo))
  have hSc : IsClosed S := hAc.prod (hVc.prod (hVc.prod hBc))
  have hSk : IsCompact S := hAk.prod (hVk.prod (hVk.prod hBk))
  unfold unitG
  rw [hSeq]
  exact ⟨isLocallyConstant_indicator_one ⟨hSc, hSo⟩,
    HasCompactSupport.intro' hSk hSc fun x hx => Set.indicator_of_notMem hx _⟩

end GlobalTheory.JR.UnitTest
