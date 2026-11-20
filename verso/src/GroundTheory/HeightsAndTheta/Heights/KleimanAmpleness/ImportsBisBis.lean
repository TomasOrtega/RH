import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraBis
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideTer
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

/- English proof (translation)
Introduce `F _ K _ _ ι _ _ Ω _ _ y k₀ N e hM γ J`. Use `⟨fun I hne hI => Submodule.span_le.mpr (hSub F K ι Ω y k₀ N e γ J I hne hI), ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs hd choose c₀ hc₀ using hM.1`. Set `cell : (∀ k, ι k) → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0` to `fun c => ⟨fun k => {c k}, fun _ => Finset.singleton_nonempty _, by simp⟩`. Establish `hmeet : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → CellMeets y (cell c).1`.

Introduce `c hc k i hi`. Rewrite using `[Finset.mem_singleton.mp hi]`. Conclude with `hc k`. Use `⟨s (cell c₀), Submodule.subset_span (hGlue F K ι Ω y k₀ N e γ J _ fun c hc => ?_), fun c hc => hZ F K ι Ω y s hd c (cell c₀) hc (hmeet c₀ hc₀)⟩` and prove the remaining obligations. Rewrite using `[← hZ F K ι Ω y s hd (cell c) (cell c₀) (hmeet c hc) (hmeet c₀ hc₀)]`.

Conclude with `hs (cell c) (Set.mem_univ _)`. Take `⟨m, f, u, hf, hu, hsum, hloc⟩` from `hCov F K ι Ω y k₀ N e hM γ J`. Use `hL F K ι Ω y _ (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J).toSubring m f u hf hu hsum (fun I r hr a ha => hAct F K ι Ω y k₀ N e γ J I r a hr ha) fun l => ?_` and prove the remaining obligations. Take `⟨c, hc, h0, hmono, hinv⟩` from `hloc l`. Conclude with `hC F K ι Ω y _ c hc h0 hmono hinv`.
-/
theorem ModelRowExact.proof (hSub : RowSub.Statement) (hZ : CellZeroConst.Statement)
    (hGlue : RowSecGlue.Statement) (hC : CellContract.Statement) (hL : CellLocGlue.Statement)
    (hAct : RowChartAct.Statement) (hCov : RowLocCover.Statement) : ModelRowExact.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ N e hM γ J
  refine ⟨fun I hne hI => Submodule.span_le.mpr (hSub F K ι Ω y k₀ N e γ J I hne hI), ?_, ?_⟩
  · intro s hs hd
    choose c₀ hc₀ using hM.1

    let cell : (∀ k, ι k) → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 := fun c =>
      ⟨fun k => {c k}, fun _ => Finset.singleton_nonempty _, by simp⟩
    have hmeet : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → CellMeets y (cell c).1 := by
      intro c hc k i hi
      rw [Finset.mem_singleton.mp hi]
      exact hc k
    refine ⟨s (cell c₀), Submodule.subset_span (hGlue F K ι Ω y k₀ N e γ J _ fun c hc => ?_),
      fun c hc => hZ F K ι Ω y s hd c (cell c₀) hc (hmeet c₀ hc₀)⟩
    rw [← hZ F K ι Ω y s hd (cell c) (cell c₀) (hmeet c hc) (hmeet c₀ hc₀)]
    exact hs (cell c) (Set.mem_univ _)
  · obtain ⟨m, f, u, hf, hu, hsum, hloc⟩ := hCov F K ι Ω y k₀ N e hM γ J
    refine hL F K ι Ω y _ (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J).toSubring m f u hf hu hsum
      (fun I r hr a ha => hAct F K ι Ω y k₀ N e γ J I r a hr ha) fun l => ?_
    obtain ⟨c, hc, h0, hmono, hinv⟩ := hloc l
    exact hC F K ι Ω y _ c hc h0 hmono hinv

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
