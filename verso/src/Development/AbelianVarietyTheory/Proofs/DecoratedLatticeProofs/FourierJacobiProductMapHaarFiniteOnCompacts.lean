import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdRFJCoe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProperTriple
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricDoubleIntegralFiniteCombination
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarR

/- English proof (translation)
Introduce `k _ _ _ _ _ _ n _ _ c ρ hp hpc ν hν m hm`. Use `haveI := GlobalTheory.SplitWeil.secondCountable k`. Use `haveI := GlobalTheory.SplitWeil.t2Space k`. Use `haveI : BorelSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.borel_GL`. Use `haveI := QuotLinear.finiteOnCompacts_volN (n := n) (c := c) (p := ρ + 1) ν`.

Use `haveI : LocallyCompactSpace (N k n c (ρ + 1)) := (QuotLinear.isClosed_N (k := k) (n := n) (c := c) (p := ρ + 1)).isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology (N k n c (ρ + 1)) := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : IsLocallyFiniteMeasure (volN ν n c (ρ + 1)) := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`. Use `haveI : SigmaFinite (volN ν n c (ρ + 1)) := sigmaFinite_of_locallyFinite`. Use `haveI : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`.

Use `haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite`. Use `set M := (m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν) with hM`. Use `haveI : IsFiniteMeasureOnCompacts M := by rw [hM]; infer_instance`. Use `⟨fun K hK => ?_⟩` and prove the remaining obligations. Take `⟨D, hD, hD'⟩` from `GlobalTheory.RootEx.ProperTriple.proper_triple k n c ρ hp hpc _ (hK.image continuous_subtype_val)`.

Establish `hD2 : IsCompact ((fun w : GL n k × N k n c (ρ + 1) × (n → k) => ((w.1, w.2.1), w.2.2)) '' D)` using `hD.image (by fun_prop)`. Establish `hsub : prodRFJ ρ ⁻¹' K ⊆ (fun w : GL n k × N k n c (ρ + 1) × (n → k) => ((w.1, w.2.1), w.2.2)) '' D`. Introduce `z hz`. Conclude with `⟨(z.1.1, z.1.2, z.2), hD' _ ⟨_, hz, rfl⟩, rfl⟩`. Distinguish the cases in `hf : AEMeasurable (prodRFJ (k := k) (n := n) (c := c) ρ) M`.

Rewrite using `[Measure.map_apply_of_aemeasurable hf hK.isClosed.measurableSet]`. Conclude with `(measure_mono hsub).trans_lt hD2.measure_lt_top`. Rewrite using `[Measure.map_of_not_aemeasurable hf]`. Simplify using the standard rewrite rules.
-/
theorem finite_on_compacts_prodRFJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), 1 ≤ ρ → ρ < c → ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ m : Measure (GL n k), m.IsHaarMeasure → IsFiniteMeasureOnCompacts (((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)).map (prodRFJ ρ)) := by
  intro k _ _ _ _ _ _ n _ _ c ρ hp hpc ν hν m hm
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.borel_GL
  haveI := QuotLinear.finiteOnCompacts_volN (n := n) (c := c) (p := ρ + 1) ν
  haveI : LocallyCompactSpace (N k n c (ρ + 1)) :=
    (QuotLinear.isClosed_N (k := k) (n := n) (c := c) (p := ρ + 1)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (N k n c (ρ + 1)) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : IsLocallyFiniteMeasure (volN ν n c (ρ + 1)) := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite (volN ν n c (ρ + 1)) := sigmaFinite_of_locallyFinite
  haveI : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite
  set M := (m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν) with hM
  haveI : IsFiniteMeasureOnCompacts M := by rw [hM]; infer_instance
  refine ⟨fun K hK => ?_⟩
  obtain ⟨D, hD, hD'⟩ := GlobalTheory.RootEx.ProperTriple.proper_triple k n c ρ hp hpc _ (hK.image continuous_subtype_val)
  have hD2 : IsCompact ((fun w : GL n k × N k n c (ρ + 1) × (n → k) => ((w.1, w.2.1), w.2.2)) '' D) :=
    hD.image (by fun_prop)
  have hsub : prodRFJ ρ ⁻¹' K ⊆ (fun w : GL n k × N k n c (ρ + 1) × (n → k) => ((w.1, w.2.1), w.2.2)) '' D := by
    intro z hz
    exact ⟨(z.1.1, z.1.2, z.2), hD' _ ⟨_, hz, rfl⟩, rfl⟩
  by_cases hf : AEMeasurable (prodRFJ (k := k) (n := n) (c := c) ρ) M
  · rw [Measure.map_apply_of_aemeasurable hf hK.isClosed.measurableSet]
    exact (measure_mono hsub).trans_lt hD2.measure_lt_top
  · rw [Measure.map_of_not_aemeasurable hf]
    simp

end GlobalTheory.HaarR
end
