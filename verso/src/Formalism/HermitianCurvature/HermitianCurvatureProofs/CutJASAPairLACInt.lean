import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RankOneEmbeddings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACProper

open MeasureTheory Topology
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ D φ₀ hφ hφc g hg`. Take `⟨P, hPc, hPm⟩` from `hP k r Wp Wq D (tsupport φ₀) {g} hφc isCompact_singleton (Set.singleton_subset_iff.2 hg)`. Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW` as an intermediate fact. Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN` as an intermediate fact. Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'` as an intermediate fact.

Establish `: IsFiniteMeasureOnCompacts D.μW` using `⟨fun K hK => D.haarW.finite_compact K hK⟩`. Establish `: IsFiniteMeasureOnCompacts D.μN` using `⟨fun K hK => D.haarN.finite_compact K hK⟩`. Establish `: IsFiniteMeasureOnCompacts D.μW'` using `⟨fun K hK => D.haarW'.finite_compact K hK⟩`. Establish `hfin : D.μSS P < ⊤` using `by show ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) P < ⊤`. Conclude with `hPc.measure_lt_top`.

Take `⟨M, hM⟩` from `hφ.bounded_above_of_compact_support hφc`. Establish `hφ' : Continuous (fun x : Mt k r => φ₀ (Matrix.of x))` using `hφ.comp (continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp (continuous_apply i))`. Establish `hmeasφ : Measurable (fun x : Mt k r => φ₀ (Matrix.of x))` using `hφ'.measurable`. Establish `hmeas : Measurable (fun p : B.SS k r => φ₀ (B.sgs p g))`. Establish `h1 : Measurable (fun p : B.SS k r => Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.sgF (p, (g : Mt k r)))` using `Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.sgF_meas.comp (measurable_id.prodMk measurable_const)`.

Conclude with `hmeasφ.comp h1`. Establish `hind : Integrable (P.indicator fun _ : B.SS k r => M) D.μSS` using `(integrable_indicator_iff hPc.isClosed.measurableSet).2 (integrableOn_const hfin.ne)`. Use `hind.mono' hmeas.aestronglyMeasurable ?_` and prove the remaining obligations. Use `filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp`. Distinguish the cases in `hpP : p ∈ P`.

Rewrite using `[Set.indicator_of_mem hpP]`. Conclude with `hM _`. Establish `h0 : φ₀ (B.sgs p g) = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hpP (hPm p hp g rfl (subset_tsupport _ hne))`.

Rewrite using `[h0, norm_zero, Set.indicator_of_notMem hpP]`.
-/
theorem aCInt_of_proper (hP : ACProper) : ACInt := by
  intro k r Wp Wq _ _ _ _ D φ₀ hφ hφc g hg
  obtain ⟨P, hPc, hPm⟩ := hP k r Wp Wq D (tsupport φ₀) {g} hφc isCompact_singleton
    (Set.singleton_subset_iff.2 hg)
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have : IsFiniteMeasureOnCompacts D.μW := ⟨fun K hK => D.haarW.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun K hK => D.haarN.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts D.μW' := ⟨fun K hK => D.haarW'.finite_compact K hK⟩
  have hfin : D.μSS P < ⊤ := by
    show ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) P < ⊤
    exact hPc.measure_lt_top
  obtain ⟨M, hM⟩ := hφ.bounded_above_of_compact_support hφc
  have hφ' : Continuous (fun x : Mt k r => φ₀ (Matrix.of x)) :=
    hφ.comp (continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp (continuous_apply i))
  have hmeasφ : Measurable (fun x : Mt k r => φ₀ (Matrix.of x)) := hφ'.measurable
  have hmeas : Measurable (fun p : B.SS k r => φ₀ (B.sgs p g)) := by
    have h1 : Measurable (fun p : B.SS k r => Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.sgF (p, (g : Mt k r))) :=
      Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.sgF_meas.comp (measurable_id.prodMk measurable_const)
    exact hmeasφ.comp h1
  have hind : Integrable (P.indicator fun _ : B.SS k r => M) D.μSS :=
    (integrable_indicator_iff hPc.isClosed.measurableSet).2 (integrableOn_const hfin.ne)
  refine hind.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
  by_cases hpP : p ∈ P
  · rw [Set.indicator_of_mem hpP]; exact hM _
  · have h0 : φ₀ (B.sgs p g) = 0 := by
      by_contra hne
      exact hpP (hPm p hp g rfl (subset_tsupport _ hne))
    rw [h0, norm_zero, Set.indicator_of_notMem hpP]

/- English proof (translation)
The claim follows from `aCInt_of_proper averaging_properness_holds`.
-/
theorem averaging_integrability_holds : ACInt := aCInt_of_proper averaging_properness_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
