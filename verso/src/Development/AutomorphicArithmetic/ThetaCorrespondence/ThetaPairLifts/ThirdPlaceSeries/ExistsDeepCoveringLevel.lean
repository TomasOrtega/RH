import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsDeepCoveringLevel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.DeepExist
/- English proof (translation)
Use `Closed.imp (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0) fun Fm CH _ h => ?_` and prove the remaining obligations. Take `⟨C, hC, x0, h⟩` from `h`. Use `⟨C, hC, x0, fun x hx hle ι p hp i hi => ?_⟩` and prove the remaining obligations. Establish `hN` using `h x hx hle ι p hp i`. Take `⟨Y, hY⟩` from `GlobalTheory.T.exists_good_cover_over_sized_field hP.p8 (Fm.D x ι) p.T.toCore p.fw.laws.pins ((i : ℕ) + 1) ⟨by omega, i.isLt⟩ hN.split hN.cop (expL (Fm.L x ι).sc.L)`.

Use `⟨Y, (goodCov_iff p i Y).2 (hY.mono (size_le hN ?_))⟩` and prove the remaining obligations. Conclude with `RecTied.core_size_le p hp.2 (by linarith [hN.big.2.1])`.
-/
theorem exists_deep_covering_level_alt (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) : _root_.GlobalTheory.CovTop.DeepExistence := by
  refine Closed.imp (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0) fun Fm CH _ h => ?_
  obtain ⟨C, hC, x0, h⟩ := h
  refine ⟨C, hC, x0, fun x hx hle ι p hp i hi => ?_⟩
  have hN := h x hx hle ι p hp i
  obtain ⟨Y, hY⟩ := GlobalTheory.T.exists_good_cover_over_sized_field hP.p8 (Fm.D x ι) p.T.toCore p.fw.laws.pins ((i : ℕ) + 1) ⟨by omega, i.isLt⟩ hN.split
    hN.cop (expL (Fm.L x ι).sc.L)
  refine ⟨Y, (goodCov_iff p i Y).2 (hY.mono (size_le hN ?_))⟩
  exact RecTied.core_size_le p hp.2 (by linarith [hN.big.2.1])
end GlobalTheory.CovTop.DeepExist
end
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.CovTop.DeepExist.exists_deep_covering_level_alt | exact _root_.GlobalTheory.CovTop.DeepExist.exists_deep_covering_level_alt | (intros; apply _root_.GlobalTheory.CovTop.DeepExist.exists_deep_covering_level_alt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.covering_deepEx_of_prints : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepExistence := by
  first | exact @_root_.GlobalTheory.CovTop.DeepExist.exists_deep_covering_level_alt | exact _root_.GlobalTheory.CovTop.DeepExist.exists_deep_covering_level_alt | (intros; apply _root_.GlobalTheory.CovTop.DeepExist.exists_deep_covering_level_alt <;> assumption)
end
end
