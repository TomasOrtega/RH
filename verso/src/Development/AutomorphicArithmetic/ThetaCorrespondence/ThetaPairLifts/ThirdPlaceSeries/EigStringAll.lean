import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenStringOfAgreement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandEigenStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigenAtInertStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SysParamSplitStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SysParamAtInertStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StrSplitStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaEigenCompatibilitySixth
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
/- English proof (translation)
Introduce `hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy`. Use `show y ≠ 0 → _`. Introduce `hy0 hh hops`. Set `s : GlobalTheory.DownLift.Sys D` to `fun Pp d => if hc : ∃ c : ℂ, hh Pp (Finsupp.single d 1) y = c • y then hc.choose else 0`. Establish `hs : GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) hh s y`.

Introduce `Pp d hG hLab`. Establish `hc : ∃ c : ℂ, hh Pp (Finsupp.single d 1) y = c • y` using `(GlobalTheory.LPositivity.split_or_inert D Pp).elim (fun h1 => _root_.GlobalTheory.T.theta_eigen_compatibility_first_alt hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops Pp hG h1 d hLab) (fun h1 => _root_.GlobalTheory.T.theta_eigen_compatibility_second_alt hAF hL D …`. Simplify using `only [s, dif_pos hc]`. Conclude with `hc.choose_spec`. Set `B : GlobalTheory.LFun.Fam D.host.E` to `fun w => if hB : ∃ Bw, GlobalTheory.LFun.IsSysParam D.sp.cm.sig (Formalism.IndefR.Links.Vc D j).rank (rfl : w.under (𝓞 D.host.F) = _) (s w) Bw then hB.choose else 0`.

Establish `hB : GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i))) (Formalism.IndefR.Links.Vc D j).rank s B`. Introduce `v hv w hw`. Substitute `hw` using the available equality. Establish `hex : ∃ Bw, GlobalTheory.LFun.IsSysParam D.sp.cm.sig (Formalism.IndefR.Links.Vc D j).rank (rfl : w.under (𝓞 D.host.F) = _) (s w) Bw`. Break down `GlobalTheory.LPositivity.split_or_inert D w with h1 | h1` into its components or cases.

Conclude with `_root_.GlobalTheory.T.theta_eigen_compatibility_third_alt hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s hs w hv h1`. Conclude with `_root_.GlobalTheory.T.theta_eigen_compatibility_fourth_alt hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s hs w hv h1`. Use `show GlobalTheory.LFun.IsSysParam D.sp.cm.sig _ _ (s w) (B w)`. Simplify using `only [B, dif_pos hex]`. Conclude with `hex.choose_spec`.

Use `⟨s, ⟨B, hB, fun w hw => ?_⟩, hs⟩` and prove the remaining obligations. Break down `GlobalTheory.LPositivity.split_or_inert D w with h1 | h1` into its components or cases. Conclude with `_root_.GlobalTheory.T.theta_eigen_compatibility_fifth_alt hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s B hs hB w hw h1`. Conclude with `_root_.GlobalTheory.T.theta_eigen_compatibility_sixth_alt hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s B hs hB w hw h1`.
-/
theorem GlobalTheory.EigStr.eigString_all_of_aux41_adm7_tieLab : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ i, GlobalTheory.NJoin.EigString X i := by
  intro hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy
  show y ≠ 0 → _
  intro hy0 hh hops
  classical
  let s : GlobalTheory.DownLift.Sys D := fun Pp d =>
    if hc : ∃ c : ℂ, hh Pp (Finsupp.single d 1) y = c • y then hc.choose else 0
  have hs : GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) hh s y := by
    intro Pp d hG hLab
    have hc : ∃ c : ℂ, hh Pp (Finsupp.single d 1) y = c • y :=
      (GlobalTheory.LPositivity.split_or_inert D Pp).elim
        (fun h1 => _root_.GlobalTheory.T.theta_eigen_compatibility_first_alt hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops Pp hG h1 d hLab)
        (fun h1 => _root_.GlobalTheory.T.theta_eigen_compatibility_second_alt hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops Pp hG h1 d hLab)
    simp only [s, dif_pos hc]
    exact hc.choose_spec
  let B : GlobalTheory.LFun.Fam D.host.E := fun w =>
    if hB : ∃ Bw, GlobalTheory.LFun.IsSysParam D.sp.cm.sig (Formalism.IndefR.Links.Vc D j).rank
        (rfl : w.under (𝓞 D.host.F) = _) (s w) Bw then hB.choose else 0
  have hB : GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i)))
      (Formalism.IndefR.Links.Vc D j).rank s B := by
    intro v hv w hw
    subst hw
    have hex : ∃ Bw, GlobalTheory.LFun.IsSysParam D.sp.cm.sig (Formalism.IndefR.Links.Vc D j).rank
        (rfl : w.under (𝓞 D.host.F) = _) (s w) Bw := by
      rcases GlobalTheory.LPositivity.split_or_inert D w with h1 | h1
      · exact _root_.GlobalTheory.T.theta_eigen_compatibility_third_alt hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s hs w hv h1
      · exact _root_.GlobalTheory.T.theta_eigen_compatibility_fourth_alt hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s hs w hv h1
    show GlobalTheory.LFun.IsSysParam D.sp.cm.sig _ _ (s w) (B w)
    simp only [B, dif_pos hex]
    exact hex.choose_spec
  refine ⟨s, ⟨B, hB, fun w hw => ?_⟩, hs⟩
  rcases GlobalTheory.LPositivity.split_or_inert D w with h1 | h1
  · exact _root_.GlobalTheory.T.theta_eigen_compatibility_fifth_alt hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s B hs hB w hw h1
  · exact _root_.GlobalTheory.T.theta_eigen_compatibility_sixth_alt hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s B hs hB w hw h1
end
