import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalRepOfReadingLaws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Laws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MAvGood
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecLawsH
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SphRead
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DaAutRepSphAt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
/- English proof (translation)
Introduce `hL D P S hT hLaws i P₁ P₂ hsplit hns`. Apply `P.H.av.inj i P₁ P₂` to reduce the goal to its premises. Use `GlobalTheory.T.algebraic_modular_forms_strong_multiplicity_one D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i P₁) (P.H.av.S i P₂) (P.H.av.irr i P₁) (P.H.av.irr i P₂) ?_ ?_` and prove the remaining obligations. Introduce `s`. Establish `hw` using `GlobalTheory.T.isSplitPlace_of_splitPlace_realSubfield_host D s`.

Use `⟨((S i s.w hw).rep P₁).toIrrRep, ((S i s.w hw).rep P₂).toIrrRep, hT.rep i s hw P₁, hT.rep i s hw P₂, ?_⟩` and prove the remaining obligations. Establish `e1` using `(S i s.w hw).locV P₁`. Establish `e2` using `(S i s.w hw).locV P₂`. Rewrite `e1` using `[hsplit s.w hw, e2]`. Conclude with `(_root_.UpperTheory.One.M.RecLawsH.iso (hLaws i s.w hw) _ _ _ (_root_.UpperTheory.One.M.good_cls_of_isLocS_av P i P₂ s _ (hT.rep i s hw P₂))).1 e1.symm`.

Introduce `v hv`. Take `⟨w, hO, hns', ⟨Dv⟩⟩` from `GlobalTheory.T.exists_nonsplit_place_with_inertDatum D D.R.nV v hv`. Establish `hsph : ∀ Q : D.naut.AV i, (P.H.av.rep i Q).SphericalAtPlace v` using `fun Q => by`. Establish `h` using `D.nbc.embAV_sph i Q w hns'`. Rewrite `h` using `[P.H.emb i Q]`.

Conclude with `(P.H.au.sph _ _ _ _ w v hns' hO).1 h`. Take `⟨α₁, hα₁, e₁⟩` from `P.H.au.sat _ _ _ (P.H.av.rep i P₁) v w hO Dv (_root_.UpperTheory.One.M.Sph.exists_satAt_of_overPl_sphAtG _ _ _ v w hO (hsph P₁) Dv)`. Take `⟨α₂, hα₂, e₂⟩` from `P.H.au.sat _ _ _ (P.H.av.rep i P₂) v w hO Dv (_root_.UpperTheory.One.M.Sph.exists_satAt_of_overPl_sphAtG _ _ _ v w hO (hsph P₂) Dv)`. Establish `hu` using `hns w hns'`. Rewrite `hu` using `[D.nbc.embAV_sat, D.nbc.embAV_sat, P.H.emb, P.H.emb, e₁, e₂]`.

Use `⟨w, Dv, α₁, hO, hα₁, ?_⟩` and prove the remaining obligations. Take `⟨f, hf, hf0, U, hU, hUv, hh⟩` from `hα₂`. Use `⟨f, hf, hf0, U, hU, hUv, fun h hh' => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.unitarySatake_eq_of_same_unramifiedBaseChange _ Dv.ϖ Dv.σw _ D.R.nV Dv.unram α₁ α₂ hu h hh']`. Conclude with `hh h hh'`.
-/
theorem repOfLocal_h_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → _root_.GlobalTheory.SplitRead.LawsAlt S → ∀ i, RepOfLoc D.nd D.naut i := by
  intro hL D P S hT hLaws i P₁ P₂ hsplit hns
  apply P.H.av.inj i P₁ P₂
  refine GlobalTheory.T.algebraic_modular_forms_strong_multiplicity_one D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i P₁) (P.H.av.S i P₂) (P.H.av.irr i P₁) (P.H.av.irr i P₂) ?_ ?_
  · intro s
    have hw := GlobalTheory.T.isSplitPlace_of_splitPlace_realSubfield_host D s
    refine ⟨((S i s.w hw).rep P₁).toIrrRep, ((S i s.w hw).rep P₂).toIrrRep, hT.rep i s hw P₁, hT.rep i s hw P₂, ?_⟩
    have e1 := (S i s.w hw).locV P₁
    have e2 := (S i s.w hw).locV P₂
    rw [hsplit s.w hw, e2] at e1
    exact (_root_.UpperTheory.One.M.RecLawsH.iso (hLaws i s.w hw) _ _ _ (_root_.UpperTheory.One.M.good_cls_of_isLocS_av P i P₂ s _ (hT.rep i s hw P₂))).1 e1.symm
  · intro v hv
    obtain ⟨w, hO, hns', ⟨Dv⟩⟩ := GlobalTheory.T.exists_nonsplit_place_with_inertDatum D D.R.nV v hv
    have hsph : ∀ Q : D.naut.AV i, (P.H.av.rep i Q).SphericalAtPlace v := fun Q => by
      have h := D.nbc.embAV_sph i Q w hns'
      rw [P.H.emb i Q] at h
      exact (P.H.au.sph _ _ _ _ w v hns' hO).1 h
    obtain ⟨α₁, hα₁, e₁⟩ :=
      P.H.au.sat _ _ _ (P.H.av.rep i P₁) v w hO Dv (_root_.UpperTheory.One.M.Sph.exists_satAt_of_overPl_sphAtG _ _ _ v w hO (hsph P₁) Dv)
    obtain ⟨α₂, hα₂, e₂⟩ :=
      P.H.au.sat _ _ _ (P.H.av.rep i P₂) v w hO Dv (_root_.UpperTheory.One.M.Sph.exists_satAt_of_overPl_sphAtG _ _ _ v w hO (hsph P₂) Dv)
    have hu := hns w hns'
    rw [D.nbc.embAV_sat, D.nbc.embAV_sat, P.H.emb, P.H.emb, e₁, e₂] at hu
    refine ⟨w, Dv, α₁, hO, hα₁, ?_⟩
    obtain ⟨f, hf, hf0, U, hU, hUv, hh⟩ := hα₂
    refine ⟨f, hf, hf0, U, hU, hUv, fun h hh' => ?_⟩
    rw [GlobalTheory.T.unitarySatake_eq_of_same_unramifiedBaseChange _ Dv.ϖ Dv.σw _ D.R.nV Dv.unram α₁ α₂ hu h hh']
    exact hh h hh'
end UpperTheory.One.M
end
end
