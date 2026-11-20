import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharEtaBack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.GoodDepthZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
/- English proof (translation)
Introduce `D hT hA h41 _ a x hx Sig hSig k v`. Take `⟨-, Sig', hSig', hgood⟩` from `hx`. Establish `hc : ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b` using `hA.2.2`. Establish `hL` using `charSum_of_tie D hT.1 hc`. Take `⟨P, hP, hB⟩` from `hSig`.

Take `⟨P', hP', hB'⟩` from `id hSig'`. Establish `hperm` using `((h41 a).2.1 P P' (by rw [hP]; simp) (hP.trans hP'.symm)).1 _ _ hB hB'`. Establish `e1` using `GlobalTheory.RowTie.isoLoc_perm D.nd D.naut hperm (D.naut.plGw k v)`. Rewrite `e1` using `[GlobalTheory.LocCongrRoad.isoLoc_twist _ _ hL, GlobalTheory.LocCongrRoad.isoLoc_twist _ _ hL]`. Establish `e2` using `congrArg (fun b => D.naut.lpChar b (D.naut.locG D.naut.etaT (D.naut.plGw k v))) e1`.

Simplify using `only [lpChar_eta_back D hT.1] at e2`. Rewrite `e2` using `[GlobalTheory.LocCongrRoad.isoLoc_append_singleton, GlobalTheory.LocCongrRoad.isoLoc_append_singleton]`. Rewrite using `[hc _ _ _ _ e2]`. Conclude with `GlobalTheory.PointIrredCompare.fullLabels_of_good D.nd D.naut hSig' hgood k v`.
-/
theorem main_alt_alt : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D →
    (∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)) → Formalism.MainNotions.N.GlobalDatumDepthZeroCondition D := by
  intro D hT hA h41 _ a x hx Sig hSig k v
  obtain ⟨-, Sig', hSig', hgood⟩ := hx
  have hc : ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b := hA.2.2
  have hL := charSum_of_tie D hT.1 hc
  obtain ⟨P, hP, hB⟩ := hSig
  obtain ⟨P', hP', hB'⟩ := id hSig'
  have hperm := ((h41 a).2.1 P P' (by rw [hP]; simp) (hP.trans hP'.symm)).1 _ _ hB hB'
  have e1 := GlobalTheory.RowTie.isoLoc_perm D.nd D.naut hperm (D.naut.plGw k v)
  rw [GlobalTheory.LocCongrRoad.isoLoc_twist _ _ hL, GlobalTheory.LocCongrRoad.isoLoc_twist _ _ hL] at e1
  have e2 := congrArg (fun b => D.naut.lpChar b (D.naut.locG D.naut.etaT (D.naut.plGw k v))) e1
  simp only [lpChar_eta_back D hT.1] at e2
  rw [GlobalTheory.LocCongrRoad.isoLoc_append_singleton, GlobalTheory.LocCongrRoad.isoLoc_append_singleton] at e2
  rw [hc _ _ _ _ e2]
  exact GlobalTheory.PointIrredCompare.fullLabels_of_good D.nd D.naut hSig' hgood k v
end GlobalTheory.GoodDepthZero
end
end
