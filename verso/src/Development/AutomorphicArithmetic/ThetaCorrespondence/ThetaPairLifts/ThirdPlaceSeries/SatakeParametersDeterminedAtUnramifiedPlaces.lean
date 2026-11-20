import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StatementAOfPhotonCompatStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithOrigin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RayPrimeHostIntegral
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowDepthOfPrimitive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclOfGrpStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
noncomputable section
namespace GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
/- English proof (translation)
Introduce `hP hC hL`. Establish `hE` using `_root_.GlobalTheory.T.isRayPrime_g_and_integral_range hP`. Establish `hR` using `_root_.GlobalTheory.T.depth_of_repOf_of_inputs hP`. Establish `hA` using `_root_.GlobalTheory.T.types_true_of_ray_class_alt hL hP.what₂.fin hP.what₂.berger hP.greenC hP.what₂.art hP.ray hP.what₂.cheb`. Unfold `_root_.GlobalTheory.HeightCounting.Up.FirstStageExists AllSt`.

Use `StepW.trans (StepW.and hE hR) (StepW.of_all ?_)` and prove the remaining obligations. Introduce `K B f T w _ _ hq P x hLoc`. Take `⟨hEl, hRw⟩` from `hq`. Take `⟨hElem, -, -, h, jE, hfr, hray⟩` from `hEl P x`. Establish `e1 : (cfOf x).P = f.P` using `by show w.I.C.P = f.P`.

Rewrite using `[w.C_eq]`. Establish `e2 : (cfOf x).W = f.W` using `by show w.I.C.W = f.W`. Rewrite using `[w.C_eq]`. Establish `hTy : TypesTrue (Dof x).ntypes (cfOf x).P (cfOf x).W`. Rewrite using `[e1, e2]`.

Conclude with `x.fits.grp`. Take `⟨L, hZ, hη, A, hcg, hau, hrow, hTT, hPlG, hplGw, hcA, hcM, hζ, hloc, hO1, hO2, hO3, hO4, hlab⟩` from `hA (Dof x) hLoc (cfOf x) jE (repOf x.r.Y) hElem.int hTy (hRw P x) hray`. Establish `hG : GrpTrue (nOfLay x L hZ hη) f` using `by show TypesTrue L.ntypes f.P f.W`. Rewrite using `[← e1, ← e2]`. Conclude with `hTT`.

Take `⟨hGA, hCen⟩` from `GlobalTheory.T.heckeGaloisStage_fits_of_same_centre_actions x (nOfLay x L hZ hη) hG hPlG hplGw hcA hcM`. Take `⟨x', hx', hrep⟩` from `GlobalTheory.T.exists_transported_state_heckeGaloisStage x (nOfLay x L hZ hη) hG hGA hCen`. Take `⟨Pq, hPq1, hPq2⟩` from `exists_pq_sel B w.I w.ok`. Establish `hEl'` using `hEl P x'`. Establish `hRw'` using `hRw P x'`.

Take `⟨o', fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩` from `x'`. Simplify using `only at hx'`. Substitute `hx'` using the available equality. Take `⟨fr, hfrj⟩` from `omFrame_exists_with_jE (setK (Dof x) L hZ hη) jE`. Take `⟨Wd, hWd⟩` from `PhtExt.exists_phtOn_all hC (setK (Dof x) L hZ hη) fr A.wdT A.wd`.

Set `A' : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding (setK (Dof x) L hZ hη) (cfK L hZ hη (cfOf x)) jE` to `{ A with wd := Wd }`. Establish `e` using `eq_of_heq hrep`. Take `⟨cg⟩` from `hcg`. Use `⟨⟨⟨x.o.η, x.o.hη, x.o.V, x.o.S, nOfLay x L hZ hη, x.o.G⟩, fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩, ⟨⟨⟨⟨h.fr, h.jLL, h.embLL⟩, jE, hfr, A', cg, hau, ?_, fr, hfrj, hWd, hRw', hEl'.1, hEl'.2.1, hlab, hζ, hEl'.2.2.1⟩, Pq, hPq1, hPq2⟩⟩, ⟨⟨rfl, HEq.rfl, hloc.symm, hO1. …` and prove the remaining obligations. Rewrite using `[e]`.

Conclude with `hrow`.
-/
theorem satake_parameter_of_prime_to_level_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → PhtCmp → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.FirstStageExists hL := by
  intro hP hC hL
  have hE := _root_.GlobalTheory.T.isRayPrime_g_and_integral_range hP
  have hR := _root_.GlobalTheory.T.depth_of_repOf_of_inputs hP
  have hA := _root_.GlobalTheory.T.types_true_of_ray_class_alt hL hP.what₂.fin hP.what₂.berger hP.greenC hP.what₂.art hP.ray hP.what₂.cheb
  unfold _root_.GlobalTheory.HeightCounting.Up.FirstStageExists AllSt
  refine StepW.trans (StepW.and hE hR) (StepW.of_all ?_)
  intro K B f T w _ _ hq P x hLoc
  obtain ⟨hEl, hRw⟩ := hq
  obtain ⟨hElem, -, -, h, jE, hfr, hray⟩ := hEl P x
  have e1 : (cfOf x).P = f.P := by
    show w.I.C.P = f.P
    rw [w.C_eq]
  have e2 : (cfOf x).W = f.W := by
    show w.I.C.W = f.W
    rw [w.C_eq]
  have hTy : TypesTrue (Dof x).ntypes (cfOf x).P (cfOf x).W := by
    rw [e1, e2]
    exact x.fits.grp
  obtain ⟨L, hZ, hη, A, hcg, hau, hrow, hTT, hPlG, hplGw, hcA, hcM, hζ, hloc, hO1, hO2, hO3, hO4, hlab⟩ :=
    hA (Dof x) hLoc (cfOf x) jE (repOf x.r.Y) hElem.int hTy (hRw P x) hray
  have hG : GrpTrue (nOfLay x L hZ hη) f := by
    show TypesTrue L.ntypes f.P f.W
    rw [← e1, ← e2]
    exact hTT
  obtain ⟨hGA, hCen⟩ := GlobalTheory.T.heckeGaloisStage_fits_of_same_centre_actions x (nOfLay x L hZ hη) hG hPlG hplGw hcA hcM
  obtain ⟨x', hx', hrep⟩ := GlobalTheory.T.exists_transported_state_heckeGaloisStage x (nOfLay x L hZ hη) hG hGA hCen
  obtain ⟨Pq, hPq1, hPq2⟩ := exists_pq_sel B w.I w.ok
  have hEl' := hEl P x'
  have hRw' := hRw P x'
  obtain ⟨o', fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩ := x'
  dsimp only at hx'
  subst hx'
  obtain ⟨fr, hfrj⟩ := omFrame_exists_with_jE (setK (Dof x) L hZ hη) jE
  obtain ⟨Wd, hWd⟩ := PhtExt.exists_phtOn_all hC (setK (Dof x) L hZ hη) fr A.wdT A.wd
  let A' : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding (setK (Dof x) L hZ hη) (cfK L hZ hη (cfOf x)) jE := { A with wd := Wd }
  have e := eq_of_heq hrep
  obtain ⟨cg⟩ := hcg
  refine ⟨⟨⟨x.o.η, x.o.hη, x.o.V, x.o.S, nOfLay x L hZ hη, x.o.G⟩, fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩, ⟨⟨⟨⟨h.fr, h.jLL, h.embLL⟩, jE, hfr, A', cg, hau, ?_, fr, hfrj, hWd, hRw', hEl'.1, hEl'.2.1, hlab, hζ, hEl'.2.2.1⟩,
    Pq, hPq1, hPq2⟩⟩, ⟨⟨rfl, HEq.rfl, hloc.symm, hO1.symm, hO2.symm, hO3.symm, hO4.symm, heq_of_eq hPlG.symm⟩, hplGw.symm⟩⟩
  rw [e]
  exact hrow
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.HeightCounting.Up.satake_parameter_of_prime_to_level_alt | exact _root_.GlobalTheory.HeightCounting.Up.satake_parameter_of_prime_to_level_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.satake_parameter_of_prime_to_level_alt <;> assum …`.
-/
theorem _root_.GlobalTheory.T.stageAExists_of_inputs_phtCmp : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → PhtCmp → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.FirstStageExists hL := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.satake_parameter_of_prime_to_level_alt | exact _root_.GlobalTheory.HeightCounting.Up.satake_parameter_of_prime_to_level_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.satake_parameter_of_prime_to_level_alt <;> assumption)
end
end
