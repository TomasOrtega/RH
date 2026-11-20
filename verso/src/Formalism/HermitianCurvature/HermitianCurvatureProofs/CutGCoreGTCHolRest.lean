import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolPh
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolPhaseRel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolConnUniq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

/- English proof (translation)
Introduce `TT u hu h1 R _ hR`. Conclude with `Ph.hol_unit (TT := TT) hu (fun ζ hζ => h1 ζ hζ) hR`.
-/
theorem phase_holomorphy_holds : GTCPhHol := by
  intro TT u hu h1 R _ hR
  exact Ph.hol_unit (TT := TT) hu (fun ζ hζ => h1 ζ hζ) hR

/- English proof (translation)
Introduce `TT u hu h1 ζ hζ`. Conclude with `Ph.curv_unit (TT := TT) hu (fun ζ hζ => h1 ζ hζ) hζ`.
-/
theorem phase_curvature_holds : GTCPhCurv := by
  intro TT u hu h1 ζ hζ
  exact Ph.curv_unit (TT := TT) hu (fun ζ hζ => h1 ζ hζ) hζ

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs X d hyp e A B u hAB hu hC`. Conclude with `connF_phase P (tt_nonneg_of_hyp hyp) Bs d e A B u hAB hC hu`.
-/
theorem connection_phase_holds : GTCConnPhase := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e A B u hAB hu hC
  exact connF_phase P (tt_nonneg_of_hyp hyp) Bs d e A B u hAB hC hu

/- English proof (translation)
The claim follows from `gTCHol_of_cut hRef phase_relation_holds connection_uniqueness_holds connection_phase_holds phase_holomorphy_holds`.
-/
theorem gTCHol_of_ref (hRef : GTCRef) : GTCHol :=
  gTCHol_of_cut hRef phase_relation_holds connection_uniqueness_holds connection_phase_holds phase_holomorphy_holds

/- English proof (translation)
The claim follows from `gTCCurv_of_cut hRef phase_relation_holds connection_uniqueness_holds connection_phase_holds phase_curvature_holds`.
-/
theorem gTCCurv_of_ref (hRef : GTCRef) : GTCCurv :=
  gTCCurv_of_cut hRef phase_relation_holds connection_uniqueness_holds connection_phase_holds phase_curvature_holds

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
