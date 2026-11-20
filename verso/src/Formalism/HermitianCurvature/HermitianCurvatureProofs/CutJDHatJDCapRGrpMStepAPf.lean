import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMStepA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JDRvStepAOfLvlA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.GrpMA

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ k r hr z z' π π' D' Y hz hz' hD J₀ hJ₀ c hc g hg hgD`. Establish `h` using `Formalism.FourierDecayAlt.P.Qx6.lvlA (E := Wq →L[ℂ] Wp) hz hz' (TemperedBoundGL3.lr hr) (by show r - 1 + 1 = r; omega) hD hJ₀.1 hJ₀.2.1 hJ₀.2.2.1 Y hc (by rw [TemperedBoundGL3.lr_succ]; exact hg) hgD`. Rewrite `h` using `[TemperedBoundGL3.lr_succ]`. Conclude with `h`.
-/
theorem lvlA_last : LvlA := by
  intro Wp Wq _ _ _ _ k r hr z z' π π' D' Y hz hz' hD J₀ hJ₀ c hc g hg hgD
  have h := Formalism.FourierDecayAlt.P.Qx6.lvlA (E := Wq →L[ℂ] Wp) hz hz' (TemperedBoundGL3.lr hr) (by show r - 1 + 1 = r; omega) hD hJ₀.1
    hJ₀.2.1 hJ₀.2.2.1 Y hc (by rw [TemperedBoundGL3.lr_succ]; exact hg) hgD
  rw [TemperedBoundGL3.lr_succ] at h
  exact h

/- English proof (translation)
The claim follows from `jDRvStepA_of_lvlA lvlA_last`.
-/
theorem mirror_residue_first_move : JDRvStepA := jDRvStepA_of_lvlA lvlA_last

end Formalism.FourierDecayAlt.P.CutMP.GrpMA
