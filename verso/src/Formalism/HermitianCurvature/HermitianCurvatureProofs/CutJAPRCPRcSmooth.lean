import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCoreCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian

open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `k r E _ _ D f f' _ hf hf' Z hZ`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Qx2.smooth_add (Qx2.rd_smooth hf hZ.1) (Qx2.smooth_smul (Qx2.rd_smooth hf hZ.2) Complex.I)`. Introduce `a g hg`. Establish `e : (fun x => a • f x + f' x) = fun x => f' x + a • f x`.

Use function extensionality and compare the values at `x`. Conclude with `add_comm _ _`. Use `show RdV _ (fun x => a • f x + f' x) g + Complex.I • RdV _ (fun x => a • f x + f' x) g = a • (RdV _ f g + Complex.I • RdV _ f g) + (RdV _ f' g + Complex.I • RdV _ f' g)`. Rewrite using `[e, Qx2.rd_lin hf' hf a hg hZ.1, Qx2.rd_lin hf' hf a hg hZ.2, smul_add, smul_add, smul_comm Complex.I a]`. Normalize the expressions using the abelian group laws.

Introduce `E' _ _ L g hg show RdV _ (fun x => L (f x)) g + Complex.I • RdV _ (fun x => L (f x)) g = L (RdV _ f g + Complex.I • RdV _ f g)`. Establish `e1 : RdV (hpart1 (Hpk k r) Z) (fun y => L (f y)) g = L (RdV _ f g)` using `Qx5.ntw_rd L hZ.1 f hf g hg`. Establish `e2 : RdV (hpart2 (Hpk k r) Z) (fun y => L (f y)) g = L (RdV _ f g)` using `Qx5.ntw_rd L hZ.2 f hf g hg`. Rewrite using `[e1, e2, map_add, map_smul]`.
-/
theorem radial_coefficient_smoothness : RcSmooth := by
  intro k r E _ _ D f f' _ hf hf' Z hZ
  refine ⟨?_, ?_, ?_⟩
  · exact Qx2.smooth_add (Qx2.rd_smooth hf hZ.1) (Qx2.smooth_smul (Qx2.rd_smooth hf hZ.2) Complex.I)
  · intro a g hg
    have e : (fun x => a • f x + f' x) = fun x => f' x + a • f x := by
      funext x
      exact add_comm _ _
    show RdV _ (fun x => a • f x + f' x) g + Complex.I • RdV _ (fun x => a • f x + f' x) g =
      a • (RdV _ f g + Complex.I • RdV _ f g) + (RdV _ f' g + Complex.I • RdV _ f' g)
    rw [e, Qx2.rd_lin hf' hf a hg hZ.1, Qx2.rd_lin hf' hf a hg hZ.2, smul_add, smul_add, smul_comm Complex.I a]
    abel
  · intro E' _ _ L g hg
    show RdV _ (fun x => L (f x)) g + Complex.I • RdV _ (fun x => L (f x)) g = L (RdV _ f g + Complex.I • RdV _ f g)
    have e1 : RdV (hpart1 (Hpk k r) Z) (fun y => L (f y)) g = L (RdV _ f g) := Qx5.ntw_rd L hZ.1 f hf g hg
    have e2 : RdV (hpart2 (Hpk k r) Z) (fun y => L (f y)) g = L (RdV _ f g) := Qx5.ntw_rd L hZ.2 f hf g hg
    rw [e1, e2, map_add, map_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
