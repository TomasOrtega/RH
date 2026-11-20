import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelCoordinatesCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterpolationInverseMatrixSumIdentity

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD`. Take `⟨-, -, hL, hQ, -⟩` from `hD`. Take `⟨hp, hpb, hc, hci, hcb, hcbi, -⟩` from `hL`. Establish `ht : ∀ Y (a b : Fin 2) l (i : Fin 6), Commute (X.t Y a b) (X.op l i)` using `fun Y a b l i => Formalism.FourierDecayAlt.P.NFx1.TC.t_op_comm X Y a b l i`. Introduce `Y a b l x hx`.

Establish `hm : Commute (X.QQ Y a b) x`. Rewrite using `[Formalism.FourierDecayAlt.P.NFx3.QQ_apply]`. Simplify using `only [coordOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hx`. Break down `hx with rfl | rfl | rfl | rfl | rfl | rfl` into its components or cases. Rewrite using `[hp l]`.

Conclude with `Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 0) (ht (star Y) b a l 3).neg_right`. Rewrite using `[hpb l]`. Conclude with `Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 3) (ht (star Y) b a l 0).neg_right`. Rewrite using `[hc l]`. Conclude with `Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 1) (ht (star Y) b a l 4)`.

Rewrite using `[hci l]`. Conclude with `Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 2) (ht (star Y) b a l 5)`. Rewrite using `[hcb l]`. Conclude with `Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 4) (ht (star Y) b a l 1)`. Rewrite using `[hcbi l]`.

Conclude with `Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 5) (ht (star Y) b a l 2)`. Rewrite using `[hQ Y, Matrix.smul_apply]`. Conclude with `hm.smul_left _`.
-/
theorem radial_start_coordinates : RDStartCoord := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD
  obtain ⟨-, -, hL, hQ, -⟩ := hD
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL
  have ht : ∀ Y (a b : Fin 2) l (i : Fin 6), Commute (X.t Y a b) (X.op l i) :=
    fun Y a b l i => Formalism.FourierDecayAlt.P.NFx1.TC.t_op_comm X Y a b l i
  intro Y a b l x hx
  have hm : Commute (X.QQ Y a b) x := by
    rw [Formalism.FourierDecayAlt.P.NFx3.QQ_apply]
    simp only [coordOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 0) (ht (star Y) b a l 3).neg_right
    · rw [hpb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 3) (ht (star Y) b a l 0).neg_right
    · rw [hc l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 1) (ht (star Y) b a l 4)
    · rw [hci l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 2) (ht (star Y) b a l 5)
    · rw [hcb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 4) (ht (star Y) b a l 1)
    · rw [hcbi l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 5) (ht (star Y) b a l 2)
  rw [hQ Y, Matrix.smul_apply]
  exact hm.smul_left _

end Formalism.FourierDecayAlt.P.CutSE
