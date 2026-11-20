import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Lin

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Replace the relevant objects with their definitions. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem hsVec_sub_rd (A A' : Wq →L[ℂ] Wp) : B.hsVec (A - A') = B.hsVec A - B.hsVec A' := by
  unfold B.hsVec
  ext i
  simp

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.
-/
theorem beta_conj_rd (D : B.RealPlaceData k r Wp Wq) (F F' : B.Mat k r → (Wq →L[ℂ] Wp)) :
    B.beta D F F' = starRingEnd ℂ (B.beta D F' F) := by
  unfold B.beta Formalism.QuantumDeterminants.betaBig
  rw [← integral_conj]
  congr 1
  funext p
  rw [map_mul, Complex.conj_ofReal, inner_conj_symm]

variable [FiniteDimensional ℂ Wp]

end Lin

end Formalism.FourierDecayAlt.P.CutSE
