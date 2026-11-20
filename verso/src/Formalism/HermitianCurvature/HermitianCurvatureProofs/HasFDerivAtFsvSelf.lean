import Formalism.HermitianCurvature.TopEntryWaveEquation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FsvMulFsvNeg

open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem contDiff_fsv (s : ℂ) : ContDiff ℝ ∞ (fsv s) := by
  have hL : ContDiff ℝ ∞ (fun t : ℂ => s * t - conj s * conj t) :=
    (contDiff_const.mul contDiff_id).sub (contDiff_const.mul Complex.conjCLE.contDiff)
  exact Complex.contDiff_exp.comp hL

section PairNeg

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pr_neg_fst (a : Pr V) : (-a).1 = -a.1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pr_neg_snd (a : Pr V) : (-a).2.unop = -a.2.unop := rfl

end PairNeg

end Formalism.FourierDecayAlt.P5
