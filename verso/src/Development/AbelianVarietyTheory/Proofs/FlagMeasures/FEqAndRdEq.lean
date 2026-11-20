import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

namespace GlobalTheory.DegreeRankEquations

/- English proof (translation)
Establish `e1 : Module.finrank ℚ X.B.I.E = Module.finrank ℚ D.host.E` using `(X.ιE.toRatAlgEquiv).toLinearEquiv.finrank_eq`. Establish `e2 : Module.finrank ℚ X.B.I.F * Module.finrank X.B.I.F X.B.I.E = Module.finrank ℚ X.B.I.E` using `Module.finrank_mul_finrank ℚ X.B.I.F X.B.I.E`. Establish `e3 : Module.finrank X.B.I.F X.B.I.E = 2` using `X.B.I.cm.deg2`. Establish `e4 : Module.finrank ℚ D.host.E = 2 * D.R.f`. Rewrite using `[D.host.finrank_cmField]`.

Unfold `Ranks.f Ranks.n`. Put the polynomial expressions in normal form. Rewrite `e2` using `[e3]`. Unfold `AutInst.f`. Use linear arithmetic over natural numbers and integers.
-/
theorem f_eq (D : D7) (X : HidaSetting D) : X.B.I.f = D.R.f := by
  have e1 : Module.finrank ℚ X.B.I.E = Module.finrank ℚ D.host.E :=
    (X.ιE.toRatAlgEquiv).toLinearEquiv.finrank_eq
  have e2 : Module.finrank ℚ X.B.I.F * Module.finrank X.B.I.F X.B.I.E = Module.finrank ℚ X.B.I.E :=
    Module.finrank_mul_finrank ℚ X.B.I.F X.B.I.E
  have e3 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have e4 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring_nf
  rw [e3] at e2
  unfold AutInst.f
  omega

/- English proof (translation)
Establish `hd : discr X.B.I.E = discr D.host.E` using `NumberField.discr_eq_discr_of_algEquiv X.B.I.E X.ιE.toRatAlgEquiv`. Establish `e1 : Module.finrank ℚ X.B.I.E = Module.finrank ℚ D.host.E` using `(X.ιE.toRatAlgEquiv).toLinearEquiv.finrank_eq`. Establish `e2 : Module.finrank ℚ X.B.I.F * Module.finrank X.B.I.F X.B.I.E = Module.finrank ℚ X.B.I.E` using `Module.finrank_mul_finrank ℚ X.B.I.F X.B.I.E`. Establish `e3 : Module.finrank X.B.I.F X.B.I.E = 2` using `X.B.I.cm.deg2`. Establish `e4 : (Module.finrank ℚ D.host.E : ℝ) = 2 * (X.B.I.f : ℝ)`.

Unfold `AutInst.f`. Establish `: Module.finrank ℚ D.host.E = 2 * Module.finrank ℚ X.B.I.F` using `by rw [← e1, ← e2, e3, mul_comm]`. Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Unfold `AutInst.rd Host.rdE`. Rewrite using `[hd, e4]`.
-/
theorem rd_eq (D : D7) (X : HidaSetting D) : X.B.I.rd = D.host.rdE := by
  have hd : discr X.B.I.E = discr D.host.E := NumberField.discr_eq_discr_of_algEquiv X.B.I.E X.ιE.toRatAlgEquiv
  have e1 : Module.finrank ℚ X.B.I.E = Module.finrank ℚ D.host.E :=
    (X.ιE.toRatAlgEquiv).toLinearEquiv.finrank_eq
  have e2 : Module.finrank ℚ X.B.I.F * Module.finrank X.B.I.F X.B.I.E = Module.finrank ℚ X.B.I.E :=
    Module.finrank_mul_finrank ℚ X.B.I.F X.B.I.E
  have e3 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have e4 : (Module.finrank ℚ D.host.E : ℝ) = 2 * (X.B.I.f : ℝ) := by
    unfold AutInst.f
    have : Module.finrank ℚ D.host.E = 2 * Module.finrank ℚ X.B.I.F := by rw [← e1, ← e2, e3, mul_comm]
    rw [this]; push_cast; ring
  unfold AutInst.rd Host.rdE
  rw [hd, e4]

end GlobalTheory.DegreeRankEquations
