import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableOfIntegrableProdOfContinuous

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.ProdFactor

/- English proof (translation)
Introduce `D X hX v`. Establish `hU : ∀ v, IsURepOn (UJset (X.B.I.ε v)) (X.B.σ v)` using `fun v => (X.ds v).2.2.1`. Establish `hw : ∀ v, ‖X.B.w v‖ = 1` using `fun v => (X.low v).1`. Establish `hd : ∀ v, X.dv v ≠ 0` using `fun v => (fdegOf_pos (hU v) (X.ds v).2.2.2.2.1 (hw v)).ne'`. Conclude with `integrable_factor' X.B.I.ε X.B.σ X.B.w X.dv hU hw hd hX v`.
-/
theorem integrable_phLoc_of_integrable_ph : ∀ (D : D7) (X : HidaSetting D), Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v))) (Formalism.REAL.muG (X.B.I.ε v)) := by
  intro D X hX v
  have hU : ∀ v, IsURepOn (UJset (X.B.I.ε v)) (X.B.σ v) := fun v => (X.ds v).2.2.1
  have hw : ∀ v, ‖X.B.w v‖ = 1 := fun v => (X.low v).1
  have hd : ∀ v, X.dv v ≠ 0 := fun v =>
    (fdegOf_pos (hU v) (X.ds v).2.2.2.2.1 (hw v)).ne'

  exact integrable_factor' X.B.I.ε X.B.σ X.B.w X.dv hU hw hd hX v

end GlobalTheory.ProdFactor
