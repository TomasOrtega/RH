import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralAdeleAtPlaceWithComponent
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SigV
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FixedUnitNorm.exists_intAt_compAt_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsIntegralAdeleAtPlaceWithComponent.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.exists_integralAdele_atPlace_with_component : ∀ (D : D7) (v : Pl D) (z : Fv D.host.F v ⊗[D.host.F] D.host.E), z ∈ intV D v → ∃ x ∈ intAt D (· = v), compAt D v x = z := by
  first | exact @GlobalTheory.FixedUnitNorm.exists_intAt_compAt_eq | exact GlobalTheory.FixedUnitNorm.exists_intAt_compAt_eq | (intros; apply GlobalTheory.FixedUnitNorm.exists_intAt_compAt_eq <;> assumption)
