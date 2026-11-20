import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelRowsEqDimensionAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR
namespace GlobalTheory.Fc.Ind
/- English proof (translation)
Introduce `D O c b`. Establish `h1 : D.what₂.D0 = b.P.S0.D` using `GlobalTheory.rowSide_card_eq_of_coord O.ex.p0.s D.what₂.onb0 b.P.I.eRR0`. Establish `key : ∀ (Z Z' : DefSub b.P.A3.fam3.amb3) (S : IndefData (b.P.A3.side3 b.P.P0 b.P.ψ0 Z)) (S' : IndefData (b.P.A3.side3 b.P.P0 b.P.ψ0 Z')), Z = Z' → HEq S S' → S.D = S'.D`. Introduce `Z Z' S S' h h'`. Substitute `h` using the available equality.

Consider the cases of `eq_of_heq h'`. Both sides reduce to the same expression. Establish `h2` using `key _ _ _ _ b.B.Q.zs b.B.Q.s0`. Establish `h3` using `b.B.Q.zs`. Unfold `_root_.GlobalTheory.Fc.Ind.summandDegreeZero`.

Rewrite using `[h1, ← h2, ← h3]`. Both sides reduce to the same expression.
-/
theorem base_level_rows_eq_dimension_alt : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), _root_.GlobalTheory.Fc.Ind.summandDegreeZero D O c b := by
  intro D O c b
  have h1 : D.what₂.D0 = b.P.S0.D := GlobalTheory.rowSide_card_eq_of_coord O.ex.p0.s D.what₂.onb0 b.P.I.eRR0
  have key : ∀ (Z Z' : DefSub b.P.A3.fam3.amb3) (S : IndefData (b.P.A3.side3 b.P.P0 b.P.ψ0 Z))
      (S' : IndefData (b.P.A3.side3 b.P.P0 b.P.ψ0 Z')), Z = Z' → HEq S S' → S.D = S'.D := by
    intro Z Z' S S' h h'
    subst h
    cases eq_of_heq h'
    rfl
  have h2 := key _ _ _ _ b.B.Q.zs b.B.Q.s0
  have h3 := b.B.Q.zs
  unfold _root_.GlobalTheory.Fc.Ind.summandDegreeZero
  rw [h1, ← h2, ← h3]
  rfl
end GlobalTheory.Fc.Ind
end
