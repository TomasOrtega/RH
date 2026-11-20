import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TermSumBoundOfPairsAmplitude
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanDiagonalOfConditions
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqWire
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
noncomputable section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc
namespace GlobalTheory.Core.Deg

/- English proof (translation)
Introduce `C' Cl Cg cb Cw cT CT C0 D large₂ X Y u hH hT ha hA`. Establish `hN : NormExpDegC` using `Formalism.L2.SG.Pf.normExpDegC_of_leaves Formalism.L2.SG.Closed.FinLeviC_holds Formalism.L2.SG.Closed.OOLintSumC_holds`. Establish `hG0 : 0 ≤ (Y.tO u u).Gam1` using `ha.2.2.le`. Establish `hPg : 0 ≤ PgC Y` using `Finset.prod_nonneg fun v _ => by positivity`. Establish `hGB : (Y.tO u u).GGBound (PgC Y)` using `Formalism.L2.SG.TermOp.ggBound Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) Formalism.L2.SG.Closed.TermsGGBound_holds Y.psi_ne (fun v => card_ge_three hH.2 Y.TR v)`.

Use `⟨ha.1.indicator _, ?_⟩` and prove the remaining obligations. Conclude with `Formalism.L2.SG.RowsOther.kppDiag_of_pairs (Y.tO u u) Formalism.FourierDecayAlt.P.price_of_index Formalism.FourierDecayAlt.P.equal_index Formalism.FourierDecayAlt.P.pair_split_alt Formalism.FourierDecayAlt.P.subfamilyAlt (PgC Y) (duC X Y u) D.R.k D.R.f hPg ha (Formalism.L2.SG.Ter …`.
-/
theorem termSumBound_of_pairsAmplitude : TermSumBoundOfPairsAmplitude := by
  intro C' Cl Cg cb Cw cT CT C0 D large₂ X Y u hH hT ha hA
  have hN : NormExpDegC :=
    Formalism.L2.SG.Pf.normExpDegC_of_leaves Formalism.L2.SG.Closed.FinLeviC_holds Formalism.L2.SG.Closed.OOLintSumC_holds
  have hG0 : 0 ≤ (Y.tO u u).Gam1 := ha.2.2.le
  have hPg : 0 ≤ PgC Y := Finset.prod_nonneg fun v _ => by positivity
  have hGB : (Y.tO u u).GGBound (PgC Y) :=
    Formalism.L2.SG.TermOp.ggBound Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) Formalism.L2.SG.Closed.TermsGGBound_holds Y.psi_ne
      (fun v => card_ge_three hH.2 Y.TR v)
  refine ⟨ha.1.indicator _, ?_⟩
  exact Formalism.L2.SG.RowsOther.kppDiag_of_pairs (Y.tO u u) Formalism.FourierDecayAlt.P.price_of_index
    Formalism.FourierDecayAlt.P.equal_index Formalism.FourierDecayAlt.P.pair_split_alt Formalism.FourierDecayAlt.P.subfamilyAlt
    (PgC Y) (duC X Y u) D.R.k D.R.f hPg ha
    (Formalism.L2.SG.TermOp.rowOrth Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u))
    (Formalism.L2.SG.KappaOffDiagonal.corankPosC_holds D X Y u u hT) (hN D X Y u hT) hGB
    (Formalism.L2.SG.RowsOther.pairsDeg_of_amp _ hG0 _ _ _ _ hPg hA)

end GlobalTheory.Core.Deg
