import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactChainTopRowRealPointInOrthonormalBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqConjOfInFrame

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FCompactChainTopRowRealPointInOrthonormalBasis.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.compactChainTopRowRealPoint_inOrthonormalBasis : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (n : Fin (D.R.m + 1)),
    ((n : ℕ) = D.R.m → ∀ τ, W.onb (.top D.R.m) τ = GlobalTheory.RowReal.topFrame W τ) → ∀ τ,
    (W.onb (.top n) τ)⁻¹ * compAt W.θ τ (mt _ (GlobalTheory.RowReal.ptTop W g n)) * W.onb (.top n) τ =
      (rowComp (GlobalTheory.RowReal.rowSizes D) g n τ).1.submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (Nat.lt_succ_iff.1 n.2)))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (Nat.lt_succ_iff.1 n.2))) := by
  first | exact @GlobalTheory.RowReal.ptTop_inOnb | exact GlobalTheory.RowReal.ptTop_inOnb | (intros; apply GlobalTheory.RowReal.ptTop_inOnb <;> assumption)
