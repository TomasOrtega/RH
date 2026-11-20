import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagCellOfNonvanishingLeadingMinors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsFlagCellOfNonvanishingLeadingMinors.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.exists_flagCell_of_nonvanishing_leading_minors : ∀ (T : Type) (m : T → ℕ) (K : Type) [Field K] (M : ℕ) (D c u : Let m → Fin (M + 1) → K) (w : Pm m), LeftInv D c → InBlock c u → (∀ τ j hj, ∑ q, lform D (wLet w ∘ std τ j hj) q * plk u (std τ j hj) q ≠ 0) → ∃ (x : CellVar m → K) (d : Let m → K), (∀ z, d z ≠ 0) ∧ Tri (cellVec c w x) u d := by
  first | exact @GlobalTheory.FlagEmb.CellLU.exists_cell | exact GlobalTheory.FlagEmb.CellLU.exists_cell | (intros; apply GlobalTheory.FlagEmb.CellLU.exists_cell <;> assumption)
