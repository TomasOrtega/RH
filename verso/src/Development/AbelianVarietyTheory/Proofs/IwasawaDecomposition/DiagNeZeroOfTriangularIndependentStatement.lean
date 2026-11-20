import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagNeZeroOfTriangularIndependent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagEmb.tri_diag_ne_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FDiagNeZeroOfTriangularIndependent.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.diag_ne_zero_of_triangular_independent : ∀ (T : Type) (m : T → ℕ) (K : Type) [Field K] (ι : Type) (c c' : Let m → ι → K) (d : Let m → K), (∀ τ, LinearIndependent K fun j : Fin (m τ) => c' ⟨τ, j⟩) → Tri c c' d → ∀ z, d z ≠ 0 := by
  first | exact @GlobalTheory.FlagEmb.tri_diag_ne_zero | exact GlobalTheory.FlagEmb.tri_diag_ne_zero | (intros; apply GlobalTheory.FlagEmb.tri_diag_ne_zero <;> assumption)
