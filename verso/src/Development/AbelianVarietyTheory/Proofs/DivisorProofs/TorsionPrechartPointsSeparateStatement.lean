import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPrechartPointsSeparate
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTorsionPrechartPointsSeparate.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.torsion_prechart_points_separate : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (q : PrimeSpectrum R) (c : PreChart G N q), Finite (c.C →ₐ[R] K) ∧ ∀ a : c.C, (∀ ψ : c.C →ₐ[R] K, ψ a = 0) → a = 0 := by
  first | exact @GlobalTheory.ChartSep.chart_finite_separating | exact GlobalTheory.ChartSep.chart_finite_separating | (intros; apply GlobalTheory.ChartSep.chart_finite_separating <;> assumption)
