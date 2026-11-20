import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFiniteSemiabelianOverAlgClosed
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
Apply `GlobalTheory.GroupBplus.Aff.TorsFin.finite_tors` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTorsionFiniteSemiabelianOverAlgClosed.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.torsion_finite_semiabelian_over_alg_closed : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → Finite (Tors G N K) := by
  first | exact @GlobalTheory.GroupBplus.Aff.TorsFin.finite_tors | exact GlobalTheory.GroupBplus.Aff.TorsFin.finite_tors | (intros; apply GlobalTheory.GroupBplus.Aff.TorsFin.finite_tors <;> assumption)
