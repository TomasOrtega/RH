import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPidSubringPIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LatChain.exists_pid_subring_pInt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPidSubringPIntegral.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_pid_subring_p_integral : ∀ (K : Type) [Field K] [CharZero K] (p : ℕ), p.Prime → ∀ s : Finset K, (∀ f ∈ s, IsIntegral ℤ f) → ∃ R : Subring K, IsPrincipalIdealRing R ∧ (∀ f ∈ s, f ∈ R) ∧ ∀ f ∈ R, PInt p f := by
  first | exact @GlobalTheory.LatChain.exists_pid_subring_pInt | exact GlobalTheory.LatChain.exists_pid_subring_pInt | (intros; apply GlobalTheory.LatChain.exists_pid_subring_pInt <;> assumption)
