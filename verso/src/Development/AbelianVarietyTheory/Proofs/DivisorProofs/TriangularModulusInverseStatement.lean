import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularModulusInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTriangularModulusInverse.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.triangular_modulus_inverse : ∀ (K : Type) [Field K] (N : ℕ) (R : Subring K) (h b : K) (A : Matrix (Fin N) (Fin N) K) (d : Fin N → K), Small R h → b ∈ R → A.det ≠ 0 → b • A⁻¹ ∈ R.matrix → TriMod R (h * b * b) A d → (∀ i, d i ≠ 0) ∧ TriMod R h A⁻¹ fun i => (d i)⁻¹ := by
  first | exact @GlobalTheory.LatChain.triMod_inv | exact GlobalTheory.LatChain.triMod_inv | (intros; apply GlobalTheory.LatChain.triMod_inv <;> assumption)
