import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoherentOfCrossWithBoundedInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LatChain.coh_of_cross` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoherentOfCrossWithBoundedInverse.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.coherent_of_cross_with_bounded_inverse : ∀ (X : Scheme.{0}) [IsIntegral X] (p k a N : ℕ) (M M' : X → Matrix (Fin N) (Fin N) X.functionField) (c c' : X → Fin N → X.functionFieldˣ) (P Q : Matrix (Fin N) (Fin N) X.functionField), P * Q = 1 → (∀ x, Ov p x → ((p : X.functionField) ^ a) • P ∈ (loc x).matrix ∧ ((p : X.functionField) ^ a) • Q ∈ (loc x).matrix) → Cross p (k + 1 + 3 * a) M M' c c' P → Coh p (k + 1) M c ∧ Coh p (k + 1) M' c' := by
  first | exact @GlobalTheory.LatChain.coh_of_cross | exact GlobalTheory.LatChain.coh_of_cross | (intros; apply GlobalTheory.LatChain.coh_of_cross <;> assumption)
