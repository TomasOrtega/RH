import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleSectionsFiniteProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FVectorBundleSectionsFiniteProjective.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.vector_bundle_sections_finite_projective : ∀ (X : Scheme.{0}) (F : X.Modules) (r : ℕ), GlobalTheory.VB.IsVB F r → ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(F, U) ∧ Module.Projective Γ(X, U) Γ(F, U) := by
  first | exact @GlobalTheory.ChainDesc.finite_projective_sections_of_isVB | exact GlobalTheory.ChainDesc.finite_projective_sections_of_isVB | (intros; apply GlobalTheory.ChainDesc.finite_projective_sections_of_isVB <;> assumption)
