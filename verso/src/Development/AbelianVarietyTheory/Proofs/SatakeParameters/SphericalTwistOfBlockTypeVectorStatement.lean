import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalTwistOfBlockTypeVector
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FSphericalTwistOfBlockTypeVector.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.spherical_twist_of_blockTypeVector : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (π₁ : Irr k r) (π₂ : Irr k t) (v : π.V), IsSmoothChar χ → IsTame χ → (∀ α : ℂˣ, ¬ InSupport π₁.π (χ * unrChar k α)) → Nonempty (π.π.Equiv (prod₂ π₁.π π₂.π)) → v ≠ 0 → IsBlockVec χ π.π v → IsSpherical (twist π₂.π (detChar (Fin t) χ⁻¹)) := by
  first | exact @GlobalTheory.BlockSph.sph_of_isBlockVec | exact GlobalTheory.BlockSph.sph_of_isBlockVec | (intros; apply GlobalTheory.BlockSph.sph_of_isBlockVec <;> assumption)
