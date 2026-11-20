import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateHonda
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et
open scoped TensorProduct DirectSum
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AbFieldDim

/- English proof (translation)
Introduce `k _ A _ hA`. Conclude with `GlobalTheory.AbelianDim.exists_relDim k A hA`.
-/
theorem exists_smoothOfRelativeDimension : ∀ (k : Type) [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A],
    IsAbelianScheme A → ∃ g : ℕ, SmoothOfRelativeDimension g A.hom := by
  intro k _ A _ hA
  exact GlobalTheory.AbelianDim.exists_relDim k A hA

end GlobalTheory.AbFieldDim
