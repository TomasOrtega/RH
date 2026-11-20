import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleLocalExtResidueFieldSeparable
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFiniteEtaleLocalExtResidueFieldSeparable.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_finiteEtale_local_ext_residueField_separable : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (k' : Type) [Field k'] [Algebra (ResidueField R) k'] [Module.Finite (ResidueField R) k'] [Algebra.IsSeparable (ResidueField R) k'], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (σ : k' →+* ResidueField R'), FinExt ρ ∧ ρ.Etale ∧ σ.comp ((algebraMap (ResidueField R) k').comp (residue R)) = (residue R').comp ρ := by
  first | exact @GlobalTheory.Mum.exists_finExt_etale_of_isSeparable | exact GlobalTheory.Mum.exists_finExt_etale_of_isSeparable | (intros; apply GlobalTheory.Mum.exists_finExt_etale_of_isSeparable <;> assumption)
