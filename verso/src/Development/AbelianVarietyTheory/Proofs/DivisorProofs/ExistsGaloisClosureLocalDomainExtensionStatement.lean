import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisClosureLocalDomainExtension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsGaloisClosureLocalDomainExtension.lean&line=89#L89)
-/
theorem _root_.GlobalTheory.T.exists_galois_closure_local_domain_extension : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → ∃ (R'' : Type) (_ : CommRing R'') (_ : IsDomain R'') (_ : IsLocalRing R'') (σ : R' →+* R''), FinExt σ ∧ IsLocalHom σ ∧ FinExt (σ.comp ρ) ∧ IsGal (σ.comp ρ) := by
  first | exact @GlobalTheory.GalClosure.exists_galois_finExt_isLocalHom | exact GlobalTheory.GalClosure.exists_galois_finExt_isLocalHom | (intros; apply GlobalTheory.GalClosure.exists_galois_finExt_isLocalHom <;> assumption)
