import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFibreClosedFibrePointSubsetOpenPart
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSteinFibreClosedFibrePointSubsetOpenPart.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.steinFibre_closedFibre_point_subset_open_part : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∀ (H' : E.H.toScheme.Opens) (X'' : Scheme.{0}) (ν : X'' ⟶ pullback (PSpace.str R E.N) M.π) (i : H'.toScheme ⟶ X'') (P'' : Scheme.{0}) (a'' : X'' ⟶ P'') (b'' : P'' ⟶ PSpace R E.N), IsFinite ν → IsOpenImmersion i → i ≫ ν = H'.ι ≫ pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over → a'' ≫ b'' = ν ≫ pullback.fst (PSpace.str R E.N) M.π → IsFinite b'' → IsProper a'' → (∀ y : P'', _root_.IsPreconnected {x : X'' | a'' x = y}) → (∀ h : E.H.toScheme, M.π (G'.hom (E.H.ι h)) = closedPoint R → h ∈ H') → ∀ z : H'.toScheme, M.π (G'.hom (E.H.ι (H'.ι z))) = closedPoint R → ∀ w : X'', a'' w = a'' (i z) → w ∈ Set.range i := by
  first | exact @GlobalTheory.Mum.steinFibre_subset_range | exact GlobalTheory.Mum.steinFibre_subset_range | (intros; apply GlobalTheory.Mum.steinFibre_subset_range <;> assumption)
