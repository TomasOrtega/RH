import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianIsoOfExtensionIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSemiabelianIsoOfExtensionIso.lean&line=238#L238)
-/
theorem _root_.GlobalTheory.T.semiabelian_iso_of_extension_iso : ∀ (k : Type) [Field k] [IsAlgClosed k] (E E' : SplitExt (Sp k)) (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'] (β : E.B ≅ E'.B) (e : E.X ≃+ E'.X), IsMonHom β.hom → IsSemiAbelian G → IsSemiAbelian G' → (∀ χ, LBIso (E.O χ).L ((E'.O (e χ)).L.pull β.hom.left)) → E.IsGt G → E'.IsGt G' → ∃ i : G ≅ G', IsMonHom i.hom := by
  first | exact @GlobalTheory.ExtUnique.exists_iso_isMonHom_of_isGt | exact GlobalTheory.ExtUnique.exists_iso_isMonHom_of_isGt | (intros; apply GlobalTheory.ExtUnique.exists_iso_isMonHom_of_isGt <;> assumption)
