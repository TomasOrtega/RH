import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiabelianExtensionDvr
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsSemiabelianExtensionDvr.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_semiabelian_extension_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ Y.X), Set.range (jK W ≫ χ) ⊆ Set.range Y.j → ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (ι : W →+* W') (t' : SAB H (Sp W')) (_ : SABMap t' Y.t (spMap ι ≫ χ)) (_ : PELUnif (maximalIdeal W') t'), CDvr W' ∧ Function.Injective ι ∧ IsLocalHom ι := by
  first | exact @GlobalTheory.TraitUnif.exists_ext_pelUnif | exact GlobalTheory.TraitUnif.exists_ext_pelUnif | (intros; apply GlobalTheory.TraitUnif.exists_ext_pelUnif <;> assumption)
