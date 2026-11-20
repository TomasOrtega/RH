import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeightOnePrimeEtaleStalkComap
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FHeightOnePrimeEtaleStalkComap.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.height_one_prime_etale_stalk_comap : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → Q.comap (Scheme.stalkClosedPointTo ξ).hom ≠ ⊥ → (Q.comap (Scheme.stalkClosedPointTo ξ).hom).map ((algebraMap R (Localization.AtPrime Q)).comp (Scheme.stalkClosedPointTo ξ).hom) = maximalIdeal (Localization.AtPrime Q) := by
  first | exact @GlobalTheory.FibreUnram.stalk_map_comap_eq_maximalIdeal | exact GlobalTheory.FibreUnram.stalk_map_comap_eq_maximalIdeal | (intros; apply GlobalTheory.FibreUnram.stalk_map_comap_eq_maximalIdeal <;> assumption)
