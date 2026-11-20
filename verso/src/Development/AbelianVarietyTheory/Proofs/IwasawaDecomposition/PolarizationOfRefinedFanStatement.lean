import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationOfRefinedFan
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ChartExtend.extend` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPolarizationOfRefinedFan.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.polarization_of_refined_fan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ)
    (φ : InvFun (𝓞 E)) (d k : ℕ) (DX : GlobalTheory.EffCartierData X.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs →
    Refines H (min D.p D.q) φs 𝒩 φ → IsPol (comb d (resInt _ φs) 0 φ) k X DX →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (mξ : SABMap t Y.t ξ)
      (P : PELUnif (maximalIdeal R) t) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X),
      IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom →
      ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso →
      ConeO H φ P.D.toPre.X m γ → InCone P.D.toPre γ →
      ∀ y : Sp (FractionRing R) ⟶ Xo.XF c, y ≫ Y.j = jK R ≫ ξ → ∃ χ : Sp R ⟶ X.X, jK R ≫ χ = y ≫ X.j := by
  first | exact @GlobalTheory.ChartExtend.extend | exact GlobalTheory.ChartExtend.extend | (intros; apply GlobalTheory.ChartExtend.extend <;> assumption)
