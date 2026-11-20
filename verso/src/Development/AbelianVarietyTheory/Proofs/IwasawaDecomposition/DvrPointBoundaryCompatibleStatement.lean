import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrPointBoundaryCompatible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMem
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FDvrPointBoundaryCompatible.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.dvr_point_boundary_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X.X) (tR : SAB H (Sp R)) (_ : SABMap tR X.t ξ) (PR : PELUnif (maximalIdeal R) tR), IsCN R → PR.TorsionIso → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ¬ (∀ p : ℕ, p.Prime → IsUnit (p : W)) → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ Z.X) (t : SAB H (Sp W)) (_ : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be : LinearMap.BilinForm ℤ P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (f : W →+* V) (ψ : R →+* V), Function.Injective f → IsLocalHom f → IsLocalHom ψ → Irreducible (f ϖ) → spMap f ≫ χ ≫ π = spMap ψ ≫ ξ → Set.range (jK V ≫ spMap ψ ≫ ξ) ⊆ Set.range X.j → ∃ ε : PR.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X, ∀ y, ∃ (r : R) (n : ℕ), PsiCoord PR.D.toPre y r ∧ be (ε y) (ε y) = 2 * n ∧ Associated (ψ r) (f ϖ ^ n) := by
  first | exact @GlobalTheory.TraitBlowForm.main | exact GlobalTheory.TraitBlowForm.main | (intros; apply GlobalTheory.TraitBlowForm.main <;> assumption)
