import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.SameB
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

/- English proof (translation)
Introduce `R _ _ I D A G _ _ U U' hM k σ σ₀ σ' f f' hσ hG hB hE e`. Take `⟨S, hS⟩` from `ReciprocityTheory.ChartRestriction.G.DVR.expandsAt_val U' e k σ f (hE e)`. Use `⟨S, fun Z x rG rB h1 h2 _ z JG J hJG hJ => ?_⟩` and prove the remaining obligations. Take `⟨h₀, h₁⟩` from `hS Z x z J hJ`. Use `clear hS hE`.

Take `⟨-, hL, -, -, hgt, hw⟩` from `hM`. Consider the cases of `U'`. Simplify using `only at hL hgt hw`. Substitute `hL hgt` using the available equality. Consider the cases of `hw`.

Consider the cases of `hσ`. Establish `eB : ∀ α, sval (f' α) rB z J = sval (f α) (x ≫ (U.gt e).pG.left) z J` using `fun α => by`. Rewrite using `[hB α Z rB z J hJ, h2]`. Use `⟨fun α hα => (eB α).trans (h₀ α hα), ?_⟩` and prove the remaining obligations. Establish `H` using `h₁ (JG (x ≫ (fstG I e G).left)) (hJG (x ≫ (fstG I e G).left))`.

Rewrite using `[hG Z rG z JG hJG, h1, Finset.sum_congr rfl fun α _ => congrArg (· * _) (eB α)]`. Use `Eq.trans ?_ H` and prove the remaining obligations. Rewrite using `[Units.val_pow_eq_pow_val, sval_of σ₀ _ z JG (fun _ => JG (x ≫ (fstG I e G).left)) (fun _ => by rw [Category.comp_id])]`. Both sides reduce to the same expression.
-/
theorem expT_of_expandsAt : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : H0 U'.LG.L k) (σ₀ : H0 U.P.L.L k) (σ' : U.SecGT (𝟙_ _) k) (f) (f'), HEq σ σ₀ → SameG σ₀ σ' → SameB f f' → (∀ e, U'.ExpandsAt e k σ f) → U.ExpT (𝟙_ _) k σ' f' := by
  intro R _ _ I D A G _ _ U U' hM k σ σ₀ σ' f f' hσ hG hB hE e
  obtain ⟨S, hS⟩ := ReciprocityTheory.ChartRestriction.G.DVR.expandsAt_val U' e k σ f (hE e)
  refine ⟨S, fun Z x rG rB h1 h2 _ z JG J hJG hJ => ?_⟩
  obtain ⟨h₀, h₁⟩ := hS Z x z J hJ
  clear hS hE
  obtain ⟨-, hL, -, -, hgt, hw⟩ := hM
  cases U'
  dsimp only at hL hgt hw
  subst hL hgt
  cases hw
  cases hσ
  have eB : ∀ α, sval (f' α) rB z J = sval (f α) (x ≫ (U.gt e).pG.left) z J := fun α => by
    rw [hB α Z rB z J hJ, h2]
  refine ⟨fun α hα => (eB α).trans (h₀ α hα), ?_⟩
  have H := h₁ (JG (x ≫ (fstG I e G).left)) (hJG (x ≫ (fstG I e G).left))
  rw [hG Z rG z JG hJG, h1, Finset.sum_congr rfl fun α _ => congrArg (· * _) (eB α)]
  refine Eq.trans ?_ H
  rw [Units.val_pow_eq_pow_val, sval_of σ₀ _ z JG (fun _ => JG (x ≫ (fstG I e G).left)) (fun _ => by rw [Category.comp_id])]
  rfl

end GlobalTheory.UU
