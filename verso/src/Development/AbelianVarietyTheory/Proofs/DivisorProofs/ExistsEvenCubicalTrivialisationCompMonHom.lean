import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.CubTrivComp

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem val_cast {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (h ▸ t : LB.Gen (LB.LinComb L φ' ε)) r z J = val t r z J := by
  subst h; rfl

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `ht`.
-/
theorem isGen_cast {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : φ = φ') {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) :
    (h ▸ t : LB.Gen (LB.LinComb L φ' ε)).IsGen := by
  subst h; exact ht

/- English proof (translation)
Introduce `S G H H' _ _ _ _ P i e he σ hσ`. Establish `hφ : (fun k => e.left ≫ (![i.left, (1 : H' ⟶ G).left] : Fin 2 → (H'.left ⟶ G.left)) k) = ![(e ≫ i).left, (1 : H ⟶ G).left]`. Use function extensionality and compare the values at `k`. Use `fin_cases k`. Conclude with `(Over.comp_left _ _ _ e i).symm`.

Use `show e.left ≫ (1 : H' ⟶ G).left = (1 : H ⟶ G).left`. Rewrite using `[← Over.comp_left, MonObj.comp_one]`. Set `s₁ : LB.Gen (LB.LinComb P.L.L (K` to `Fin 2) ![(e ≫ i).left, (1 : H ⟶ G).left] ![1, -1]) := hφ ▸ LB.pullGen P.L.L _ _ σ.s e.left`. Establish `v : ∀ {T : Over S} (x : T ⟶ H) {z : T.left} {J}, Good P.L.L z J → val s₁ x.left z J = val σ.s (x ≫ e).left z J` using `fun x z J hJ => (val_cast hφ _ _ _ _).trans ((val_pull hJ σ.s e.left x.left).trans (by rw [Over.comp_left]))`. Use `⟨⟨s₁, isGen_cast hφ (DVR.pullGen_isGen _ _ _ _ σ.gen _), fun T x y u z J hJ => ?_⟩, fun T x z J hJ => ?_⟩` and prove the remaining obligations.

Establish `c` using `σ.cub T (x ≫ e) (y ≫ e) (u ≫ e) z J hJ`. Simplify using `only [← MonObj.mul_comp, Category.assoc] at c`. Simplify using `only [v _ hJ]`. Conclude with `c`. Use `show val s₁ (x⁻¹).left z J = val P.sym (x ≫ e ≫ i).left z J * val s₁ x.left z J`.

Rewrite using `[v _ hJ, v _ hJ, GrpObj.inv_comp, hσ T (x ≫ e) z J hJ, Category.assoc]`.
-/
theorem exists_even_comp : ∀ (S : Scheme.{0}) (G H H' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj H] [GrpObj H']
    (P : GlobalTheory.UU.CP G) (i : H' ⟶ G) (e : H ⟶ H'), IsMonHom e → ∀ σ : GlobalTheory.UU.CubTriv P.c i,
    GlobalTheory.UU.CubTriv.Even (P := P) σ → ∃ σ₁ : GlobalTheory.UU.CubTriv P.c (e ≫ i), GlobalTheory.UU.CubTriv.Even (P := P) σ₁ := by
  intro S G H H' _ _ _ _ P i e he σ hσ
  have hφ : (fun k => e.left ≫ (![i.left, (1 : H' ⟶ G).left] : Fin 2 → (H'.left ⟶ G.left)) k) =
      ![(e ≫ i).left, (1 : H ⟶ G).left] := by
    funext k
    fin_cases k
    · exact (Over.comp_left _ _ _ e i).symm
    · show e.left ≫ (1 : H' ⟶ G).left = (1 : H ⟶ G).left
      rw [← Over.comp_left, MonObj.comp_one]
  let s₁ : LB.Gen (LB.LinComb P.L.L (K := Fin 2) ![(e ≫ i).left, (1 : H ⟶ G).left] ![1, -1]) :=
    hφ ▸ LB.pullGen P.L.L _ _ σ.s e.left
  have v : ∀ {T : Over S} (x : T ⟶ H) {z : T.left} {J}, Good P.L.L z J →
      val s₁ x.left z J = val σ.s (x ≫ e).left z J := fun x z J hJ =>
    (val_cast hφ _ _ _ _).trans ((val_pull hJ σ.s e.left x.left).trans (by rw [Over.comp_left]))
  refine ⟨⟨s₁, isGen_cast hφ (DVR.pullGen_isGen _ _ _ _ σ.gen _), fun T x y u z J hJ => ?_⟩, fun T x z J hJ => ?_⟩
  · have c := σ.cub T (x ≫ e) (y ≫ e) (u ≫ e) z J hJ
    simp only [← MonObj.mul_comp, Category.assoc] at c
    simp only [v _ hJ]
    exact c
  · show val s₁ (x⁻¹).left z J = val P.sym (x ≫ e ≫ i).left z J * val s₁ x.left z J
    rw [v _ hJ, v _ hJ, GrpObj.inv_comp, hσ T (x ≫ e) z J hJ, Category.assoc]

end GlobalTheory.CubTrivComp
