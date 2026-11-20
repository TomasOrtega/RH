import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmpleD

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

/- English proof (translation)
Apply the tactic sequence `fin_cases i <;> simp [fourfoldProductLift, prj]`.
-/
theorem g4lift_prj {X G : Over S} (c : Fin 4 → (X ⟶ G)) (i : Fin 4) : fourfoldProductLift c ≫ prj G i = c i := by
  fin_cases i <;> simp [fourfoldProductLift, prj]

/- English proof (translation)
The claim follows from `g4lift_prj c i`.
-/
@[reassoc] theorem g4lift_prj' {X G : Over S} (c : Fin 4 → (X ⟶ G)) (i : Fin 4) : fourfoldProductLift c ≫ prj G i = c i :=
  g4lift_prj c i

/- English proof (translation)
Establish `h0` using `h 0`. Establish `h1` using `h 1`. Establish `h2` using `h 2`. Establish `h3` using `h 3`. Simplify using `only [prj] at h0 h1 h2 h3`.

Apply the tactic sequence `refine CartesianMonoidalCategory.hom_ext _ _ h0 (CartesianMonoidalCategory.hom_ext _ _ ?_ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)) <;> simpa only [Category.assoc] using ‹_›`.
-/
theorem fourfold_product_ext {X G : Over S} {f f' : X ⟶ G4 G} (h : ∀ i, f ≫ prj G i = f' ≫ prj G i) : f = f' := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [prj] at h0 h1 h2 h3
  refine CartesianMonoidalCategory.hom_ext _ _ h0 (CartesianMonoidalCategory.hom_ext _ _ ?_
    (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)) <;> simpa only [Category.assoc] using ‹_›

instance prj.isMonHom (G : Over S) [GrpObj G] (i : Fin 4) : IsMonHom (prj G i) := by
  fin_cases i <;> simp only [prj] <;> infer_instance

def precompMH {X Y G : Over S} [GrpObj G] (f : X ⟶ Y) : (Y ⟶ G) →* (X ⟶ G) where
  toFun g := f ≫ g
  map_one' := MonObj.comp_one f
  map_mul' a b := MonObj.comp_mul f a b

/- English proof (translation)
The claim follows from `map_zpow (precompMH f) g k`.
-/
theorem comp_zpow' {X Y G : Over S} [GrpObj G] (f : X ⟶ Y) (g : Y ⟶ G) (k : ℤ) : f ≫ g ^ k = (f ≫ g) ^ k :=
  map_zpow (precompMH f) g k

/- English proof (translation)
The claim follows from `map_inv (precompMH f) g`.
-/
theorem comp_inv' {X Y G : Over S} [GrpObj G] (f : X ⟶ Y) (g : Y ⟶ G) : f ≫ g⁻¹ = (f ≫ g)⁻¹ :=
  map_inv (precompMH f) g

/- English proof (translation)
The claim follows from `map_pow (precompMH f) g k`.
-/
theorem comp_pow' {X Y G : Over S} [GrpObj G] (f : X ⟶ Y) (g : Y ⟶ G) (k : ℕ) : f ≫ g ^ k = (f ≫ g) ^ k :=
  map_pow (precompMH f) g k

def postcompMH {X G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f] : (X ⟶ G) →* (X ⟶ H) where
  toFun g := g ≫ f
  map_one' := MonObj.one_comp f
  map_mul' a b := MonObj.mul_comp a b f

/- English proof (translation)
The claim follows from `map_pow (postcompMH f) g k`.
-/
theorem pow_comp' {X G H : Over S} [GrpObj G] [GrpObj H] (g : X ⟶ G) (f : G ⟶ H) [IsMonHom f] (k : ℕ) :
    (g ^ k) ≫ f = (g ≫ f) ^ k :=
  map_pow (postcompMH f) g k

/- English proof (translation)
Simplify using `[Fin.prod_univ_four, MonObj.comp_mul, comp_zpow']`.
-/
theorem comp_prod_zpow {X Y G : Over S} [GrpObj G] [IsCommMonObj G] (f : X ⟶ Y) (c : Fin 4 → (Y ⟶ G))
    (k : Fin 4 → ℤ) : f ≫ (∏ j, c j ^ k j) = ∏ j, (f ≫ c j) ^ k j := by
  simp [Fin.prod_univ_four, MonObj.comp_mul, comp_zpow']

/- English proof (translation)
Apply `fourfold_product_ext` to reduce the goal to its premises. Introduce `i`. Rewrite using `[Category.assoc, eMap, g4lift_prj]`. Use `ext1`. Rewrite using `[Category.assoc, lift_fst, Category.assoc, pow_comp', Category.id_comp, MonObj.comp_mul, comp_inv', comp_prod_zpow]`.

Simplify using `only [← Category.assoc, eMap', g4lift_prj, lift_fst, lift_snd]`. Simplify using `only [mul_inv_cancel_right]`. Rewrite using `[Category.assoc, lift_snd, Category.assoc, pow_comp', Category.id_comp, comp_pow', ← Category.assoc, eMap', g4lift_prj, lift_snd]`.
-/
theorem eMap'_comp_eMap (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) :
    eMap' mu α m ≫ eMap mu α m = 𝟙 (G4 (A ⊗ B)) ^ (2 * m) := by
  apply fourfold_product_ext
  intro i
  rw [Category.assoc, eMap, g4lift_prj]
  ext1
  · rw [Category.assoc, lift_fst, Category.assoc, pow_comp', Category.id_comp, MonObj.comp_mul, comp_inv',
      comp_prod_zpow]
    simp only [← Category.assoc, eMap', g4lift_prj, lift_fst, lift_snd]
    simp only [mul_inv_cancel_right]
  · rw [Category.assoc, lift_snd, Category.assoc, pow_comp', Category.id_comp, comp_pow', ← Category.assoc, eMap',
      g4lift_prj, lift_snd]

end PositivityTheory.PrwZar
