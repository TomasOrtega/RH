import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

open GlobalTheory.Serre in

/- English proof (translation)
Introduce `S G' G _ _ _ _ j p`. Take `⟨pr, hpr, hl⟩` from `p`. Establish `hprI : ∀ i, IsMonHom (pr i)` using `hpr`. Establish `hext : ∀ {X : Over S} (f g : X ⟶ G'), (∀ i, f ≫ pr i = g ≫ pr i) → f = g` using `fun f g h => Fan.IsLimit.hom_ext hl f g h`. Set `lf : (G ⟶ G) → (G' ⟶ G')` to `fun f => Fan.IsLimit.lift hl (fun i => pr i ≫ f)`.

Establish `hlf : ∀ (f : G ⟶ G) (i : Fin j), lf f ≫ pr i = pr i ≫ f` using `fun f i => Fan.IsLimit.fac hl _ i`. Establish `hlf' : ∀ (f : G ⟶ G) (i : Fin j) {Z : Over S} (h : G ⟶ Z), lf f ≫ pr i ≫ h = pr i ≫ f ≫ h`. Introduce `f i Z h`. Rewrite using `[← Category.assoc, hlf, Category.assoc]`. Establish `hone : lf (𝟙 G) = 𝟙 G'` using `hext _ _ (fun i => by rw [hlf]; simp)`.

Establish `hcomp : ∀ f g : G ⟶ G, lf (f ≫ g) = lf f ≫ lf g` using `fun f g => hext _ _ (fun i => by simp only [Category.assoc, hlf, hlf'])`. Establish `hmon : ∀ f : G ⟶ G, IsMonHom f → IsMonHom (lf f)`. Introduce `f hf`. Prove the components needed by the constructor for the conclusion. Use `hext _ _ (fun i => ?_)` and prove the remaining obligations.

Simplify using `only [Category.assoc, hlf, IsMonHom.one_hom]`. Use `hext _ _ (fun i => ?_)` and prove the remaining obligations. Simplify using `only [Category.assoc, hlf, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc]`. Establish `hadd : ∀ f g : G ⟶ G, lf (lift f g ≫ μ) = lift (lf f) (lf g) ≫ μ`. Introduce `f g`.

Use `hext _ _ (fun i => ?_)` and prove the remaining obligations. Simplify using `only [Category.assoc, hlf, IsMonHom.mul_hom, comp_lift_assoc, lift_map_assoc]`. Apply the tactic sequence `refine ⟨fun O _ r => ⟨⟨fun a => lf (r.act a), fun a => hmon _ (r.hom a), by try dsimp only`. Rewrite using `[r.map_one, hone],`. Apply the tactic sequence `fun a b => by try dsimp only`.

Rewrite using `[r.map_mul, hcomp],`. Apply the tactic sequence `fun a b => by try dsimp only`. Rewrite using `[r.map_add]`. Conclude with `hadd (r.act a) (r.act b)⟩,`. Use `fun a i => hlf _ i⟩,`.

Apply the tactic sequence `fun O _ r => ⟨⟨fun a => lf (r.act a), fun a => hmon _ (r.hom a), by try dsimp only`. Rewrite using `[r.one, hone],`. Apply the tactic sequence `fun a b => by try dsimp only`. Rewrite using `[r.mul, hcomp],`. Apply the tactic sequence `fun a b => by try dsimp only`.

Rewrite using `[r.add]`. Conclude with `hadd (r.act a) (r.act b)⟩,`. Use `fun a i => hlf _ i⟩⟩`.
-/
theorem exists_powAct : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j), (∀ (O : Type) [Ring O] (r : RingAct G O), ∃ r' : RingAct G' O, ∀ a i, r'.act a ≫ p.pr i = p.pr i ≫ r.act a) ∧ ∀ (O : Type) [CommRing O] (r : Geo.Tor.OAct O G), ∃ r' : Geo.Tor.OAct O G', ∀ a i, r'.act a ≫ p.pr i = p.pr i ≫ r.act a := by
  intro S G' G _ _ _ _ j p
  obtain ⟨pr, hpr, hl⟩ := p
  have hprI : ∀ i, IsMonHom (pr i) := hpr
  have hext : ∀ {X : Over S} (f g : X ⟶ G'), (∀ i, f ≫ pr i = g ≫ pr i) → f = g :=
    fun f g h => Fan.IsLimit.hom_ext hl f g h

  let lf : (G ⟶ G) → (G' ⟶ G') := fun f => Fan.IsLimit.lift hl (fun i => pr i ≫ f)
  have hlf : ∀ (f : G ⟶ G) (i : Fin j), lf f ≫ pr i = pr i ≫ f :=
    fun f i => Fan.IsLimit.fac hl _ i
  have hlf' : ∀ (f : G ⟶ G) (i : Fin j) {Z : Over S} (h : G ⟶ Z),
      lf f ≫ pr i ≫ h = pr i ≫ f ≫ h := by
    intro f i Z h
    rw [← Category.assoc, hlf, Category.assoc]
  have hone : lf (𝟙 G) = 𝟙 G' := hext _ _ (fun i => by rw [hlf]; simp)
  have hcomp : ∀ f g : G ⟶ G, lf (f ≫ g) = lf f ≫ lf g := fun f g =>
    hext _ _ (fun i => by simp only [Category.assoc, hlf, hlf'])
  have hmon : ∀ f : G ⟶ G, IsMonHom f → IsMonHom (lf f) := by
    intro f hf
    constructor
    · refine hext _ _ (fun i => ?_)
      simp only [Category.assoc, hlf, IsMonHom.one_hom]
    · refine hext _ _ (fun i => ?_)
      simp only [Category.assoc, hlf, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc]

  have hadd : ∀ f g : G ⟶ G, lf (lift f g ≫ μ) = lift (lf f) (lf g) ≫ μ := by
    intro f g
    refine hext _ _ (fun i => ?_)
    simp only [Category.assoc, hlf, IsMonHom.mul_hom, comp_lift_assoc, lift_map_assoc]
  refine ⟨fun O _ r => ⟨⟨fun a => lf (r.act a), fun a => hmon _ (r.hom a),
      by try dsimp only
         rw [r.map_one, hone],
      fun a b => by
        try dsimp only
        rw [r.map_mul, hcomp],
      fun a b => by
        try dsimp only
        rw [r.map_add]
        exact hadd (r.act a) (r.act b)⟩,
      fun a i => hlf _ i⟩,
    fun O _ r => ⟨⟨fun a => lf (r.act a), fun a => hmon _ (r.hom a),
      by try dsimp only
         rw [r.one, hone],
      fun a b => by
        try dsimp only
        rw [r.mul, hcomp],
      fun a b => by
        try dsimp only
        rw [r.add]
        exact hadd (r.act a) (r.act b)⟩,
      fun a i => hlf _ i⟩⟩

end GlobalTheory
