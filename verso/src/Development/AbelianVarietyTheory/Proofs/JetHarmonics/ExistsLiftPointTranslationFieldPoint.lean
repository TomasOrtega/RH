import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TranslatePullbackEigensection
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EigenEquationOfForallGeometricPoint
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecLinIffComb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Establish `hx : x.left ≫ pullback.snd G.hom f = P.hom` using `Over.w x`. Establish `hT : T.hom = (e ≫ P.hom) ≫ f`. Rewrite using `[← Over.w g, hg, ← hx]`. Simplify using `only [Category.assoc, pullback.condition]`. Set `T' : Over S'` to `Over.mk (e ≫ P.hom)`.

Set `e' : T' ⟶ P` to `Over.homMk e rfl`. Set `r' : T' ⟶ (Over.pullback f).obj G` to `Over.homMk (pullback.lift r.left (e ≫ P.hom) ((Over.w r).trans hT)) (pullback.lift_snd _ _ _)`. Establish `hr' : r'.left ≫ pullback.fst G.hom f = r.left` using `pullback.lift_fst _ _ _`. Set `U : Over.mk (T'.hom ≫ f) ⟶ T` to `Over.homMk (𝟙 T.left) ((Category.id_comp _).trans hT)`. Establish `hU : ∀ z : T ⟶ G, (U ≫ z).left = z.left` using `fun z => Category.id_comp _`.

Establish `h1 : lift e' r' ≫ translT ((Over.pullback f).obj G) x ≫ fst _ _ = e'`. Simplify using `[translT]`. Establish `h2 : lift e' r' ≫ translT ((Over.pullback f).obj G) x ≫ snd _ _ = (e' ≫ x) * r'`. Simplify using `only [translT, translPt, lift_snd, Hom.mul_def]`. Rewrite using `[← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]`.

Establish `h3` using `(isGrpPullback_pullback G f).2 T' (e' ≫ x) r' (U ≫ g) (U ≫ r) ((hU g).trans (hg.trans (Category.assoc _ _ _).symm)) ((hU r).trans hr'.symm)`. Use `⟨(lift e' r').left, congrArg (fun z => z.left) (lift_fst e' r'), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `((Category.assoc _ _ _).symm.trans (congrArg (fun z : T' ⟶ (Over.pullback f).obj G => z.left ≫ pullback.fst G.hom f) (lift_snd e' r'))).trans hr'`. Conclude with `(Category.assoc _ _ _).trans (congrArg (fun z => z.left) h1)`. Establish `h4 : ((lift e' r').left ≫ (translT ((Over.pullback f).obj G) x).left) ≫ (snd P ((Over.pullback f).obj G)).left = ((e' ≫ x) * r').left` using `(Category.assoc _ _ _).trans (congrArg (fun z => z.left) h2)`.

Use `((Category.assoc _ _ _).symm.trans (congrArg (· ≫ pullback.fst G.hom f) h4)).trans (h3.symm.trans ?_)` and prove the remaining obligations. Rewrite using `[← MonObj.comp_mul, hU, mul_comm]`.
-/
theorem exists_lift_translT_general {S S' : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (f : S' ⟶ S)
    (P : Over S') (x : P ⟶ (Over.pullback f).obj G) (T : Over S) (e : T.left ⟶ P.left) (r g : T ⟶ G)
    (hg : g.left = e ≫ x.left ≫ pullback.fst G.hom f) :
    ∃ ρ : T.left ⟶ (P ⊗ (Over.pullback f).obj G).left,
      ρ ≫ (fst P ((Over.pullback f).obj G)).left = e ∧
      ρ ≫ (snd P ((Over.pullback f).obj G)).left ≫ pullback.fst G.hom f = r.left ∧
      (ρ ≫ (translT ((Over.pullback f).obj G) x).left) ≫ (fst P ((Over.pullback f).obj G)).left = e ∧
      (ρ ≫ (translT ((Over.pullback f).obj G) x).left) ≫ (snd P ((Over.pullback f).obj G)).left ≫
        pullback.fst G.hom f = (r * g).left := by
  have hx : x.left ≫ pullback.snd G.hom f = P.hom := Over.w x
  have hT : T.hom = (e ≫ P.hom) ≫ f := by
    rw [← Over.w g, hg, ← hx]
    simp only [Category.assoc, pullback.condition]
  let T' : Over S' := Over.mk (e ≫ P.hom)
  let e' : T' ⟶ P := Over.homMk e rfl
  let r' : T' ⟶ (Over.pullback f).obj G :=
    Over.homMk (pullback.lift r.left (e ≫ P.hom) ((Over.w r).trans hT)) (pullback.lift_snd _ _ _)
  have hr' : r'.left ≫ pullback.fst G.hom f = r.left := pullback.lift_fst _ _ _
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk (𝟙 T.left) ((Category.id_comp _).trans hT)
  have hU : ∀ z : T ⟶ G, (U ≫ z).left = z.left := fun z => Category.id_comp _
  have h1 : lift e' r' ≫ translT ((Over.pullback f).obj G) x ≫ fst _ _ = e' := by
    simp [translT]
  have h2 : lift e' r' ≫ translT ((Over.pullback f).obj G) x ≫ snd _ _ = (e' ≫ x) * r' := by
    simp only [translT, translPt, lift_snd, Hom.mul_def]
    rw [← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
  have h3 := (isGrpPullback_pullback G f).2 T' (e' ≫ x) r' (U ≫ g) (U ≫ r)
    ((hU g).trans (hg.trans (Category.assoc _ _ _).symm)) ((hU r).trans hr'.symm)
  refine ⟨(lift e' r').left, congrArg (fun z => z.left) (lift_fst e' r'), ?_, ?_, ?_⟩
  · exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z : T' ⟶ (Over.pullback f).obj G => z.left ≫ pullback.fst G.hom f) (lift_snd e' r'))).trans hr'
  · exact (Category.assoc _ _ _).trans (congrArg (fun z => z.left) h1)
  · have h4 : ((lift e' r').left ≫ (translT ((Over.pullback f).obj G) x).left) ≫
        (snd P ((Over.pullback f).obj G)).left = ((e' ≫ x) * r').left :=
      (Category.assoc _ _ _).trans (congrArg (fun z => z.left) h2)
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ pullback.fst G.hom f) h4)).trans (h3.symm.trans ?_)
    rw [← MonObj.comp_mul, hU, mul_comm]

/- English proof (translation)
Introduce `R _ _ G _ _ F _ _ x T e r g hg`. Conclude with `exists_lift_translT_general G (jK R) (TFK (R := R) F) x T e r g hg`.
-/
theorem exists_lift_translT : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (T : Over (Spec (CommRingCat.of R))) (e : T.left ⟶ Spec (CommRingCat.of F)) (r g : T ⟶ G), g.left = e ≫ x.left ≫ pullback.fst G.hom (jK R) → ∃ ρ : T.left ⟶ (UnifPre.GF (G := G) F).left, ρ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = e ∧ ρ ≫ UnifPre.gFK (G := G) F = r.left ∧ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) x).left) ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = e ∧ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) x).left) ≫ UnifPre.gFK (G := G) F = (r * g).left := by
  intro R _ _ G _ _ F _ _ x T e r g hg
  exact exists_lift_translT_general G (jK R) (TFK (R := R) F) x T e r g hg

end GlobalTheory
