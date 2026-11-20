import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp)

namespace GlobalTheory.CompanionTheory.FlatFactor

/- English proof (translation)
Establish `key : ∀ (B : CommRingCat.{0}) (j₀ : Spec B ⟶ W.left), j₀ ≫ u.left = j₀ ≫ v.left`. Introduce `B j₀`. Use `letI : Algebra R B := (Spec.preimage (j₀ ≫ W.hom)).hom.toAlgebra`. Set `j : sp (R₀` to `R) B ⟶ W := Over.homMk j₀ (Spec.map_preimage (j₀ ≫ W.hom)).symm`. Conclude with `congrArg CommaMorphism.left (h B j)`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Conclude with `Scheme.Cover.hom_ext W.left.affineCover _ _ fun i => key _ _`.
-/
theorem ext_of_affine_points {R : Type} [CommRing R] {W X : Over (Sp R)} (u v : W ⟶ X)
    (h : ∀ (S : Type) [CommRing S] [Algebra R S] (t : sp (R₀ := R) S ⟶ W), t ≫ u = t ≫ v) : u = v := by
  have key : ∀ (B : CommRingCat.{0}) (j₀ : Spec B ⟶ W.left), j₀ ≫ u.left = j₀ ≫ v.left := by
    intro B j₀
    letI : Algebra R B := (Spec.preimage (j₀ ≫ W.hom)).hom.toAlgebra
    let j : sp (R₀ := R) B ⟶ W := Over.homMk j₀ (Spec.map_preimage (j₀ ≫ W.hom)).symm
    exact congrArg CommaMorphism.left (h B j)
  apply Over.OverMorphism.ext
  exact Scheme.Cover.hom_ext W.left.affineCover _ _ fun i => key _ _

/- English proof (translation)
Use `ext_of_affine_points _ _ fun S _ _ t => ?_` and prove the remaining obligations. Establish `h1 : ((t ≫ a) / (t ≫ b)) ≫ l = 1`. Rewrite using `[GrpObj.div_comp, Category.assoc, Category.assoc, h, div_self']`. Establish `h2` using `hk S _ h1`. Rewrite `h2` using `[GrpObj.div_comp, div_eq_one]`.

Simplify using `using h2`.
-/
theorem comp_eq_of_comp_eq {R : Type} [CommRing R] {A B A' : Over (Sp R)} [GrpObj A] [GrpObj B] [GrpObj A']
    (l : A ⟶ B) (f : A ⟶ A') [IsMonHom l] [IsMonHom f]
    (hk : ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A), z ≫ l = 1 → z ≫ f = 1)
    {W : Over (Sp R)} (a b : W ⟶ A) (h : a ≫ l = b ≫ l) : a ≫ f = b ≫ f := by
  refine ext_of_affine_points _ _ fun S _ _ t => ?_
  have h1 : ((t ≫ a) / (t ≫ b)) ≫ l = 1 := by
    rw [GrpObj.div_comp, Category.assoc, Category.assoc, h, div_self']
  have h2 := hk S _ h1
  rw [GrpObj.div_comp, div_eq_one] at h2
  simpa using h2

/- English proof (translation)
Introduce `R _ A B A' _ _ _ l f hl hf hfl hsl hql hk`. Establish `hc : ∀ {Z : Scheme.{0}} (g g' : Z ⟶ A.left), g ≫ l.left = g' ≫ l.left → g ≫ f.left = g' ≫ f.left`. Introduce `Z g g' h`. Establish `hw : g' ≫ A.hom = g ≫ A.hom`. Rewrite using `[← Over.w l, ← Category.assoc, ← h, Category.assoc]`.

Use `comp_eq_of_comp_eq l f hk (W := Over.mk (g ≫ A.hom)) (Over.homMk g rfl) (Over.homMk g' hw) (Over.OverMorphism.ext h)` as an intermediate fact. Conclude with `congrArg CommaMorphism.left this`. Establish `hfac` using `EffectiveEpi.fac l.left f.left hc`. Set `g : B ⟶ A'` to `Over.homMk (EffectiveEpi.desc l.left f.left hc) (by`. Rewrite using `[← cancel_epi l.left, ← Category.assoc, hfac, Over.w, Over.w])`.

Establish `hg : l ≫ g = f` using `Over.OverMorphism.ext hfac`. Use `⟨g, ⟨?_, ?_⟩, hg⟩` and prove the remaining obligations. Rewrite using `[← IsMonHom.one_hom l, Category.assoc, hg, IsMonHom.one_hom]`. Use `GlobalTheory.FlatQuotient.epi_tensorHom l l` as an intermediate fact. Rewrite using `[← cancel_epi (l ⊗ₘ l), ← IsMonHom.mul_hom_assoc, hg, tensorHom_comp_tensorHom_assoc, hg, IsMonHom.mul_hom]`.
-/
theorem factorThroughFF : PositivityTheory.Tls2.Zar3.Ch1.FactorThroughFF := by
  intro R _ A B A' _ _ _ l f hl hf hfl hsl hql hk
  have hc : ∀ {Z : Scheme.{0}} (g g' : Z ⟶ A.left), g ≫ l.left = g' ≫ l.left →
      g ≫ f.left = g' ≫ f.left := by
    intro Z g g' h
    have hw : g' ≫ A.hom = g ≫ A.hom := by
      rw [← Over.w l, ← Category.assoc, ← h, Category.assoc]
    have := comp_eq_of_comp_eq l f hk (W := Over.mk (g ≫ A.hom))
      (Over.homMk g rfl) (Over.homMk g' hw) (Over.OverMorphism.ext h)
    exact congrArg CommaMorphism.left this
  have hfac := EffectiveEpi.fac l.left f.left hc
  let g : B ⟶ A' := Over.homMk (EffectiveEpi.desc l.left f.left hc) (by
    rw [← cancel_epi l.left, ← Category.assoc, hfac, Over.w, Over.w])
  have hg : l ≫ g = f := Over.OverMorphism.ext hfac
  refine ⟨g, ⟨?_, ?_⟩, hg⟩
  · rw [← IsMonHom.one_hom l, Category.assoc, hg, IsMonHom.one_hom]
  · have := GlobalTheory.FlatQuotient.epi_tensorHom l l
    rw [← cancel_epi (l ⊗ₘ l), ← IsMonHom.mul_hom_assoc, hg, tensorHom_comp_tensorHom_assoc, hg,
      IsMonHom.mul_hom]

end GlobalTheory.CompanionTheory.FlatFactor
