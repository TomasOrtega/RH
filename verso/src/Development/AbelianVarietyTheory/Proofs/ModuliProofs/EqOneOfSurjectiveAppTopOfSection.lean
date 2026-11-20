import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

/- English proof (translation)
Take `⟨b, rfl⟩` from `hs a`. Establish `e : o.appTop.hom (p.appTop.hom b) = b`. Rewrite using `[← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, ho, Scheme.Hom.id_appTop]`. Both sides reduce to the same expression. Rewrite using `[e.symm.trans ha, map_one]`.
-/
theorem eq_one_of_surjective_appTop_of_section {X S : Scheme.{0}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
    (hs : Function.Surjective p.appTop.hom) (a : Γ(X, ⊤)) (ha : o.appTop.hom a = 1) : a = 1 := by
  obtain ⟨b, rfl⟩ := hs a
  have e : o.appTop.hom (p.appTop.hom b) = b := by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, ho, Scheme.Hom.id_appTop]
    rfl
  rw [e.symm.trans ha, map_one]

/- English proof (translation)
Introduce `hG E _ _ _ H S S' t t' f φ hp gp ⟨w, hw⟩ hact`. Take `⟨w', hw', Hr⟩` from `TripleMap.exists_rigidified t.PP.isLB t'.PP.isLB w ((isGen_iff w).1 hw) (eSec t.G) (eSec t'.G) t'.G.hom (Over.w _) f (cubeMapOf gp).e_comm t.PP.rig t.PP.rigGen t'.PP.rig t'.PP.rigGen`. Establish `hp' : IsProper t'.G.hom` using `MorphismProperty.of_isPullback gp.1 hp`. Establish `hA` using `AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi`. Establish `hA₃` using `AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA)`.

Use `⟨⟨cubeMapOf gp, gp, rfl, hact, (isPullCubical_iff _ _ _).2 ⟨w', hw', Hr, TripleMap.pmaps_cubical gp t.cub t'.cub hw' fun a ha => ?_⟩⟩, rfl⟩` and prove the remaining obligations. Set `o` to `lift (1 : 𝟙_ (Over S') ⟶ t'.G) (lift (1 : 𝟙_ (Over S') ⟶ t'.G) (1 : 𝟙_ (Over S') ⟶ t'.G))`. Establish `h₁ : pullU o.left ⊤ a = 1` using `unit_ext fun y _ => (gm_pull (𝟙 _) o.left y ⊤ trivial a).trans ((congrArg (fun q => gm q y ⊤ a) (Category.id_comp _)).trans ((ha y).trans (map_one _).symm))`. Conclude with `Units.ext (eq_one_of_surjective_appTop_of_section (G3 t'.G).hom o.left (Over.w o) (hG _ _ hA₃).2 a.val (congrArg Units.val h₁))`.
-/
theorem exists_sabMap_of_isProper_of_lbIso : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (φ : t'.G.left ⟶ t.G.left), IsProper t.G.hom → IsGrpPullback t'.G t.G f φ → LBIso t'.PP.L (t.PP.L.pull φ) → (∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left) → ∃ m : SABMap t' t f, m.φ = φ := by
  intro hG E _ _ _ H S S' t t' f φ hp gp ⟨w, hw⟩ hact
  obtain ⟨w', hw', Hr⟩ := TripleMap.exists_rigidified t.PP.isLB t'.PP.isLB w ((isGen_iff w).1 hw) (eSec t.G)
    (eSec t'.G) t'.G.hom (Over.w _) f (cubeMapOf gp).e_comm t.PP.rig t.PP.rigGen t'.PP.rig t'.PP.rigGen
  have hp' : IsProper t'.G.hom := MorphismProperty.of_isPullback gp.1 hp
  have hA := AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi
  have hA₃ := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA)
  refine ⟨⟨cubeMapOf gp, gp, rfl, hact, (isPullCubical_iff _ _ _).2 ⟨w', hw', Hr,
    TripleMap.pmaps_cubical gp t.cub t'.cub hw' fun a ha => ?_⟩⟩, rfl⟩
  let o := lift (1 : 𝟙_ (Over S') ⟶ t'.G) (lift (1 : 𝟙_ (Over S') ⟶ t'.G) (1 : 𝟙_ (Over S') ⟶ t'.G))
  have h₁ : pullU o.left ⊤ a = 1 := unit_ext fun y _ =>
    (gm_pull (𝟙 _) o.left y ⊤ trivial a).trans ((congrArg (fun q => gm q y ⊤ a) (Category.id_comp _)).trans
      ((ha y).trans (map_one _).symm))
  exact Units.ext (eq_one_of_surjective_appTop_of_section (G3 t'.G).hom o.left (Over.w o) (hG _ _ hA₃).2 a.val
    (congrArg Units.val h₁))

end GlobalTheory
