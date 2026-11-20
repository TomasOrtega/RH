import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGlue

/- English proof (translation)
Set `T : Z → Scheme.{0}` to `fun z => Sp (AlgebraicClosure (Z.residueField z))`. Set `pt : ∀ z, T z ⟶ Z` to `fun z => spMap (algebraMap (Z.residueField z) (AlgebraicClosure (Z.residueField z))) ≫ Z.fromSpecResidueField z`. Set `m : (∐ T) ⟶ Z` to `Sigma.desc pt`. Establish `hs : Function.Surjective m.base`. Introduce `z`.

Use `⟨(Sigma.ι T z).base default, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, Sigma.ι_desc]`. Simplify using `only [pt, Scheme.Hom.comp_apply]`. Conclude with `Scheme.fromSpecResidueField_apply _ _`. Establish `: IsDominant m` using `⟨hs.denseRange⟩`.

Use `ext_of_isDominant_of_isSeparated q hq m ?_` and prove the remaining obligations. Use `Sigma.hom_ext _ _ fun z => ?_` and prove the remaining obligations. Simplify using `only [m, Sigma.ι_desc_assoc]`. Conclude with `h _ (pt z)`.
-/
theorem hom_ext_of_geometric {Z P S : Scheme.{0}} [IsReduced Z] (q : P ⟶ S) [IsSeparated q] (a b : Z ⟶ P)
    (hq : a ≫ q = b ≫ q)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ Z), y ≫ a = y ≫ b) : a = b := by
  let T : Z → Scheme.{0} := fun z => Sp (AlgebraicClosure (Z.residueField z))
  let pt : ∀ z, T z ⟶ Z := fun z =>
    spMap (algebraMap (Z.residueField z) (AlgebraicClosure (Z.residueField z))) ≫ Z.fromSpecResidueField z
  let m : (∐ T) ⟶ Z := Sigma.desc pt
  have hs : Function.Surjective m.base := by
    intro z
    refine ⟨(Sigma.ι T z).base default, ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
    simp only [pt, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have : IsDominant m := ⟨hs.denseRange⟩
  refine ext_of_isDominant_of_isSeparated q hq m ?_
  refine Sigma.hom_ext _ _ fun z => ?_
  simp only [m, Sigma.ι_desc_assoc]
  exact h _ (pt z)

/- English proof (translation)
Introduce `o _ n X _ s I W f hW hf hg`. Establish `: IsSeparated (PSpace.str o n)`. Use `isProper_str o n` as an intermediate fact. Use `infer_instance`. Set `𝒰` to `X.openCoverOfIsOpenCover W hW`.

Establish `hc : ∀ a b, pullback.fst (W a).ι (W b).ι ≫ f a = pullback.snd (W a).ι (W b).ι ≫ f b`. Introduce `a b`. Establish `: IsReduced (pullback (W a).ι (W b).ι)` using `isReduced_of_isOpenImmersion (pullback.fst _ _ ≫ (W a).ι)`. Use `hom_ext_of_geometric (PSpace.str o n) _ _ ?_ fun K _ _ y => ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, hf, hf, pullback.condition_assoc]`.

Rewrite using `[← Category.assoc, ← Category.assoc]`. Conclude with `hg a b K _ _ (by rw [Category.assoc, Category.assoc, pullback.condition])`. Establish `he : ∀ a, (W a).ι ≫ 𝒰.glueMorphisms f hc = f a` using `fun a => 𝒰.ι_glueMorphisms f hc a`. Use `⟨𝒰.glueMorphisms f hc, 𝒰.hom_ext _ _ fun (a : I) => ?_, he⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(W a).ι ≫ _ = (W a).ι ≫ _`.

Rewrite using `[← Category.assoc, he, hf]`.
-/
theorem glue_geom : ∀ (o : Type) [CommRing o] (n : ℕ) (X : Scheme.{0}) [IsReduced X] (s : X ⟶ Sp o) (I : Type)
    (W : I → X.Opens) (f : ∀ i, (W i).toScheme ⟶ PSpace o n), (⨆ i, W i) = ⊤ →
    (∀ i, f i ≫ PSpace.str o n = (W i).ι ≫ s) →
    (∀ i j (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ (W i).toScheme) (y' : Sp K ⟶ (W j).toScheme),
      y ≫ (W i).ι = y' ≫ (W j).ι → y ≫ f i = y' ≫ f j) →
    ∃ g : X ⟶ PSpace o n, g ≫ PSpace.str o n = s ∧ ∀ i, (W i).ι ≫ g = f i := by
  intro o _ n X _ s I W f hW hf hg
  have : IsSeparated (PSpace.str o n) := by
    have := isProper_str o n
    infer_instance
  let 𝒰 := X.openCoverOfIsOpenCover W hW
  have hc : ∀ a b, pullback.fst (W a).ι (W b).ι ≫ f a = pullback.snd (W a).ι (W b).ι ≫ f b := by
    intro a b
    have : IsReduced (pullback (W a).ι (W b).ι) :=
      isReduced_of_isOpenImmersion (pullback.fst _ _ ≫ (W a).ι)
    refine hom_ext_of_geometric (PSpace.str o n) _ _ ?_ fun K _ _ y => ?_
    · rw [Category.assoc, Category.assoc, hf, hf, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc]
      exact hg a b K _ _ (by rw [Category.assoc, Category.assoc, pullback.condition])
  have he : ∀ a, (W a).ι ≫ 𝒰.glueMorphisms f hc = f a := fun a => 𝒰.ι_glueMorphisms f hc a
  refine ⟨𝒰.glueMorphisms f hc, 𝒰.hom_ext _ _ fun (a : I) => ?_, he⟩
  change (W a).ι ≫ _ = (W a).ι ≫ _
  rw [← Category.assoc, he, hf]

end GlobalTheory.ThetaGlue
