import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMonHomPointedSplitExtToAbelianVarietyStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Establish `key : ∀ (a : G ⟶ G ⊗ G), a ≫ t = 1 → ∀ χ : X, a.left.appTop.hom (splitTorusPointsEquiv (Sp K) X (G ⊗ G) t (Multiplicative.ofAdd χ)).val = 1`. Introduce `a ha χ`. Use `splitTorusPointsEquiv_val (Sp K) X G (a ≫ t) χ` as an intermediate fact. Rewrite `this` using `[Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ha, map_one]`. Rewrite using `[splitTorusPointsEquiv_val]`.

Conclude with `this.symm`. Apply `(splitTorusPointsEquiv (Sp K) X (G ⊗ G)).injective` to reduce the goal to its premises. Rewrite using `[map_one]`. Use extensionality with `χ`. Conclude with `unit_eq_one_of_axes_of_isGt K E G h _ (Units.isUnit _) (key _ h₁ χ) (key _ h₂ χ)`.
-/
theorem splitTorus_point_eq_one_of_axes (K : Type) [Field K] [IsAlgClosed K] (E : SplitExt (Sp K))
    (G : Over (Sp K)) [GrpObj G] (h : E.IsGt G) (X : Type) [AddCommGroup X]
    (t : G ⊗ G ⟶ splitTorus (Sp K) X)
    (h₁ : lift (𝟙 G) (1 : G ⟶ G) ≫ t = 1) (h₂ : lift (1 : G ⟶ G) (𝟙 G) ≫ t = 1) : t = 1 := by
  have key : ∀ (a : G ⟶ G ⊗ G), a ≫ t = 1 → ∀ χ : X, a.left.appTop.hom
      (splitTorusPointsEquiv (Sp K) X (G ⊗ G) t (Multiplicative.ofAdd χ)).val = 1 := by
    intro a ha χ
    have := splitTorusPointsEquiv_val (Sp K) X G (a ≫ t) χ
    rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ha, map_one] at this
    rw [splitTorusPointsEquiv_val]
    exact this.symm
  apply (splitTorusPointsEquiv (Sp K) X (G ⊗ G)).injective
  rw [map_one]
  ext χ
  exact unit_eq_one_of_axes_of_isGt K E G h _ (Units.isUnit _) (key _ h₁ χ) (key _ h₂ χ)

/- English proof (translation)
Introduce `K _ _ E E' G G' _ _ _ _ h ⟨D⟩ f hf`. Use `D.q_hom` as an intermediate fact. Use `D.i_hom` as an intermediate fact. Establish `hk` using `D.isKernel`. Establish `hq : IsMonHom (f ≫ D.q)` using `GlobalTheory.T.isMonHom_pointed_splitExt_to_abelianVariety K E G h E'.B E'.isAbelian (f ≫ D.q) (by`.

Rewrite using `[reassoc_of% hf]`. Conclude with `IsMonHom.one_hom D.q)`. Establish `hf1 : ∀ {W : Over (Sp K)}, (1 : W ⟶ G) ≫ f = 1`. Introduce `W`. Rewrite using `[Hom.one_def, Hom.one_def, Category.assoc, hf]`.

Set `d : G ⊗ G ⟶ G'` to `((fst G G * snd G G) ≫ f) / ((fst G G ≫ f) * (snd G G ≫ f))`. Establish `hd : d ≫ D.q = 1`. Simplify using `only [d]`. Rewrite using `[GrpObj.div_comp, Category.assoc, MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc, div_self']`. Set `t : G ⊗ G ⟶ splitTorus (Sp K) E'.X` to `hk.lift d (toUnit _) (by rw [hd, Hom.one_def])`.

Establish `ht : t ≫ D.i = d` using `hk.lift_fst _ _ _`. Establish `inj : ∀ a : G ⟶ G ⊗ G, a ≫ d = 1 → a ≫ t = 1` using `fun a ha => hk.hom_ext (by rw [Category.assoc, ht, ha, MonObj.one_comp]) (toUnit_unique _ _)`. Establish `t1 : t = 1`. Use `splitTorus_point_eq_one_of_axes K E G h E'.X t (inj _ ?_) (inj _ ?_)` and prove the remaining obligations. Simplify using `only [d]`.

Rewrite using `[GrpObj.comp_div, MonObj.comp_mul, ← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, hf1, _root_.mul_one, _root_.mul_one, div_self']`. Simplify using `only [d]`. Rewrite using `[GrpObj.comp_div, MonObj.comp_mul, ← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, hf1, _root_.one_mul, _root_.one_mul, div_self']`. Rewrite `ht` using `[t1, MonObj.one_comp]`. Establish `hm : (fst G G * snd G G) ≫ f = (fst G G ≫ f) * (snd G G ≫ f)` using `div_eq_one.mp ht.symm`.

Use `⟨hf, ?_⟩` and prove the remaining obligations. Rewrite `hm` using `[Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp]`. Rewrite using `[hm]`. Use `congr 1`.
-/
theorem isMonHom_of_isGt_of_one :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (E E' : SplitExt (Sp K)) (G G' : Over (Sp K)) [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G'], E.IsGt G → E'.IsGt G' → ∀ f : G ⟶ G', η[G] ≫ f = η[G'] → IsMonHom f := by
  intro K _ _ E E' G G' _ _ _ _ h ⟨D⟩ f hf
  have := D.q_hom
  have := D.i_hom
  have hk := D.isKernel
  have hq : IsMonHom (f ≫ D.q) := GlobalTheory.T.isMonHom_pointed_splitExt_to_abelianVariety K E G h E'.B E'.isAbelian (f ≫ D.q) (by
    rw [reassoc_of% hf]; exact IsMonHom.one_hom D.q)
  have hf1 : ∀ {W : Over (Sp K)}, (1 : W ⟶ G) ≫ f = 1 := by
    intro W
    rw [Hom.one_def, Hom.one_def, Category.assoc, hf]
  let d : G ⊗ G ⟶ G' := ((fst G G * snd G G) ≫ f) / ((fst G G ≫ f) * (snd G G ≫ f))
  have hd : d ≫ D.q = 1 := by
    simp only [d]
    rw [GrpObj.div_comp, Category.assoc, MonObj.mul_comp, MonObj.mul_comp, Category.assoc,
      Category.assoc, div_self']
  let t : G ⊗ G ⟶ splitTorus (Sp K) E'.X := hk.lift d (toUnit _) (by rw [hd, Hom.one_def])
  have ht : t ≫ D.i = d := hk.lift_fst _ _ _
  have inj : ∀ a : G ⟶ G ⊗ G, a ≫ d = 1 → a ≫ t = 1 := fun a ha =>
    hk.hom_ext (by rw [Category.assoc, ht, ha, MonObj.one_comp]) (toUnit_unique _ _)
  have t1 : t = 1 := by
    refine splitTorus_point_eq_one_of_axes K E G h E'.X t (inj _ ?_) (inj _ ?_)
    · simp only [d]
      rw [GrpObj.comp_div, MonObj.comp_mul, ← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd,
        lift_fst_assoc, lift_snd_assoc, hf1, _root_.mul_one, _root_.mul_one, div_self']
    · simp only [d]
      rw [GrpObj.comp_div, MonObj.comp_mul, ← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd,
        lift_fst_assoc, lift_snd_assoc, hf1, _root_.one_mul, _root_.one_mul, div_self']
  rw [t1, MonObj.one_comp] at ht
  have hm : (fst G G * snd G G) ≫ f = (fst G G ≫ f) * (snd G G ≫ f) := div_eq_one.mp ht.symm
  refine ⟨hf, ?_⟩
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at hm
  rw [hm]
  congr 1

end GlobalTheory
