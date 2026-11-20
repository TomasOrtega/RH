import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueRigidifiedLineBundleClassesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimageSectionsBijectiveAbelianSchemeSndStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhiskerLeftIsOpenImmersionRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditivePicClassOfLocallyAdditiveStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

/- English proof (translation)
Establish `h1` using `h Y 1 1 t`. Rewrite `h1` using `[_root_.mul_one]`. Conclude with `left_eq_add.1 h1`.
-/
theorem AddCls.pull_lift_one_eq_zero {T : Over S} {c : Pic (A ⊗ T).left} (h : AddCls A c) {Y : Over S} (t : Y ⟶ T) :
    CechPic.pull (lift (1 : Y ⟶ A) t).left c = 0 := by
  have h1 := h Y 1 1 t
  rw [_root_.mul_one] at h1
  exact left_eq_add.1 h1

/- English proof (translation)
Set `Y : Over S` to `Over.mk (t ≫ (A ⊗ Z).hom)`. Set `t' : Y ⟶ A ⊗ Z` to `Over.homMk t rfl`. Establish `hs : s ≫ T.hom = t ≫ (A ⊗ Z).hom`. Rewrite using `[← Over.w (A ◁ z), ← Category.assoc, hts, Category.assoc, Over.w]`. Set `s' : Y ⟶ T` to `Over.homMk s hs`.

Establish `h1 : t' ≫ A ◁ z = s' ≫ lift (1 : T ⟶ A) (𝟙 T)` using `Over.OverMorphism.ext hts`. Establish `h2 : t' ≫ fst A Z = 1`. Establish `h3` using `congrArg (· ≫ fst A T) h1`. Simplify `h3` using `only [Category.assoc, whiskerLeft_fst, lift_fst, MonObj.comp_one]`. Establish `h4 : t' = lift (1 : Y ⟶ A) (t' ≫ snd A Z)`.

Rewrite using `[← h2, lift_comp_fst_snd]`. Establish `h5` using `h.pull_lift_one_eq_zero (t' ≫ snd A Z)`. Rewrite `h5` using `[← h4]`. Conclude with `h5`.
-/
theorem AddCls.pull_eq_zero_of_unit {T Z : Over S} (z : Z ⟶ T) {c : Pic (A ⊗ Z).left} (h : AddCls A c)
    {T' : Scheme.{0}} (t : T' ⟶ (A ⊗ Z).left) (s : T' ⟶ T.left)
    (hts : t ≫ (A ◁ z).left = s ≫ (lift (1 : T ⟶ A) (𝟙 T)).left) : CechPic.pull t c = 0 := by
  let Y : Over S := Over.mk (t ≫ (A ⊗ Z).hom)
  let t' : Y ⟶ A ⊗ Z := Over.homMk t rfl
  have hs : s ≫ T.hom = t ≫ (A ⊗ Z).hom := by
    rw [← Over.w (A ◁ z), ← Category.assoc, hts, Category.assoc, Over.w]
  let s' : Y ⟶ T := Over.homMk s hs
  have h1 : t' ≫ A ◁ z = s' ≫ lift (1 : T ⟶ A) (𝟙 T) := Over.OverMorphism.ext hts
  have h2 : t' ≫ fst A Z = 1 := by
    have h3 := congrArg (· ≫ fst A T) h1
    simpa only [Category.assoc, whiskerLeft_fst, lift_fst, MonObj.comp_one] using h3
  have h4 : t' = lift (1 : Y ⟶ A) (t' ≫ snd A Z) := by
    rw [← h2, lift_comp_fst_snd]
  have h5 := h.pull_lift_one_eq_zero (t' ≫ snd A Z)
  rw [← h4] at h5
  exact h5

/- English proof (translation)
Set `Y : Over S` to `Over.mk (a ≫ (A ⊗ Z).hom)`. Set `a' : Y ⟶ A ⊗ Z` to `Over.homMk a rfl`. Establish `hb : b ≫ (A ⊗ Z').hom = a ≫ (A ⊗ Z).hom`. Rewrite using `[← Over.w (A ◁ z), ← Over.w (A ◁ z'), ← Category.assoc, ← hab, Category.assoc]`. Set `b' : Y ⟶ A ⊗ Z'` to `Over.homMk b hb`.

Establish `h1 : a' ≫ A ◁ z = b' ≫ A ◁ z'` using `Over.OverMorphism.ext hab`. Establish `h2 : a' ≫ fst A Z = b' ≫ fst A Z'`. Establish `h3` using `congrArg (· ≫ fst A T) h1`. Simplify `h3` using `only [Category.assoc, whiskerLeft_fst]`. Establish `h3 : (a' ≫ snd A Z) ≫ z = (b' ≫ snd A Z') ≫ z'`.

Establish `h3` using `congrArg (· ≫ snd A T) h1`. Simplify `h3` using `only [Category.assoc, whiskerLeft_snd]`. Establish `h4` using `congrArg Subtype.val (h Y _ _ h3)`. Rewrite `h4` using `[addF_map_val, addF_map_val]`. Establish `ha' : a' = lift (a' ≫ fst A Z) (𝟙 Y) ≫ A ◁ (a' ≫ snd A Z)`.

Rewrite using `[lift_whiskerLeft, Category.id_comp, lift_comp_fst_snd]`. Establish `hb' : b' = lift (a' ≫ fst A Z) (𝟙 Y) ≫ A ◁ (b' ≫ snd A Z')`. Rewrite using `[lift_whiskerLeft, Category.id_comp, h2, lift_comp_fst_snd]`. Establish `h5` using `congrArg (CechPic.pull (lift (a' ≫ fst A Z) (𝟙 Y)).left) h4`. Rewrite `h5` using `[← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, ← ha', ← hb']`.

Conclude with `h5`.
-/
theorem pull_eq_of_compat {T Z Z' : Over S} (z : Z ⟶ T) (z' : Z' ⟶ T) (y : (addF A).obj (op Z))
    (y' : (addF A).obj (op Z'))
    (h : ∀ (Y : Over S) (a : Y ⟶ Z) (b : Y ⟶ Z'), a ≫ z = b ≫ z' → (addF A).map a.op y = (addF A).map b.op y')
    {T' : Scheme.{0}} (a : T' ⟶ (A ⊗ Z).left) (b : T' ⟶ (A ⊗ Z').left)
    (hab : a ≫ (A ◁ z).left = b ≫ (A ◁ z').left) : CechPic.pull a y.1 = CechPic.pull b y'.1 := by
  let Y : Over S := Over.mk (a ≫ (A ⊗ Z).hom)
  let a' : Y ⟶ A ⊗ Z := Over.homMk a rfl
  have hb : b ≫ (A ⊗ Z').hom = a ≫ (A ⊗ Z).hom := by
    rw [← Over.w (A ◁ z), ← Over.w (A ◁ z'), ← Category.assoc, ← hab, Category.assoc]
  let b' : Y ⟶ A ⊗ Z' := Over.homMk b hb
  have h1 : a' ≫ A ◁ z = b' ≫ A ◁ z' := Over.OverMorphism.ext hab
  have h2 : a' ≫ fst A Z = b' ≫ fst A Z' := by
    have h3 := congrArg (· ≫ fst A T) h1
    simpa only [Category.assoc, whiskerLeft_fst] using h3
  have h3 : (a' ≫ snd A Z) ≫ z = (b' ≫ snd A Z') ≫ z' := by
    have h3 := congrArg (· ≫ snd A T) h1
    simpa only [Category.assoc, whiskerLeft_snd] using h3
  have h4 := congrArg Subtype.val (h Y _ _ h3)
  rw [addF_map_val, addF_map_val] at h4
  have ha' : a' = lift (a' ≫ fst A Z) (𝟙 Y) ≫ A ◁ (a' ≫ snd A Z) := by
    rw [lift_whiskerLeft, Category.id_comp, lift_comp_fst_snd]
  have hb' : b' = lift (a' ≫ fst A Z) (𝟙 Y) ≫ A ◁ (b' ≫ snd A Z') := by
    rw [lift_whiskerLeft, Category.id_comp, h2, lift_comp_fst_snd]
  have h5 := congrArg (CechPic.pull (lift (a' ≫ fst A Z) (𝟙 Y)).left) h4
  rw [← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, ← ha', ← hb'] at h5
  exact h5

/- English proof (translation)
Introduce `S A _ hA T J Z z y hz hcov hc`. Establish `he : (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (snd A T).left = 𝟙 T.left`. Rewrite using `[← Over.comp_left, lift_snd, Over.id_left]`. Take `⟨c₀, h0, hc₀⟩` from `GlobalTheory.T.exists_glue_rigidified_line_bundle_classes (A ⊗ T).left T.left (snd A T).left (lift (1 : T ⟶ A) (𝟙 T)).left he (GlobalTheory.T.isPreimageSectionsBijective_abelianScheme_snd S A T hA) J (fun i ↦ (A ⊗ Z i).left) (fun i ↦ (A ◁ z i).left) (fun i ↦ haveI := hz i; (z i). …`. Use `⟨⟨c₀, GlobalTheory.T.additive_picClass_of_locally_additive S A T hA c₀ h0 fun p ↦ ?_⟩, fun i ↦ Subtype.ext (hc₀ i)⟩` and prove the remaining obligations.

Take `⟨i, hi⟩` from `hcov p`. Use `⟨Z i, z i, hz i, hi, ?_⟩` and prove the remaining obligations. Rewrite using `[hc₀ i]`. Conclude with `(y i).2`.
-/
theorem addF_glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → (∀ (T : Over S) (J : Type) (Z : J → Over S) (z : ∀ i, Z i ⟶ T) (y : ∀ i, (addF A).obj (op (Z i))), (∀ i, IsOpenImmersion (z i).left) → (∀ p : T.left, ∃ i, p ∈ Set.range (z i).left) → (∀ (i k : J) (Y : Over S) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → (addF A).map a.op (y i) = (addF A).map b.op (y k)) → ∃ y₀ : (addF A).obj (op T), ∀ i, (addF A).map (z i).op y₀ = y i) := by
  intro S A _ hA T J Z z y hz hcov hc
  have he : (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (snd A T).left = 𝟙 T.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  obtain ⟨c₀, h0, hc₀⟩ := GlobalTheory.T.exists_glue_rigidified_line_bundle_classes (A ⊗ T).left T.left (snd A T).left (lift (1 : T ⟶ A) (𝟙 T)).left he
    (GlobalTheory.T.isPreimageSectionsBijective_abelianScheme_snd S A T hA) J (fun i ↦ (A ⊗ Z i).left) (fun i ↦ (A ◁ z i).left)
    (fun i ↦ haveI := hz i; (z i).left.opensRange) (fun i ↦ (y i).1)
    (fun i ↦ (GlobalTheory.whiskerLeft_isOpenImmersion_range S A T (Z i) (z i) (hz i)).1)
    (fun i x ↦ (GlobalTheory.whiskerLeft_isOpenImmersion_range S A T (Z i) (z i) (hz i)).2 x)
    (fun p ↦ hcov p)
    (fun i T' t s hts ↦ AddCls.pull_eq_zero_of_unit (z i) (y i).2 t s hts)
    (fun i k T' a b hab ↦ pull_eq_of_compat (z i) (z k) (y i) (y k) (hc i k) a b hab)
  refine ⟨⟨c₀, GlobalTheory.T.additive_picClass_of_locally_additive S A T hA c₀ h0 fun p ↦ ?_⟩, fun i ↦ Subtype.ext (hc₀ i)⟩
  obtain ⟨i, hi⟩ := hcov p
  refine ⟨Z i, z i, hz i, hi, ?_⟩
  rw [hc₀ i]
  exact (y i).2

end GlobalTheory.PicGlue
