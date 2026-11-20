import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace CosetQuotient

universe v u

/- English proof (translation)
Establish `same : ∀ {Z : C} (t : Z ⟶ T) (g : Z ⟶ G), ((t ≫ i) * g) ≫ q = g ≫ q` using `fun t g => ((h _ _ _).2 ⟨t, rfl⟩).symm`. Establish `hw2 : ∀ {Z : C} (g₁ g₂ : Z ⟶ G ⊗ G), g₁ ≫ (q ⊗ₘ q) = g₂ ≫ (q ⊗ₘ q) → g₁ ≫ μ[G] ≫ q = g₂ ≫ μ[G] ≫ q`. Introduce `Z g₁ g₂ hg`. Establish `h1 : (g₁ ≫ fst G G) ≫ q = (g₂ ≫ fst G G) ≫ q`. Simplify using `using hg =≫ fst B B`.

Establish `h2 : (g₁ ≫ snd G G) ≫ q = (g₂ ≫ snd G G) ≫ q`. Simplify using `using hg =≫ snd B B`. Take `⟨t, ht⟩` from `(h _ _ _).1 h1`. Take `⟨s, hs⟩` from `(h _ _ _).1 h2`. Establish `e : ∀ g : Z ⟶ G ⊗ G, g ≫ μ[G] = (g ≫ fst G G) * (g ≫ snd G G)`.

Introduce `g`. Rewrite using `[MonObj.mul_eq_mul, MonObj.comp_mul]`. Rewrite using `[← Category.assoc, ← Category.assoc, e g₁, e g₂, ht, hs, _root_.mul_mul_mul_comm, ← MonObj.mul_comp, same]`. Establish `hw1 : ∀ {Z : C} (g₁ g₂ : Z ⟶ G), g₁ ≫ q = g₂ ≫ q → g₁ ≫ ι[G] ≫ q = g₂ ≫ ι[G] ≫ q`. Introduce `Z g₁ g₂ hg`.

Take `⟨t, ht⟩` from `(h _ _ _).1 hg`. Rewrite using `[← Category.assoc, ← Category.assoc, ← Hom.inv_def, ← Hom.inv_def, ht, _root_.mul_inv, ← GrpObj.inv_comp, same]`. Set `mB : B ⊗ B ⟶ B` to `EffectiveEpi.desc (q ⊗ₘ q) (μ[G] ≫ q) hw2`. Establish `hmB : (q ⊗ₘ q) ≫ mB = μ[G] ≫ q` using `EffectiveEpi.fac _ _ _`. Set `iB : B ⟶ B` to `EffectiveEpi.desc q (ι[G] ≫ q) hw1`.

Establish `hiB : q ≫ iB = ι[G] ≫ q` using `EffectiveEpi.fac _ _ _`. Set `eB : 𝟙_ C ⟶ B` to `η[G] ≫ q`. Establish `key : ∀ {Z : C} (a b : Z ⟶ G), lift (a ≫ q) (b ≫ q) ≫ mB = (a * b) ≫ q`. Introduce `Z a b`. Rewrite using `[← CartesianMonoidalCategory.lift_map, Category.assoc, hmB, ← Category.assoc]`.

Both sides reduce to the same expression. Establish `keyL : ∀ {Z : C} (f : Z ⟶ 𝟙_ C) (b : Z ⟶ G), lift (f ≫ eB) (b ≫ q) ≫ mB = b ≫ q`. Introduce `Z f b`. Establish `e : f ≫ eB = (f ≫ η[G]) ≫ q` using `(Category.assoc _ _ _).symm`. Rewrite using `[e, key, toUnit_unique f (toUnit Z), ← Hom.one_def, _root_.one_mul]`.

Establish `keyR : ∀ {Z : C} (a : Z ⟶ G) (f : Z ⟶ 𝟙_ C), lift (a ≫ q) (f ≫ eB) ≫ mB = a ≫ q`. Introduce `Z a f`. Establish `e : f ≫ eB = (f ≫ η[G]) ≫ q` using `(Category.assoc _ _ _).symm`. Rewrite using `[e, key, toUnit_unique f (toUnit Z), ← Hom.one_def, _root_.mul_one]`. Establish `epiL : Epi (𝟙_ C ◁ q)`.

Establish `e : 𝟙_ C ◁ q = (λ_ G).hom ≫ q ≫ (λ_ B).inv`. Rewrite using `[← Category.assoc, ← MonoidalCategory.leftUnitor_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Rewrite using `[e]`. Use `infer_instance`. Establish `epiR : Epi (q ▷ 𝟙_ C)`.

Establish `e : q ▷ 𝟙_ C = (ρ_ G).hom ≫ q ≫ (ρ_ B).inv`. Rewrite using `[← Category.assoc, ← MonoidalCategory.rightUnitor_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Rewrite using `[e]`. Use `infer_instance`. Establish `invL : lift (ι[G] ≫ q) q ≫ mB = (ι[G] * 𝟙 G) ≫ q`.

Establish `e` using `key ι[G] (𝟙 G)`. Rewrite `e` using `[Category.id_comp]`. Then use the resulting hypothesis. Establish `invR : lift q (ι[G] ≫ q) ≫ mB = (𝟙 G * ι[G]) ≫ q`. Establish `e` using `key (𝟙 G) ι[G]`. Rewrite `e` using `[Category.id_comp]`. Then use the resulting hypothesis.

Set `inst : GrpObj B` to `{ one := eB mul := mB inv := iB one_mul := by`. Apply `(cancel_epi (𝟙_ C ◁ q)).1` to reduce the goal to its premises. Establish `e : 𝟙_ C ◁ q = lift (fst _ _) (snd _ _ ≫ q)`. Use `ext`. Simplify using `[CartesianMonoidalCategory.leftUnitor_hom]`.

Rewrite using `[e, lift_whiskerRight_assoc, keyL, lift_leftUnitor_hom]`. Use `mul_one := by`. Apply `(cancel_epi (q ▷ 𝟙_ C)).1` to reduce the goal to its premises. Establish `e : q ▷ 𝟙_ C = lift (fst _ _ ≫ q) (snd _ _)`. Use `ext`.

Simplify using `[CartesianMonoidalCategory.rightUnitor_hom]`. Rewrite using `[e, lift_whiskerLeft_assoc, keyR, lift_rightUnitor_hom]`. Use `mul_assoc := by`. Apply `(cancel_epi ((q ⊗ₘ q) ⊗ₘ q)).1` to reduce the goal to its premises. Apply the tactic sequence `have e : (q ⊗ₘ q) ⊗ₘ q = lift (lift ((fst _ _ ≫ fst _ _) ≫ q) ((fst _ _ ≫ snd _ _) ≫ q)) (snd _ _ ≫ q) := by ext <;> simp`.

Rewrite using `[e]`. Simplify using `only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, key]`. Rewrite using `[_root_.mul_assoc]`. Use `left_inv := by`. Apply `(cancel_epi q).1` to reduce the goal to its premises.

Rewrite using `[← Category.assoc, comp_lift, hiB, Category.comp_id, invL, ← Category.assoc q, toUnit_unique (q ≫ toUnit B) (toUnit G), GrpObj.inv_eq_inv, inv_mul_cancel, Hom.one_def, Category.assoc]`. Use `right_inv := by`. Apply `(cancel_epi q).1` to reduce the goal to its premises. Rewrite using `[← Category.assoc, comp_lift, hiB, Category.comp_id, invR, ← Category.assoc q, toUnit_unique (q ≫ toUnit B) (toUnit G), GrpObj.inv_eq_inv, mul_inv_cancel, Hom.one_def, Category.assoc] }`. Use `⟨inst, ⟨?_⟩, ⟨rfl, hmB.symm⟩, ?_⟩` and prove the remaining obligations.

Use `show (β_ B B).hom ≫ mB = mB`. Apply `(cancel_epi (q ⊗ₘ q)).1` to reduce the goal to its premises. Apply the tactic sequence `have e : q ⊗ₘ q = lift (fst G G ≫ q) (snd G G ≫ q) := by ext <;> simp`. Rewrite using `[e, ← Category.assoc, lift_braiding_hom, key, key, _root_.mul_comm]`. Establish `hsq : i ≫ q = toUnit T ≫ eB`.

Establish `e` using `same (𝟙 T) 1`. Rewrite `e` using `[Category.id_comp, _root_.mul_one]`. Rewrite using `[e, Hom.one_def, Category.assoc]`. Establish `ex : ∀ s : PullbackCone q eB, ∃ t : s.pt ⟶ T, s.fst = t ≫ i`. Introduce `s`.

Establish `hs : (1 : s.pt ⟶ G) ≫ q = s.fst ≫ q`. Rewrite using `[s.condition, Hom.one_def, toUnit_unique s.snd (toUnit s.pt), Category.assoc]`. Take `⟨t, ht⟩` from `(h _ _ _).1 hs`. Conclude with `⟨t, by rw [ht, _root_.mul_one]⟩`. Conclude with `IsPullback.of_isLimit (PullbackCone.IsLimit.mk hsq (fun s => Classical.choose (ex s)) (fun s => (Classical.choose_spec (ex s)).symm) (fun s => toUnit_unique _ _) (fun s m hm _ => by`.

Rewrite using `[← cancel_mono i, hm]`. Conclude with `Classical.choose_spec (ex s)))`.
-/
theorem exists_grpObj {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    [BraidedCategory C] {G T B : C} [GrpObj G] [IsCommMonObj G] [GrpObj T]
    (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [Mono i]
    [EffectiveEpi q] [EffectiveEpi (q ⊗ₘ q)] [Epi ((q ⊗ₘ q) ⊗ₘ q)]
    (h : ∀ (Z : C) (g g' : Z ⟶ G), g ≫ q = g' ≫ q ↔ ∃ t : Z ⟶ T, g' = (t ≫ i) * g) :
    ∃ (_ : GrpObj B), IsCommMonObj B ∧ IsMonHom q ∧ IsPullback i (toUnit _) q (η[B]) := by
  classical
  have same : ∀ {Z : C} (t : Z ⟶ T) (g : Z ⟶ G), ((t ≫ i) * g) ≫ q = g ≫ q :=
    fun t g => ((h _ _ _).2 ⟨t, rfl⟩).symm
  have hw2 : ∀ {Z : C} (g₁ g₂ : Z ⟶ G ⊗ G), g₁ ≫ (q ⊗ₘ q) = g₂ ≫ (q ⊗ₘ q) →
      g₁ ≫ μ[G] ≫ q = g₂ ≫ μ[G] ≫ q := by
    intro Z g₁ g₂ hg
    have h1 : (g₁ ≫ fst G G) ≫ q = (g₂ ≫ fst G G) ≫ q := by
      simpa using hg =≫ fst B B
    have h2 : (g₁ ≫ snd G G) ≫ q = (g₂ ≫ snd G G) ≫ q := by
      simpa using hg =≫ snd B B
    obtain ⟨t, ht⟩ := (h _ _ _).1 h1
    obtain ⟨s, hs⟩ := (h _ _ _).1 h2
    have e : ∀ g : Z ⟶ G ⊗ G, g ≫ μ[G] = (g ≫ fst G G) * (g ≫ snd G G) := by
      intro g
      rw [MonObj.mul_eq_mul, MonObj.comp_mul]
    rw [← Category.assoc, ← Category.assoc, e g₁, e g₂, ht, hs, _root_.mul_mul_mul_comm,
      ← MonObj.mul_comp, same]
  have hw1 : ∀ {Z : C} (g₁ g₂ : Z ⟶ G), g₁ ≫ q = g₂ ≫ q →
      g₁ ≫ ι[G] ≫ q = g₂ ≫ ι[G] ≫ q := by
    intro Z g₁ g₂ hg
    obtain ⟨t, ht⟩ := (h _ _ _).1 hg
    rw [← Category.assoc, ← Category.assoc, ← Hom.inv_def, ← Hom.inv_def, ht, _root_.mul_inv,
      ← GrpObj.inv_comp, same]
  let mB : B ⊗ B ⟶ B := EffectiveEpi.desc (q ⊗ₘ q) (μ[G] ≫ q) hw2
  have hmB : (q ⊗ₘ q) ≫ mB = μ[G] ≫ q := EffectiveEpi.fac _ _ _
  let iB : B ⟶ B := EffectiveEpi.desc q (ι[G] ≫ q) hw1
  have hiB : q ≫ iB = ι[G] ≫ q := EffectiveEpi.fac _ _ _
  let eB : 𝟙_ C ⟶ B := η[G] ≫ q
  have key : ∀ {Z : C} (a b : Z ⟶ G), lift (a ≫ q) (b ≫ q) ≫ mB = (a * b) ≫ q := by
    intro Z a b
    rw [← CartesianMonoidalCategory.lift_map, Category.assoc, hmB, ← Category.assoc]
    rfl
  have keyL : ∀ {Z : C} (f : Z ⟶ 𝟙_ C) (b : Z ⟶ G), lift (f ≫ eB) (b ≫ q) ≫ mB = b ≫ q := by
    intro Z f b
    have e : f ≫ eB = (f ≫ η[G]) ≫ q := (Category.assoc _ _ _).symm
    rw [e, key, toUnit_unique f (toUnit Z), ← Hom.one_def, _root_.one_mul]
  have keyR : ∀ {Z : C} (a : Z ⟶ G) (f : Z ⟶ 𝟙_ C), lift (a ≫ q) (f ≫ eB) ≫ mB = a ≫ q := by
    intro Z a f
    have e : f ≫ eB = (f ≫ η[G]) ≫ q := (Category.assoc _ _ _).symm
    rw [e, key, toUnit_unique f (toUnit Z), ← Hom.one_def, _root_.mul_one]
  have epiL : Epi (𝟙_ C ◁ q) := by
    have e : 𝟙_ C ◁ q = (λ_ G).hom ≫ q ≫ (λ_ B).inv := by
      rw [← Category.assoc, ← MonoidalCategory.leftUnitor_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    rw [e]
    infer_instance
  have epiR : Epi (q ▷ 𝟙_ C) := by
    have e : q ▷ 𝟙_ C = (ρ_ G).hom ≫ q ≫ (ρ_ B).inv := by
      rw [← Category.assoc, ← MonoidalCategory.rightUnitor_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    rw [e]
    infer_instance
  have invL : lift (ι[G] ≫ q) q ≫ mB = (ι[G] * 𝟙 G) ≫ q := by
    have e := key ι[G] (𝟙 G)
    rwa [Category.id_comp] at e
  have invR : lift q (ι[G] ≫ q) ≫ mB = (𝟙 G * ι[G]) ≫ q := by
    have e := key (𝟙 G) ι[G]
    rwa [Category.id_comp] at e
  let inst : GrpObj B :=
    { one := eB
      mul := mB
      inv := iB
      one_mul := by
        apply (cancel_epi (𝟙_ C ◁ q)).1
        have e : 𝟙_ C ◁ q = lift (fst _ _) (snd _ _ ≫ q) := by
          ext
          simp [CartesianMonoidalCategory.leftUnitor_hom]
        rw [e, lift_whiskerRight_assoc, keyL, lift_leftUnitor_hom]
      mul_one := by
        apply (cancel_epi (q ▷ 𝟙_ C)).1
        have e : q ▷ 𝟙_ C = lift (fst _ _ ≫ q) (snd _ _) := by
          ext
          simp [CartesianMonoidalCategory.rightUnitor_hom]
        rw [e, lift_whiskerLeft_assoc, keyR, lift_rightUnitor_hom]
      mul_assoc := by
        apply (cancel_epi ((q ⊗ₘ q) ⊗ₘ q)).1
        have e : (q ⊗ₘ q) ⊗ₘ q = lift (lift ((fst _ _ ≫ fst _ _) ≫ q) ((fst _ _ ≫ snd _ _) ≫ q))
            (snd _ _ ≫ q) := by ext <;> simp
        rw [e]
        simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc,
          lift_whiskerLeft_assoc, key]
        rw [_root_.mul_assoc]
      left_inv := by
        apply (cancel_epi q).1
        rw [← Category.assoc, comp_lift, hiB, Category.comp_id, invL, ← Category.assoc q,
          toUnit_unique (q ≫ toUnit B) (toUnit G), GrpObj.inv_eq_inv, inv_mul_cancel,
          Hom.one_def, Category.assoc]
      right_inv := by
        apply (cancel_epi q).1
        rw [← Category.assoc, comp_lift, hiB, Category.comp_id, invR, ← Category.assoc q,
          toUnit_unique (q ≫ toUnit B) (toUnit G), GrpObj.inv_eq_inv, mul_inv_cancel,
          Hom.one_def, Category.assoc] }
  refine ⟨inst, ⟨?_⟩, ⟨rfl, hmB.symm⟩, ?_⟩
  · show (β_ B B).hom ≫ mB = mB
    apply (cancel_epi (q ⊗ₘ q)).1
    have e : q ⊗ₘ q = lift (fst G G ≫ q) (snd G G ≫ q) := by ext <;> simp
    rw [e, ← Category.assoc, lift_braiding_hom, key, key, _root_.mul_comm]
  · have hsq : i ≫ q = toUnit T ≫ eB := by
      have e := same (𝟙 T) 1
      rw [Category.id_comp, _root_.mul_one] at e
      rw [e, Hom.one_def, Category.assoc]
    have ex : ∀ s : PullbackCone q eB, ∃ t : s.pt ⟶ T, s.fst = t ≫ i := by
      intro s
      have hs : (1 : s.pt ⟶ G) ≫ q = s.fst ≫ q := by
        rw [s.condition, Hom.one_def, toUnit_unique s.snd (toUnit s.pt), Category.assoc]
      obtain ⟨t, ht⟩ := (h _ _ _).1 hs
      exact ⟨t, by rw [ht, _root_.mul_one]⟩
    exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk hsq (fun s => Classical.choose (ex s))
      (fun s => (Classical.choose_spec (ex s)).symm) (fun s => toUnit_unique _ _)
      (fun s m hm _ => by
        rw [← cancel_mono i, hm]
        exact Classical.choose_spec (ex s)))

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}}

/- English proof (translation)
Establish `hw : ∀ {W : Over S} (e : X ⟶ W), (∀ {Z : Over S} (g₁ g₂ : Z ⟶ X), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) → ∀ {Z : Scheme} (g₁ g₂ : Z ⟶ X.left), g₁ ≫ f.left = g₂ ≫ f.left → g₁ ≫ e.left = g₂ ≫ e.left`. Introduce `W e he Z g₁ g₂ hg`. Establish `h2 : g₂ ≫ X.hom = g₁ ≫ X.hom`. Rewrite using `[← Over.w f, ← Category.assoc, ← hg, Category.assoc]`. Use `he (Over.homMk g₁ rfl : Over.mk (g₁ ≫ X.hom) ⟶ X) (Over.homMk g₂ h2) (by ext; simpa using hg)` as an intermediate fact.

Conclude with `congrArg CommaMorphism.left this`. Conclude with `⟨⟨{ desc := fun {W} e he => Over.homMk (EffectiveEpi.desc f.left e.left (hw e he)) (by`. Rewrite using `[← cancel_epi f.left, ← Category.assoc, EffectiveEpi.fac, Over.w e, Over.w f])`. Use `fac := fun {W} e he => by`. Use `ext`.

Simplify using `[EffectiveEpi.fac]`. Use `uniq := fun {W} e he m hm => by`. Use `ext`. Conclude with `EffectiveEpi.uniq f.left e.left (hw e he) m.left (by rw [← Over.comp_left, hm]) }⟩⟩`.
-/
lemma effectiveEpi_of_left {X Y : Over S} (f : X ⟶ Y) [EffectiveEpi f.left] :
    EffectiveEpi f := by
  have hw : ∀ {W : Over S} (e : X ⟶ W),
      (∀ {Z : Over S} (g₁ g₂ : Z ⟶ X), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) →
      ∀ {Z : Scheme} (g₁ g₂ : Z ⟶ X.left), g₁ ≫ f.left = g₂ ≫ f.left →
        g₁ ≫ e.left = g₂ ≫ e.left := by
    intro W e he Z g₁ g₂ hg
    have h2 : g₂ ≫ X.hom = g₁ ≫ X.hom := by
      rw [← Over.w f, ← Category.assoc, ← hg, Category.assoc]
    have := he (Over.homMk g₁ rfl : Over.mk (g₁ ≫ X.hom) ⟶ X) (Over.homMk g₂ h2)
      (by ext; simpa using hg)
    exact congrArg CommaMorphism.left this
  exact ⟨⟨{
    desc := fun {W} e he => Over.homMk (EffectiveEpi.desc f.left e.left (hw e he)) (by
      rw [← cancel_epi f.left, ← Category.assoc, EffectiveEpi.fac, Over.w e, Over.w f])
    fac := fun {W} e he => by
      ext
      simp [EffectiveEpi.fac]
    uniq := fun {W} e he m hm => by
      ext
      exact EffectiveEpi.uniq f.left e.left (hw e he) m.left (by rw [← Over.comp_left, hm]) }⟩⟩

/- English proof (translation)
The claim follows from `MorphismProperty.pullbackMap (P := @Flat) hf hg (Over.w f).symm (Over.w g).symm`.
-/
lemma flat_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : Flat f.left] [hg : Flat g.left] : Flat (f ⊗ₘ g).left := MorphismProperty.pullbackMap (P := @Flat) hf hg (Over.w f).symm (Over.w g).symm

/- English proof (translation)
Establish `hc : MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Surjective` using `⟨fun _ _ hf hg => by`. Use `hf` as an intermediate fact. Use `hg` as an intermediate fact. Use the proof step `infer_instance⟩`. Conclude with `MorphismProperty.pullbackMap (P := @AlgebraicGeometry.Surjective) hf hg (Over.w f).symm (Over.w g).symm`.
-/
lemma surjective_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : Surjective f.left] [hg : Surjective g.left] : Surjective (f ⊗ₘ g).left := by
  have hc : MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Surjective :=
    ⟨fun _ _ hf hg => by
      have := hf
      have := hg
      infer_instance⟩
  exact MorphismProperty.pullbackMap (P := @AlgebraicGeometry.Surjective) hf hg (Over.w f).symm
    (Over.w g).symm

/- English proof (translation)
The claim follows from `MorphismProperty.pullbackMap (P := @QuasiCompact) hf hg (Over.w f).symm (Over.w g).symm`.
-/
lemma quasiCompact_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : QuasiCompact f.left] [hg : QuasiCompact g.left] : QuasiCompact (f ⊗ₘ g).left := MorphismProperty.pullbackMap (P := @QuasiCompact) hf hg (Over.w f).symm (Over.w g).symm

end CosetQuotient

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Introduce `S G T B _ _ _ i q hi hm hf hs hc h`. Establish `e1 : EffectiveEpi q` using `CosetQuotient.effectiveEpi_of_left q`. Establish `f2` using `CosetQuotient.flat_tensorHom q q`. Establish `s2` using `CosetQuotient.surjective_tensorHom q q`. Establish `c2` using `CosetQuotient.quasiCompact_tensorHom q q`.

Establish `e2 : EffectiveEpi (q ⊗ₘ q)` using `CosetQuotient.effectiveEpi_of_left _`. Establish `f3` using `CosetQuotient.flat_tensorHom (q ⊗ₘ q) q`. Establish `s3` using `CosetQuotient.surjective_tensorHom (q ⊗ₘ q) q`. Establish `c3` using `CosetQuotient.quasiCompact_tensorHom (q ⊗ₘ q) q`. Establish `e3 : EffectiveEpi ((q ⊗ₘ q) ⊗ₘ q)` using `CosetQuotient.effectiveEpi_of_left _`.

Conclude with `CosetQuotient.exists_grpObj i q h`.
-/
theorem grpObj_of_flat_coset_quotient :
    ∀ (S : Scheme.{0}) (G T B : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj T] (i : T ⟶ G)
      (q : G ⟶ B), IsMonHom i → Mono i → Flat q.left → Surjective q.left →
      QuasiCompact q.left →
      (∀ (Z : Over S) (g g' : Z ⟶ G), g ≫ q = g' ≫ q ↔ ∃ t : Z ⟶ T, g' = (t ≫ i) * g) →
      ∃ (_ : GrpObj B), IsCommMonObj B ∧ IsMonHom q ∧ IsPullback i (toUnit _) q (η[B]) := by
  intro S G T B _ _ _ i q hi hm hf hs hc h
  have e1 : EffectiveEpi q := CosetQuotient.effectiveEpi_of_left q
  have f2 := CosetQuotient.flat_tensorHom q q
  have s2 := CosetQuotient.surjective_tensorHom q q
  have c2 := CosetQuotient.quasiCompact_tensorHom q q
  have e2 : EffectiveEpi (q ⊗ₘ q) := CosetQuotient.effectiveEpi_of_left _
  have f3 := CosetQuotient.flat_tensorHom (q ⊗ₘ q) q
  have s3 := CosetQuotient.surjective_tensorHom (q ⊗ₘ q) q
  have c3 := CosetQuotient.quasiCompact_tensorHom (q ⊗ₘ q) q
  have e3 : EffectiveEpi ((q ⊗ₘ q) ⊗ₘ q) := CosetQuotient.effectiveEpi_of_left _
  exact CosetQuotient.exists_grpObj i q h

end GlobalTheory
