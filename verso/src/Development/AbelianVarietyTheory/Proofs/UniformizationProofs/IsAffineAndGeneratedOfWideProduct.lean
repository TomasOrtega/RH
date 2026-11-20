import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AffineProduct

noncomputable def subringLift {Y X : Scheme.{0}} [IsAffine X] (B : Subring Γ(Y, ⊤)) (f : Y ⟶ X)
    (h : ∀ a, f.appTop.hom a ∈ B) : Spec (CommRingCat.of B) ⟶ X :=
  Spec.map (CommRingCat.ofHom (f.appTop.hom.codRestrict B h)) ≫ X.isoSpec.inv

noncomputable def toSpecSubring {Y : Scheme.{0}} (B : Subring Γ(Y, ⊤)) :
    Y ⟶ Spec (CommRingCat.of B) :=
  Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom B.subtype)

/- English proof (translation)
Establish `e : CommRingCat.ofHom (f.appTop.hom.codRestrict B h) ≫ CommRingCat.ofHom B.subtype = f.appTop`. Use extensionality with `a`. Both sides reduce to the same expression. Simplify using `only [toSpecSubring, subringLift, Category.assoc]`. Rewrite using `[← Spec.map_comp_assoc, e, ← Scheme.toSpecΓ_naturality_assoc]`.

Simplify using `[← Scheme.isoSpec_hom]`.
-/
theorem toSpecSubring_subringLift {Y X : Scheme.{0}} [IsAffine X] (B : Subring Γ(Y, ⊤))
    (f : Y ⟶ X) (h : ∀ a, f.appTop.hom a ∈ B) :
    toSpecSubring B ≫ subringLift B f h = f := by
  have e : CommRingCat.ofHom (f.appTop.hom.codRestrict B h) ≫ CommRingCat.ofHom B.subtype
      = f.appTop := by
    ext a; rfl
  simp only [toSpecSubring, subringLift, Category.assoc]
  rw [← Spec.map_comp_assoc, e, ← Scheme.toSpecΓ_naturality_assoc]
  simp [← Scheme.isoSpec_hom]

/- English proof (translation)
Substitute `w` using the available equality. Establish `e' : CommRingCat.ofHom ((f ≫ e).appTop.hom.codRestrict B h') = e.appTop ≫ CommRingCat.ofHom (f.appTop.hom.codRestrict B h)`. Use extensionality with `a`. Both sides reduce to the same expression. Simplify using `only [subringLift, Category.assoc]`.

Rewrite using `[e', Spec.map_comp, Category.assoc, Scheme.isoSpec_inv_naturality]`.
-/
theorem subringLift_comp {Y X X' : Scheme.{0}} [IsAffine X] [IsAffine X'] (B : Subring Γ(Y, ⊤))
    (f : Y ⟶ X) (h : ∀ a, f.appTop.hom a ∈ B) (e : X ⟶ X') (g : Y ⟶ X') (w : f ≫ e = g)
    (h' : ∀ a, g.appTop.hom a ∈ B) :
    subringLift B f h ≫ e = subringLift B g h' := by
  subst w
  have e' : CommRingCat.ofHom ((f ≫ e).appTop.hom.codRestrict B h')
      = e.appTop ≫ CommRingCat.ofHom (f.appTop.hom.codRestrict B h) := by
    ext a; rfl
  simp only [subringLift, Category.assoc]
  rw [e', Spec.map_comp, Category.assoc, Scheme.isoSpec_inv_naturality]

end GlobalTheory.AffineProduct

namespace GlobalTheory
open AffineProduct

/- English proof (translation)
Introduce `R j Y D s d pr w U hD`. Establish `key : ∀ B : Subring Γ(Y, ⊤), (∀ a, s.appTop.hom a ∈ B) → (∀ i a, (pr i).appTop.hom a ∈ B) → ∃ g : Spec (CommRingCat.of B) ⟶ Y, toSpecSubring B ≫ g = 𝟙 Y`. Introduce `B hs hp`. Take `⟨g, ⟨hg1, hg2⟩, -⟩` from `U _ (subringLift B s hs) (fun i => subringLift B (pr i) (hp i)) (fun i => subringLift_comp B _ _ _ _ (w i) hs)`. Use `⟨g, (U Y s pr w).unique ⟨?_, fun i => ?_⟩ ⟨by simp, by simp⟩⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, hg1, toSpecSubring_subringLift]`. Rewrite using `[Category.assoc, hg2, toSpecSubring_subringLift]`. Prove the components needed by the constructor for the conclusion. Take `⟨g, hg⟩` from `key ⊤ (fun _ => trivial) (fun _ _ => trivial)`. Rewrite `hg` using `[toSpecSubring, Category.assoc]`.

Use `set g' := Spec.map (CommRingCat.ofHom (⊤ : Subring Γ(Y, ⊤)).subtype) ≫ g with hg'`. Establish `h1 : g' ≫ Y.toSpecΓ = 𝟙 _`. Apply `ext_of_isAffine` to reduce the goal to its premises. Establish `h2 : Y.toSpecΓ ≫ g' ≫ Y.toSpecΓ = Y.toSpecΓ`. Rewrite using `[← Category.assoc, hg, Category.id_comp]`.

Establish `h3` using `congrArg Scheme.Hom.appTop h2`. Rewrite `h3` using `[Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]`. Rewrite using `[← cancel_mono (Scheme.ΓSpecIso Γ(Y, ⊤)).hom, h3]`. Conclude with `(Category.id_comp _).symm`. Conclude with `⟨⟨g', hg, h1⟩⟩`.

Introduce `B hs hp`. Take `⟨g, hg⟩` from `key B hs hp`. Establish `h3` using `congrArg Scheme.Hom.appTop hg`. Rewrite `h3` using `[toSpecSubring, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality, Scheme.Hom.id_appTop]`. Rewrite using `[eq_top_iff]`.

Introduce `a _`. Establish `h4` using `congrArg (fun φ => φ.hom a) h3`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, CommRingCat.hom_id, RingHom.id_apply] at h4`. Rewrite using `[← h4]`. Conclude with `Subtype.property _`.
-/
theorem isAffine_and_generated_of_wide_product : ∀ (R : CommRingCat.{0}) (j : ℕ) (Y : Scheme.{0}) (D : Fin j → Scheme.{0}) (s : Y ⟶ Spec R) (d : ∀ i, D i ⟶ Spec R) (pr : ∀ i, Y ⟶ D i) (w : ∀ i, pr i ≫ d i = s), (∀ (Z : Scheme.{0}) (z : Z ⟶ Spec R) (f : ∀ i, Z ⟶ D i), (∀ i, f i ≫ d i = z) → ∃! g : Z ⟶ Y, g ≫ s = z ∧ ∀ i, g ≫ pr i = f i) → (∀ i, IsAffine (D i)) → IsAffine Y ∧ ∀ B : Subring Γ(Y, ⊤), (∀ a, s.appTop.hom a ∈ B) → (∀ i a, (pr i).appTop.hom a ∈ B) → B = ⊤ := by
  intro R j Y D s d pr w U hD
  have key : ∀ B : Subring Γ(Y, ⊤), (∀ a, s.appTop.hom a ∈ B) →
      (∀ i a, (pr i).appTop.hom a ∈ B) →
      ∃ g : Spec (CommRingCat.of B) ⟶ Y, toSpecSubring B ≫ g = 𝟙 Y := by
    intro B hs hp
    obtain ⟨g, ⟨hg1, hg2⟩, -⟩ := U _ (subringLift B s hs) (fun i => subringLift B (pr i) (hp i))
      (fun i => subringLift_comp B _ _ _ _ (w i) hs)
    refine ⟨g, (U Y s pr w).unique ⟨?_, fun i => ?_⟩ ⟨by simp, by simp⟩⟩
    · rw [Category.assoc, hg1, toSpecSubring_subringLift]
    · rw [Category.assoc, hg2, toSpecSubring_subringLift]
  constructor
  · obtain ⟨g, hg⟩ := key ⊤ (fun _ => trivial) (fun _ _ => trivial)
    rw [toSpecSubring, Category.assoc] at hg
    set g' := Spec.map (CommRingCat.ofHom (⊤ : Subring Γ(Y, ⊤)).subtype) ≫ g with hg'
    have h1 : g' ≫ Y.toSpecΓ = 𝟙 _ := by
      apply ext_of_isAffine
      have h2 : Y.toSpecΓ ≫ g' ≫ Y.toSpecΓ = Y.toSpecΓ := by
        rw [← Category.assoc, hg, Category.id_comp]
      have h3 := congrArg Scheme.Hom.appTop h2
      rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at h3
      rw [← cancel_mono (Scheme.ΓSpecIso Γ(Y, ⊤)).hom, h3]
      exact (Category.id_comp _).symm
    exact ⟨⟨g', hg, h1⟩⟩
  · intro B hs hp
    obtain ⟨g, hg⟩ := key B hs hp
    have h3 := congrArg Scheme.Hom.appTop hg
    rw [toSpecSubring, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      Scheme.ΓSpecIso_naturality, Scheme.Hom.id_appTop] at h3
    rw [eq_top_iff]
    intro a _
    have h4 := congrArg (fun φ => φ.hom a) h3
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      CommRingCat.hom_id, RingHom.id_apply] at h4
    rw [← h4]
    exact Subtype.property _

end GlobalTheory
