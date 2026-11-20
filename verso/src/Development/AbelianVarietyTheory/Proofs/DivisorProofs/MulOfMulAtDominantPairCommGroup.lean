import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMonHomExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `K _ A _ hA V j f hj Y x₁ x₂ y₁ y₂ hdom h₁ h₂ h₃ Z u₁ u₂ u₃ hu`. Take `⟨_, hsm, hsep, _, _⟩` from `hA`. Set `R : A.left.Opens` to `j.left.opensRange`. Set `U : (A ⊗ A).left.Opens` to `(fst A A).left ⁻¹ᵁ R ⊓ (snd A A).left ⁻¹ᵁ R ⊓ (fst A A * snd A A).left ⁻¹ᵁ R`. Set `W : Over (Sp K)` to `Over.mk (U.ι ≫ (A ⊗ A).hom)`.

Set `ιW : W ⟶ A ⊗ A` to `Over.homMk U.ι rfl`. Establish `: IsOpenImmersion ιW.left` using `inferInstanceAs (IsOpenImmersion U.ι)`. Establish `hWU : ∀ q : W.left, ιW.left q ∈ U` using `fun q => (Scheme.Opens.range_ι U).subset ⟨q, rfl⟩`. Establish `hR : ∀ (g : A ⊗ A ⟶ A) (q : W.left), ιW.left q ∈ g.left ⁻¹ᵁ R → (ιW ≫ g).left q ∈ Set.range j.left` using `fun g q h => by`. Rewrite using `[Over.comp_left, Scheme.Hom.comp_apply]`.

Conclude with `h`. Take `⟨v₁, hv₁⟩` from `GlobalTheory.GenericHom.exists_lift j (ιW ≫ fst A A) fun q => hR _ q (hWU q).1.1`. Take `⟨v₂, hv₂⟩` from `GlobalTheory.GenericHom.exists_lift j (ιW ≫ snd A A) fun q => hR _ q (hWU q).1.2`. Take `⟨v₃, hv₃⟩` from `GlobalTheory.GenericHom.exists_lift j (ιW ≫ (fst A A * snd A A)) fun q => hR _ q (hWU q).2`. Establish `: Smooth (A ⊗ A).hom` using `inferInstanceAs (Smooth (pullback.fst A.hom A.hom ≫ A.hom))`.

Establish `: Smooth W.hom` using `inferInstanceAs (Smooth (U.ι ≫ (A ⊗ A).hom))`. Use `GlobalTheory.isNormalScheme_of_smooth (S := Spec (.of K)) W.hom` as an intermediate fact. Establish `: IsReduced W.left` using `GlobalTheory.IsNormalScheme.isReduced`. Set `Y' : Y.left.Opens` to `(lift x₁ x₂).left ⁻¹ᵁ U`. Set `Z' : Over (Sp K)` to `Over.mk (Y'.ι ≫ Y.hom)`.

Set `w : Z' ⟶ Y` to `Over.homMk Y'.ι rfl`. Set `p : Z' ⟶ W` to `Over.homMk ((lift x₁ x₂).left ∣_ U) (by show (lift x₁ x₂).left ∣_ U ≫ U.ι ≫ (A ⊗ A).hom = Y'.ι ≫ Y.hom`. Rewrite using `[← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w])`. Establish `hpw : p ≫ ιW = w ≫ lift x₁ x₂` using `Over.OverMorphism.ext (morphismRestrict_ι _ _)`. Establish `: IsDominant p.left` using `IsZariskiLocalAtTarget.restrict hdom U`.

Establish `e₁ : p ≫ v₁ ≫ f = w ≫ y₁` using `h₁ Z' w (p ≫ v₁) (by rw [Category.assoc, hv₁, ← Category.assoc, hpw, Category.assoc, lift_fst])`. Establish `e₂ : p ≫ v₂ ≫ f = w ≫ y₂` using `h₂ Z' w (p ≫ v₂) (by rw [Category.assoc, hv₂, ← Category.assoc, hpw, Category.assoc, lift_snd])`. Establish `e₃ : p ≫ v₃ ≫ f = w ≫ (y₁ * y₂)` using `h₃ Z' w (p ≫ v₃) (by`. Rewrite using `[Category.assoc, hv₃, ← Category.assoc, hpw, Category.assoc, MonObj.comp_mul, lift_fst, lift_snd])`. Establish `key : (v₁ ≫ f) * (v₂ ≫ f) = v₃ ≫ f`.

Use `Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated A.hom ?_ p.left ?_)` and prove the remaining obligations. Rewrite using `[Over.w, Over.w]`. Establish `: p ≫ ((v₁ ≫ f) * (v₂ ≫ f)) = p ≫ (v₃ ≫ f)`. Rewrite using `[MonObj.comp_mul, e₁, e₂, e₃, MonObj.comp_mul]`. Conclude with `congrArg CommaMorphism.left this`.

Establish `hU : ∀ q : Z.left, (lift (u₁ ≫ j) (u₂ ≫ j)).left q ∈ Set.range ιW.left`. Introduce `q`. Use `show _ ∈ Set.range U.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Establish `hq : ∀ (g : A ⊗ A ⟶ A) (u : Z ⟶ V), lift (u₁ ≫ j) (u₂ ≫ j) ≫ g = u ≫ j → (lift (u₁ ≫ j) (u₂ ≫ j)).left q ∈ g.left ⁻¹ᵁ R` using `fun g u e => by show g.left ((lift (u₁ ≫ j) (u₂ ≫ j)).left q) ∈ Set.range j.left`.

Rewrite using `[← Scheme.Hom.comp_apply, ← Over.comp_left, e]`. Conclude with `⟨u.left q, by rw [Over.comp_left, Scheme.Hom.comp_apply]⟩`. Conclude with `⟨⟨hq _ u₁ (lift_fst _ _), hq _ u₂ (lift_snd _ _)⟩, hq _ u₃ (by rw [MonObj.comp_mul, lift_fst, lift_snd, hu])⟩`. Take `⟨g, hg⟩` from `GlobalTheory.GenericHom.exists_lift ιW (lift (u₁ ≫ j) (u₂ ≫ j)) hU`. Establish `canc : ∀ a b : Z ⟶ V, a ≫ j = b ≫ j → a = b` using `fun a b e => Over.OverMorphism.ext ((cancel_mono j.left).1 (congrArg CommaMorphism.left e))`.

Establish `c₁ : g ≫ v₁ = u₁` using `canc _ _ (by rw [Category.assoc, hv₁, ← Category.assoc, hg, lift_fst])`. Establish `c₂ : g ≫ v₂ = u₂` using `canc _ _ (by rw [Category.assoc, hv₂, ← Category.assoc, hg, lift_snd])`. Establish `c₃ : g ≫ v₃ = u₃` using `canc _ _ (by`. Rewrite using `[Category.assoc, hv₃, ← Category.assoc, hg, MonObj.comp_mul, lift_fst, lift_snd, hu])`. Rewrite using `[← c₁, ← c₂, ← c₃, Category.assoc, Category.assoc, Category.assoc, ← MonObj.comp_mul, key]`.
-/
theorem mul_of_isDominant_pair : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], GlobalTheory.SS.SmConn A → ∀ (V : Over (Sp K)) (j f : V ⟶ A), IsOpenImmersion j.left → ∀ (Y : Over (Sp K)) (x₁ x₂ y₁ y₂ : Y ⟶ A), IsDominant (lift x₁ x₂).left → (∀ (Z : Over (Sp K)) (w : Z ⟶ Y) (u : Z ⟶ V), u ≫ j = w ≫ x₁ → u ≫ f = w ≫ y₁) → (∀ (Z : Over (Sp K)) (w : Z ⟶ Y) (u : Z ⟶ V), u ≫ j = w ≫ x₂ → u ≫ f = w ≫ y₂) → (∀ (Z : Over (Sp K)) (w : Z ⟶ Y) (u : Z ⟶ V), u ≫ j = w ≫ (x₁ * x₂) → u ≫ f = w ≫ (y₁ * y₂)) → ∀ (Z : Over (Sp K)) (u₁ u₂ u₃ : Z ⟶ V), (u₁ ≫ j) * (u₂ ≫ j) = u₃ ≫ j → (u₁ ≫ f) * (u₂ ≫ f) = u₃ ≫ f := by
  intro K _ A _ hA V j f hj Y x₁ x₂ y₁ y₂ hdom h₁ h₂ h₃ Z u₁ u₂ u₃ hu
  obtain ⟨_, hsm, hsep, _, _⟩ := hA
  let R : A.left.Opens := j.left.opensRange
  let U : (A ⊗ A).left.Opens :=
    (fst A A).left ⁻¹ᵁ R ⊓ (snd A A).left ⁻¹ᵁ R ⊓ (fst A A * snd A A).left ⁻¹ᵁ R
  let W : Over (Sp K) := Over.mk (U.ι ≫ (A ⊗ A).hom)
  let ιW : W ⟶ A ⊗ A := Over.homMk U.ι rfl
  have : IsOpenImmersion ιW.left := inferInstanceAs (IsOpenImmersion U.ι)
  have hWU : ∀ q : W.left, ιW.left q ∈ U := fun q => (Scheme.Opens.range_ι U).subset ⟨q, rfl⟩
  have hR : ∀ (g : A ⊗ A ⟶ A) (q : W.left), ιW.left q ∈ g.left ⁻¹ᵁ R →
      (ιW ≫ g).left q ∈ Set.range j.left := fun g q h => by
    rw [Over.comp_left, Scheme.Hom.comp_apply]; exact h
  obtain ⟨v₁, hv₁⟩ := GlobalTheory.GenericHom.exists_lift j (ιW ≫ fst A A) fun q => hR _ q (hWU q).1.1
  obtain ⟨v₂, hv₂⟩ := GlobalTheory.GenericHom.exists_lift j (ιW ≫ snd A A) fun q => hR _ q (hWU q).1.2
  obtain ⟨v₃, hv₃⟩ := GlobalTheory.GenericHom.exists_lift j (ιW ≫ (fst A A * snd A A)) fun q => hR _ q (hWU q).2
  have : Smooth (A ⊗ A).hom := inferInstanceAs (Smooth (pullback.fst A.hom A.hom ≫ A.hom))
  have : Smooth W.hom := inferInstanceAs (Smooth (U.ι ≫ (A ⊗ A).hom))
  have := GlobalTheory.isNormalScheme_of_smooth (S := Spec (.of K)) W.hom
  have : IsReduced W.left := GlobalTheory.IsNormalScheme.isReduced
  let Y' : Y.left.Opens := (lift x₁ x₂).left ⁻¹ᵁ U
  let Z' : Over (Sp K) := Over.mk (Y'.ι ≫ Y.hom)
  let w : Z' ⟶ Y := Over.homMk Y'.ι rfl
  let p : Z' ⟶ W := Over.homMk ((lift x₁ x₂).left ∣_ U) (by
    show (lift x₁ x₂).left ∣_ U ≫ U.ι ≫ (A ⊗ A).hom = Y'.ι ≫ Y.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w])
  have hpw : p ≫ ιW = w ≫ lift x₁ x₂ := Over.OverMorphism.ext (morphismRestrict_ι _ _)
  have : IsDominant p.left := IsZariskiLocalAtTarget.restrict hdom U
  have e₁ : p ≫ v₁ ≫ f = w ≫ y₁ :=
    h₁ Z' w (p ≫ v₁) (by rw [Category.assoc, hv₁, ← Category.assoc, hpw, Category.assoc, lift_fst])
  have e₂ : p ≫ v₂ ≫ f = w ≫ y₂ :=
    h₂ Z' w (p ≫ v₂) (by rw [Category.assoc, hv₂, ← Category.assoc, hpw, Category.assoc, lift_snd])
  have e₃ : p ≫ v₃ ≫ f = w ≫ (y₁ * y₂) :=
    h₃ Z' w (p ≫ v₃) (by
      rw [Category.assoc, hv₃, ← Category.assoc, hpw, Category.assoc, MonObj.comp_mul, lift_fst, lift_snd])
  have key : (v₁ ≫ f) * (v₂ ≫ f) = v₃ ≫ f := by
    refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated A.hom ?_ p.left ?_)
    · rw [Over.w, Over.w]
    · have : p ≫ ((v₁ ≫ f) * (v₂ ≫ f)) = p ≫ (v₃ ≫ f) := by
        rw [MonObj.comp_mul, e₁, e₂, e₃, MonObj.comp_mul]
      exact congrArg CommaMorphism.left this
  have hU : ∀ q : Z.left, (lift (u₁ ≫ j) (u₂ ≫ j)).left q ∈ Set.range ιW.left := by
    intro q
    show _ ∈ Set.range U.ι
    rw [Scheme.Opens.range_ι]
    have hq : ∀ (g : A ⊗ A ⟶ A) (u : Z ⟶ V), lift (u₁ ≫ j) (u₂ ≫ j) ≫ g = u ≫ j →
        (lift (u₁ ≫ j) (u₂ ≫ j)).left q ∈ g.left ⁻¹ᵁ R := fun g u e => by
      show g.left ((lift (u₁ ≫ j) (u₂ ≫ j)).left q) ∈ Set.range j.left
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e]
      exact ⟨u.left q, by rw [Over.comp_left, Scheme.Hom.comp_apply]⟩
    exact ⟨⟨hq _ u₁ (lift_fst _ _), hq _ u₂ (lift_snd _ _)⟩,
      hq _ u₃ (by rw [MonObj.comp_mul, lift_fst, lift_snd, hu])⟩
  obtain ⟨g, hg⟩ := GlobalTheory.GenericHom.exists_lift ιW (lift (u₁ ≫ j) (u₂ ≫ j)) hU
  have canc : ∀ a b : Z ⟶ V, a ≫ j = b ≫ j → a = b := fun a b e =>
    Over.OverMorphism.ext ((cancel_mono j.left).1 (congrArg CommaMorphism.left e))
  have c₁ : g ≫ v₁ = u₁ := canc _ _ (by rw [Category.assoc, hv₁, ← Category.assoc, hg, lift_fst])
  have c₂ : g ≫ v₂ = u₂ := canc _ _ (by rw [Category.assoc, hv₂, ← Category.assoc, hg, lift_snd])
  have c₃ : g ≫ v₃ = u₃ := canc _ _ (by
    rw [Category.assoc, hv₃, ← Category.assoc, hg, MonObj.comp_mul, lift_fst, lift_snd, hu])
  rw [← c₁, ← c₂, ← c₃, Category.assoc, Category.assoc, Category.assoc, ← MonObj.comp_mul, key]

end GlobalTheory.Mum
