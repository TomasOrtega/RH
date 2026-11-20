import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.OpenSubgrp

attribute [local instance] Over.cartesianMonoidalCategory

variable {S P : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [GrpObj H₂] {h₁ : H₁.left ⟶ P} {h₂ : H₂.left ⟶ P}
  {pS : P ⟶ S}

/- English proof (translation)
Establish `lift : ∀ c : Over.mk t ⟶ H₁, (∀ y, h₁ (c.left y) ∈ Set.range h₂) → ∃ c' : Over.mk t ⟶ H₂, c.left ≫ h₁ = c'.left ≫ h₂`. Introduce `c hc`. Set `c''` to `IsOpenImmersion.lift h₂ (c.left ≫ h₁) (by rintro _ ⟨y, rfl⟩; exact hc y)`. Establish `ec : c'' ≫ h₂ = c.left ≫ h₁` using `IsOpenImmersion.lift_fac _ _ _`. Use `⟨Over.homMk c'' ?_, ec.symm⟩` and prove the remaining obligations.

Use `show c'' ≫ H₂.hom = t`. Rewrite using `[← e₂, ← Category.assoc, ec, Category.assoc, e₁, Over.w c]`. Both sides reduce to the same expression. Take `⟨a', ea⟩` from `lift a ha`. Take `⟨b', eb⟩` from `lift b hb`.

Use `hm T t t a b a' b' ea eb` as an intermediate fact. Introduce `y`. Rewrite using `[← Scheme.Hom.comp_apply, this, Scheme.Hom.comp_apply]`. Conclude with `⟨_, rfl⟩`.
-/
theorem mul_mem_range (e₁ : h₁ ≫ pS = H₁.hom) (e₂ : h₂ ≫ pS = H₂.hom) [IsOpenImmersion h₂]
    (hm : MulAgree H₁ H₂ h₁ h₂) {T : Scheme.{0}} {t : T ⟶ S} (a b : Over.mk t ⟶ H₁)
    (ha : ∀ y, h₁ (a.left y) ∈ Set.range h₂) (hb : ∀ y, h₁ (b.left y) ∈ Set.range h₂) :
    ∀ y, h₁ ((a * b).left y) ∈ Set.range h₂ := by
  have lift : ∀ c : Over.mk t ⟶ H₁, (∀ y, h₁ (c.left y) ∈ Set.range h₂) →
      ∃ c' : Over.mk t ⟶ H₂, c.left ≫ h₁ = c'.left ≫ h₂ := by
    intro c hc
    let c'' := IsOpenImmersion.lift h₂ (c.left ≫ h₁) (by rintro _ ⟨y, rfl⟩; exact hc y)
    have ec : c'' ≫ h₂ = c.left ≫ h₁ := IsOpenImmersion.lift_fac _ _ _
    refine ⟨Over.homMk c'' ?_, ec.symm⟩
    show c'' ≫ H₂.hom = t
    rw [← e₂, ← Category.assoc, ec, Category.assoc, e₁, Over.w c]
    rfl
  obtain ⟨a', ea⟩ := lift a ha
  obtain ⟨b', eb⟩ := lift b hb
  have := hm T t t a b a' b' ea eb
  intro y
  rw [← Scheme.Hom.comp_apply, this, Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

end GlobalTheory.OpenSubgrp

namespace GlobalTheory.OpenSubgrp

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
The claim follows from `(Category.assoc _ _ _).symm`.
-/
theorem comp_inv' {S : Scheme.{0}} {G : Over S} [GrpObj G] {T T' : Over S} (ρ : T' ⟶ T) (x : T ⟶ G) :
    ρ ≫ x⁻¹ = (ρ ≫ x)⁻¹ :=
  (Category.assoc _ _ _).symm

/- English proof (translation)
Introduce `S P H₁ H₂ _ _ h₁ h₂ pS e₁ e₂ _ _ _ _ hm ho`. Establish `: GeometricallyIntegral H₁.hom` using `GlobalTheory.grpObj_geometricallyIntegral_of_smooth S H₁`. Set `WO : H₁.left.Opens` to `h₁ ⁻¹ᵁ h₂.opensRange`. Establish `hW : ∀ x, x ∈ WO ↔ h₁ x ∈ Set.range h₂` using `fun x => Iff.rfl`. Establish `hone : ∀ s : S, ∃ y ∈ WO, H₁.hom y = s`.

Introduce `s`. Use `⟨(1 : Over.mk (𝟙 S) ⟶ H₁).left s, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hW, ← Scheme.Hom.comp_apply, ho S (𝟙 S) (𝟙 S) rfl, Scheme.Hom.comp_apply]`. Conclude with `⟨_, rfl⟩`. Rewrite using `[← Scheme.Hom.comp_apply, Over.w]`.

Both sides reduce to the same expression. Set `f` to `fst H₁ H₁`. Set `g` to `snd H₁ H₁`. Set `a : H₁ ⊗ H₁ ⟶ H₁` to `g⁻¹ * f`. Set `O : (H₁ ⊗ H₁).left.Opens` to `a.left ⁻¹ᵁ WO ⊓ g.left ⁻¹ᵁ WO`.

Set `Y : Over S` to `Over.mk (O.ι ≫ (H₁ ⊗ H₁).hom)`. Set `j : Y ⟶ H₁ ⊗ H₁` to `Over.homMk O.ι rfl`. Establish `e1 : (j ≫ g) * (j ≫ a) = j ≫ f`. Rewrite using `[MonObj.comp_mul, comp_inv', mul_inv_cancel_left]`. Establish `inW : ∀ y, h₁ ((j ≫ f).left y) ∈ Set.range h₂`.

Rewrite using `[← e1]`. Conclude with `OpenSubgrp.mul_mem_range e₁ e₂ hm (j ≫ g) (j ≫ a) (fun y => y.2.2) (fun y => y.2.1)`. Establish `hg : GeometricallyIrreducible f.left` using `inferInstanceAs (GeometricallyIrreducible (pullback.fst H₁.hom H₁.hom))`. Establish `m2 : ∀ z : H₁.left, ∃ w : (H₁ ⊗ H₁).left, g.left w ∈ WO ∧ f.left w = z`. Introduce `z`.

Take `⟨y, hy, e⟩` from `hone (H₁.hom z)`. Take `⟨w, hw1, hw2⟩` from `Scheme.Pullback.exists_preimage_pullback z y e.symm`. Conclude with `⟨w, by rw [← hw2] at hy; exact hy, hw1⟩`. Establish `m1 : ∀ z : H₁.left, ∃ w : (H₁ ⊗ H₁).left, a.left w ∈ WO ∧ f.left w = z`. Introduce `z`.

Take `⟨w, hw1, hw2⟩` from `m2 z`. Set `b : H₁ ⊗ H₁ ⟶ H₁ ⊗ H₁` to `lift f (f * g⁻¹)`. Establish `b1 : b ≫ a = g`. Rewrite using `[MonObj.comp_mul, comp_inv', lift_fst, lift_snd, mul_inv_rev, inv_inv, inv_mul_cancel_right]`. Establish `b2 : b ≫ f = f` using `lift_fst _ _`.

Use `⟨b.left w, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← Over.comp_left, b1]`. Conclude with `hw1`. Rewrite using `[← Scheme.Hom.comp_apply, ← Over.comp_left, b2]`. Conclude with `hw2`.

Introduce and unpack `_ ⟨z, rfl⟩`. Establish `hi : IsIrreducible (f.left ⁻¹' {z})`. Rewrite using `[← f.left.range_fiberι, ← Set.image_univ]`. Conclude with `(IrreducibleSpace.isIrreducible_univ _).image _ (f.left.fiberι z).continuous.continuousOn`. Take `⟨w, hw, e⟩` from `m1 z`.

Take `⟨w', hw', e'⟩` from `m2 z`. Take `⟨y, hy, k₁, k₂⟩` from `hi.2 _ _ (a.left ⁻¹ᵁ WO).2 (g.left ⁻¹ᵁ WO).2 ⟨w, e, hw⟩ ⟨w', e', hw'⟩`. Use `inW ⟨y, k₁, k₂⟩` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Conclude with `hy.symm`.
-/
theorem range_subset : ∀ (S P : Scheme.{0}) (H₁ H₂ : Over S) [GrpObj H₁] [GrpObj H₂] (h₁ : H₁.left ⟶ P)
    (h₂ : H₂.left ⟶ P), ∀ pS : P ⟶ S, h₁ ≫ pS = H₁.hom → h₂ ≫ pS = H₂.hom → IsOpenImmersion h₁ →
    IsOpenImmersion h₂ → Smooth H₁.hom → GeometricallyConnected H₁.hom → MulAgree H₁ H₂ h₁ h₂ →
    OneAgree (𝟙 S) (𝟙 S) H₁ H₂ h₁ h₂ → Set.range h₁ ⊆ Set.range h₂ := by
  intro S P H₁ H₂ _ _ h₁ h₂ pS e₁ e₂ _ _ _ _ hm ho
  have : GeometricallyIntegral H₁.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth S H₁
  let WO : H₁.left.Opens := h₁ ⁻¹ᵁ h₂.opensRange
  have hW : ∀ x, x ∈ WO ↔ h₁ x ∈ Set.range h₂ := fun x => Iff.rfl

  have hone : ∀ s : S, ∃ y ∈ WO, H₁.hom y = s := by
    intro s
    refine ⟨(1 : Over.mk (𝟙 S) ⟶ H₁).left s, ?_, ?_⟩
    · rw [hW, ← Scheme.Hom.comp_apply, ho S (𝟙 S) (𝟙 S) rfl, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    · rw [← Scheme.Hom.comp_apply, Over.w]; rfl
  let f := fst H₁ H₁
  let g := snd H₁ H₁
  let a : H₁ ⊗ H₁ ⟶ H₁ := g⁻¹ * f
  let O : (H₁ ⊗ H₁).left.Opens := a.left ⁻¹ᵁ WO ⊓ g.left ⁻¹ᵁ WO
  let Y : Over S := Over.mk (O.ι ≫ (H₁ ⊗ H₁).hom)
  let j : Y ⟶ H₁ ⊗ H₁ := Over.homMk O.ι rfl
  have e1 : (j ≫ g) * (j ≫ a) = j ≫ f := by
    rw [MonObj.comp_mul, comp_inv', mul_inv_cancel_left]
  have inW : ∀ y, h₁ ((j ≫ f).left y) ∈ Set.range h₂ := by
    rw [← e1]
    exact OpenSubgrp.mul_mem_range e₁ e₂ hm (j ≫ g) (j ≫ a) (fun y => y.2.2) (fun y => y.2.1)
  have hg : GeometricallyIrreducible f.left :=
    inferInstanceAs (GeometricallyIrreducible (pullback.fst H₁.hom H₁.hom))
  have m2 : ∀ z : H₁.left, ∃ w : (H₁ ⊗ H₁).left, g.left w ∈ WO ∧ f.left w = z := by
    intro z
    obtain ⟨y, hy, e⟩ := hone (H₁.hom z)
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback z y e.symm
    exact ⟨w, by rw [← hw2] at hy; exact hy, hw1⟩
  have m1 : ∀ z : H₁.left, ∃ w : (H₁ ⊗ H₁).left, a.left w ∈ WO ∧ f.left w = z := by
    intro z
    obtain ⟨w, hw1, hw2⟩ := m2 z
    let b : H₁ ⊗ H₁ ⟶ H₁ ⊗ H₁ := lift f (f * g⁻¹)
    have b1 : b ≫ a = g := by
      rw [MonObj.comp_mul, comp_inv', lift_fst, lift_snd, mul_inv_rev, inv_inv, inv_mul_cancel_right]
    have b2 : b ≫ f = f := lift_fst _ _
    refine ⟨b.left w, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, b1]; exact hw1
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, b2]; exact hw2
  rintro _ ⟨z, rfl⟩
  have hi : IsIrreducible (f.left ⁻¹' {z}) := by
    rw [← f.left.range_fiberι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (f.left.fiberι z).continuous.continuousOn
  obtain ⟨w, hw, e⟩ := m1 z
  obtain ⟨w', hw', e'⟩ := m2 z
  obtain ⟨y, hy, k₁, k₂⟩ := hi.2 _ _ (a.left ⁻¹ᵁ WO).2 (g.left ⁻¹ᵁ WO).2 ⟨w, e, hw⟩ ⟨w', e', hw'⟩
  have := inW ⟨y, k₁, k₂⟩
  convert this using 2
  exact hy.symm

end GlobalTheory.OpenSubgrp
