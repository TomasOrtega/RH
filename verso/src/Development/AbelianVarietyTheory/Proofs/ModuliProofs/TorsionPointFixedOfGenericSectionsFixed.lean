import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsDominantGeometricPointOfIsPreimmersion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

/- English proof (translation)
Establish `key : ∀ {V : Scheme.{0}} (v : V ⟶ W) (u : V ⟶ U), v ≫ a ≫ g = u ≫ j → v ≫ a = u ≫ s`. Introduce `V v u h`. Use `congrArg (pullback.lift v u h ≫ ·) hs` as an intermediate fact. Simplify `this` using `only [pullback.lift_fst_assoc, pullback.lift_snd_assoc]`. Set `f₁` to `pullback.fst (a ≫ g) ((a ≫ g) ≫ r)`.

Set `f₂` to `pullback.snd (a ≫ g) ((a ≫ g) ≫ r)`. Establish `hc : f₁ ≫ a ≫ g = f₂ ≫ (a ≫ g) ≫ r` using `pullback.condition`. Set `t` to `f₂ ≫ a ≫ g`. Establish `: IsOpenImmersion t` using `inferInstance`. Establish `: IsReduced (pullback (a ≫ g) ((a ≫ g) ≫ r))` using `isReduced_of_isOpenImmersion t`.

Use `isDominant_pullback_fst_of_isOpenMap j t t.isOpenEmbedding.isOpenMap` as an intermediate fact. Establish `hd : pullback.fst t j ≫ f₂ ≫ a ≫ g = pullback.snd t j ≫ j` using `pullback.condition`. Establish `he : f₂ ≫ a ≫ φ = f₁ ≫ a`. Use `ext_of_isDominant_of_isSeparated g ?_ (pullback.fst t j) ?_` and prove the remaining obligations. Simplify using `only [Category.assoc, hφ, hc]`.

Establish `h₁` using `key (pullback.fst t j ≫ f₂) (pullback.snd t j) ((Category.assoc _ _ _).trans hd)`. Establish `h₂` using `key (pullback.fst t j ≫ f₁) (pullback.snd t j ≫ r₀) (by`. Simplify using `only [Category.assoc, hc, hr, reassoc_of% hd])`. Simplify using `only [Category.assoc] at h₁ h₂`. Rewrite using `[h₂, reassoc_of% h₁, hsφ]`.

Use `congrArg (pullback.lift w w hw.symm ≫ ·) he` as an intermediate fact. Simplify `this` using `only [f₁, f₂, pullback.lift_fst_assoc, pullback.lift_snd_assoc]`.
-/
theorem comp_eq_of_extending_section {X U W G T : Scheme.{0}} [IsReduced X] (j : U ⟶ X)
    [IsDominant j] (g : G ⟶ X) [IsSeparated g] (a : W ⟶ G) [IsOpenImmersion (a ≫ g)]
    (s : U ⟶ G) (hs : pullback.fst (a ≫ g) j ≫ a = pullback.snd (a ≫ g) j ≫ s)
    (r : X ⟶ X) (r₀ : U ⟶ U) (φ : G ⟶ G) (hr : r₀ ≫ j = j ≫ r) (hφ : φ ≫ g = g ≫ r)
    (hsφ : s ≫ φ = r₀ ≫ s) (w : T ⟶ W) (hw : w ≫ (a ≫ g) ≫ r = w ≫ a ≫ g) :
    w ≫ a ≫ φ = w ≫ a := by
  have key : ∀ {V : Scheme.{0}} (v : V ⟶ W) (u : V ⟶ U), v ≫ a ≫ g = u ≫ j → v ≫ a = u ≫ s := by
    intro V v u h
    have := congrArg (pullback.lift v u h ≫ ·) hs
    simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this
  let f₁ := pullback.fst (a ≫ g) ((a ≫ g) ≫ r)
  let f₂ := pullback.snd (a ≫ g) ((a ≫ g) ≫ r)
  have hc : f₁ ≫ a ≫ g = f₂ ≫ (a ≫ g) ≫ r := pullback.condition
  let t := f₂ ≫ a ≫ g
  have : IsOpenImmersion t := inferInstance
  have : IsReduced (pullback (a ≫ g) ((a ≫ g) ≫ r)) := isReduced_of_isOpenImmersion t
  have := isDominant_pullback_fst_of_isOpenMap j t t.isOpenEmbedding.isOpenMap
  have hd : pullback.fst t j ≫ f₂ ≫ a ≫ g = pullback.snd t j ≫ j := pullback.condition
  have he : f₂ ≫ a ≫ φ = f₁ ≫ a := by
    refine ext_of_isDominant_of_isSeparated g ?_ (pullback.fst t j) ?_
    · simp only [Category.assoc, hφ, hc]
    · have h₁ := key (pullback.fst t j ≫ f₂) (pullback.snd t j) ((Category.assoc _ _ _).trans hd)
      have h₂ := key (pullback.fst t j ≫ f₁) (pullback.snd t j ≫ r₀) (by
        simp only [Category.assoc, hc, hr, reassoc_of% hd])
      simp only [Category.assoc] at h₁ h₂
      rw [h₂, reassoc_of% h₁, hsφ]
  have := congrArg (pullback.lift w w hw.symm ≫ ·) he
  simpa only [f₁, f₂, pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this

/- English proof (translation)
Introduce `X U _ j hN hj₁ hj₂ hj₃ hj₄ G _ n I _ σ r r₀ φ hG hn hσ hgeo hr _ hφ hσφ k _ _ x y hx hy`. Use `hG.comm` as an intermediate fact. Use `hG.smooth` as an intermediate fact. Use `hG.separated` as an intermediate fact. Use `IsNormalScheme.of_pred hN` as an intermediate fact.

Establish `hex : ∀ {T : Over X} (z : T ⟶ G), z ^ n = 1 → ∃ z' : T ⟶ torsion G n, z' ≫ torsion.ι G n = z` using `fun z hz => ⟨pullback.lift z (toUnit _) (by rw [GrpTangent.comp_mulN, hz, Hom.one_def]), pullback.lift_fst _ _ _⟩`. Establish `hι : torsion.ι G n ^ n = 1`. Rewrite using `[← GrpTangent.comp_mulN, Hom.one_def]`. Conclude with `pullback.condition.trans (congrArg (· ≫ _) (toUnit_unique _ _))`. Establish `hcl : IsClosedImmersion η[G].left`.

Establish `: IsClosedImmersion (η[G].left ≫ G.hom)`. Rewrite using `[Over.w]`. Conclude with `inferInstanceAs (IsClosedImmersion (𝟙 X))`. Conclude with `IsClosedImmersion.of_comp _ G.hom`. Establish `: IsClosedImmersion (torsion.ι G n).left` using `MorphismProperty.of_isPullback (P := @IsClosedImmersion) (GrpTangent.isPullback_torsion G n).flip hcl`.

Establish `hsep : IsSeparated (torsion G n).hom`. Rewrite using `[← Over.w (torsion.ι G n)]`. Use `infer_instance`. Use `choose τ hτ using fun i => hex (σ i) (hσ i)`. Establish `hτ' : ∀ i, (τ i).left ≫ (torsion.ι G n).left = (σ i).left` using `fun i => congrArg Over.Hom.left (hτ i)`.

Take `⟨y', rfl⟩` from `hex y hy`. Take `⟨i, W, hyW, hW, he⟩` from `exists_opens_isOpenImmersion_extending_section X U j hN hj₁ hj₂ hj₃ hj₄ _ (torsion G n).hom I (fun i => (τ i).left) (GrpTangent.etale_torsion G hn) hsep (fun i => Over.w (τ i)) (fun k _ _ u z hz => by`. Take `⟨i, hi⟩` from `hgeo k u (Over.homMk z hz ≫ torsion.ι G n) (by rw [← comp_pow, hι, comp_one])`. Use `⟨i, ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono (torsion.ι G n).left, Category.assoc, hτ']`.

Conclude with `hi) (y'.left (IsLocalRing.closedPoint k))`. Establish `hrange : Set.range y'.left ⊆ Set.range W.ι`. Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι, Subsingleton.elim (α := PrimeSpectrum k) z (IsLocalRing.closedPoint k)]`. Conclude with `hyW`.

Establish `hw` using `IsOpenImmersion.lift_fac W.ι y'.left hrange`. Establish `hq : (W.ι ≫ (torsion.ι G n).left) ≫ G.hom = W.ι ≫ (torsion G n).hom`. Rewrite using `[Category.assoc, Over.w]`. Establish `: IsOpenImmersion ((W.ι ≫ (torsion.ι G n).left) ≫ G.hom)` using `hq ▸ hW`. Establish `hyx : y'.left ≫ (torsion G n).hom = x` using `Over.w y'`.

Use `comp_eq_of_extending_section j G.hom (W.ι ≫ (torsion.ι G n).left) (σ i).left (by` as an intermediate fact. Establish `h` using `congrArg (pullback.lift (pullback.fst ((W.ι ≫ (torsion.ι G n).left) ≫ G.hom) j) (pullback.snd _ j) (by rw [← hq]; exact pullback.condition) ≫ · ≫ (torsion.ι G n).left) he`. Simplify `h)` using `only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc, hτ']`. Use `r r₀ φ hr hφ.1.w (hσφ i) (IsOpenImmersion.lift W.ι y'.left hrange)`. Use the proof step `(by rw [hq, Category.assoc, reassoc_of% hw, reassoc_of% hw, reassoc_of% hyx, hyx, hx])`.

Simplify `this` using `only [Category.assoc, reassoc_of% hw, Over.comp_left]`.
-/
theorem torsion_point_fixed_of_generic_sections_fixed : ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (G : Over X) [GrpObj G] (n : ℕ) (I : Type) [Finite I] (σ : I → (Over.mk j ⟶ G)) (r : X ⟶ X) (r₀ : U ⟶ U) (φ : G.left ⟶ G.left), IsSemiAbelian G → IsUnit (n : Γ(X, ⊤)) → (∀ i, σ i ^ n = 1) → (∀ (k : Type) [Field k] [IsAlgClosed k] (u : Sp k ⟶ U) (y : Over.mk (u ≫ j) ⟶ G), y ^ n = 1 → ∃ i, y.left = u ≫ (σ i).left) → r₀ ≫ j = j ≫ r → IsIso r → IsGrpPullback G G r φ → (∀ i, (σ i).left ≫ φ = r₀ ≫ (σ i).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (y : Over.mk x ⟶ G), x ≫ r = x → y ^ n = 1 → y.left ≫ φ = y.left := by
  intro X U _ j hN hj₁ hj₂ hj₃ hj₄ G _ n I _ σ r r₀ φ hG hn hσ hgeo hr _ hφ hσφ k _ _ x y hx hy
  have := hG.comm
  have := hG.smooth
  have := hG.separated
  have := IsNormalScheme.of_pred hN
  have hex : ∀ {T : Over X} (z : T ⟶ G), z ^ n = 1 →
      ∃ z' : T ⟶ torsion G n, z' ≫ torsion.ι G n = z := fun z hz =>
    ⟨pullback.lift z (toUnit _) (by rw [GrpTangent.comp_mulN, hz, Hom.one_def]),
      pullback.lift_fst _ _ _⟩
  have hι : torsion.ι G n ^ n = 1 := by
    rw [← GrpTangent.comp_mulN, Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ _) (toUnit_unique _ _))
  have hcl : IsClosedImmersion η[G].left := by
    have : IsClosedImmersion (η[G].left ≫ G.hom) := by
      rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 X))
    exact IsClosedImmersion.of_comp _ G.hom
  have : IsClosedImmersion (torsion.ι G n).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (GrpTangent.isPullback_torsion G n).flip hcl
  have hsep : IsSeparated (torsion G n).hom := by
    rw [← Over.w (torsion.ι G n)]; infer_instance
  choose τ hτ using fun i => hex (σ i) (hσ i)
  have hτ' : ∀ i, (τ i).left ≫ (torsion.ι G n).left = (σ i).left := fun i =>
    congrArg Over.Hom.left (hτ i)
  obtain ⟨y', rfl⟩ := hex y hy
  obtain ⟨i, W, hyW, hW, he⟩ := exists_opens_isOpenImmersion_extending_section X U j hN hj₁ hj₂
    hj₃ hj₄ _ (torsion G n).hom I (fun i => (τ i).left) (GrpTangent.etale_torsion G hn) hsep
    (fun i => Over.w (τ i)) (fun k _ _ u z hz => by
      obtain ⟨i, hi⟩ := hgeo k u (Over.homMk z hz ≫ torsion.ι G n)
        (by rw [← comp_pow, hι, comp_one])
      refine ⟨i, ?_⟩
      rw [← cancel_mono (torsion.ι G n).left, Category.assoc, hτ']
      exact hi) (y'.left (IsLocalRing.closedPoint k))
  have hrange : Set.range y'.left ⊆ Set.range W.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim (α := PrimeSpectrum k) z (IsLocalRing.closedPoint k)]
    exact hyW
  have hw := IsOpenImmersion.lift_fac W.ι y'.left hrange
  have hq : (W.ι ≫ (torsion.ι G n).left) ≫ G.hom = W.ι ≫ (torsion G n).hom := by
    rw [Category.assoc, Over.w]
  have : IsOpenImmersion ((W.ι ≫ (torsion.ι G n).left) ≫ G.hom) := hq ▸ hW
  have hyx : y'.left ≫ (torsion G n).hom = x := Over.w y'
  have := comp_eq_of_extending_section j G.hom (W.ι ≫ (torsion.ι G n).left) (σ i).left (by
      have h := congrArg (pullback.lift (pullback.fst ((W.ι ≫ (torsion.ι G n).left) ≫ G.hom) j)
        (pullback.snd _ j) (by rw [← hq]; exact pullback.condition) ≫ · ≫ (torsion.ι G n).left) he
      simpa only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc, hτ'] using h)
    r r₀ φ hr hφ.1.w (hσφ i) (IsOpenImmersion.lift W.ι y'.left hrange)
    (by rw [hq, Category.assoc, reassoc_of% hw, reassoc_of% hw, reassoc_of% hyx, hyx, hx])
  simpa only [Category.assoc, reassoc_of% hw, Over.comp_left] using this

end GlobalTheory
