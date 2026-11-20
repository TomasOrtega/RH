import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSchemeCubicalBundleExistsAndMaps
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PkgBaseChange
open GlobalTheory.UU

/- English proof (translation)
Set `s : G' ⟶ G3 G'` to `lift (𝟙 G') (lift 1 1)`. Establish `hs : s.left ≫ (fst G' (G' ⊗ G')).left = 𝟙 _`. Rewrite using `[← Over.comp_left, lift_fst]`. Both sides reduce to the same expression. Establish `hw : s.left ≫ (G3 G').hom = G'.hom` using `Over.w s`.

Introduce `g`. Take `⟨c, hc⟩` from `h3 ((fst G' (G' ⊗ G')).left.appTop.hom g)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `e1 : G'.hom.appTop.hom c = s.left.appTop.hom ((G3 G').hom.appTop.hom c)`. Rewrite using `[← hw, Scheme.Hom.comp_appTop]`.

Both sides reduce to the same expression. Establish `e2 : s.left.appTop.hom ((fst G' (G' ⊗ G')).left.appTop.hom g) = g`. Rewrite using `[← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs]`. Both sides reduce to the same expression. Rewrite using `[e1, hc, e2]`.
-/
theorem surjective_of_cube {S' : Scheme.{0}} (G' : Over S') [GrpObj G']
    (h3 : Function.Surjective (G3 G').hom.appTop.hom) : Function.Surjective G'.hom.appTop.hom := by
  let s : G' ⟶ G3 G' := lift (𝟙 G') (lift 1 1)
  have hs : s.left ≫ (fst G' (G' ⊗ G')).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hw : s.left ≫ (G3 G').hom = G'.hom := Over.w s
  intro g
  obtain ⟨c, hc⟩ := h3 ((fst G' (G' ⊗ G')).left.appTop.hom g)
  refine ⟨c, ?_⟩
  have e1 : G'.hom.appTop.hom c = s.left.appTop.hom ((G3 G').hom.appTop.hom c) := by
    rw [← hw, Scheme.Hom.comp_appTop]; rfl
  have e2 : s.left.appTop.hom ((fst G' (G' ⊗ G')).left.appTop.hom g) = g := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs]; rfl
  rw [e1, hc, e2]

/- English proof (translation)
Introduce `S S' f G _ _ G' _ _ F hw mul h3 M M' ⟨w, hg⟩`. Establish `h1` using `surjective_of_cube G' h3`. Take `⟨rig, hr, c, s, hs, h₂, h₃, H⟩` from `exists_isCPMap M mul M'.L.L M'.L.isLB w hg`. Set `N : CP G'` to `⟨⟨M'.L.L, rig, M'.L.isLB, hr⟩, c, s, hs, h₂, h₃⟩`. Take `⟨a, ha⟩` from `GlobalTheory.AbPackage.exists_unit_ratio M'.L.isLB (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) hr M'.L.rigGen`.

Set `b : Γ(G'.left, ⊤)ˣ` to `pullU G'.hom ⊤ a`. Establish `es : ∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (J), Good M'.L.L z J → val s r z J = val M'.sym r z J` using `gen_unique M'.L.isLB G'.hom (1 : 𝟙_ (Over S') ⟶ G').left (Over.w _) h1 hs M'.sym_gen fun y J hJ => (N.val_sym_one hJ).trans (M'.val_sym_one hJ).symm`. Establish `ec : ∀ (T : Over S') (z : T.left) (J), Good M'.L.L z J → ∀ x y u : T ⟶ G', cubV c z J x y u = cubV M'.c z J x y u` using `fun T z J hJ x y u => gen_unique M'.L.isLB (φ := thφ G' (x3 G')) (ε := thε) (G3 G').hom (lift (1 : 𝟙_ (Over S') ⟶ G') (lift 1 1)).left (Over.w _) h3 c.isGen M'.c.isGen (fun y J hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV M'.c hJ).face 1 1).symm) _ _ z J hJ`. Use `⟨scaleGen b w, mul, scaleGen_isGen b hg, fun T z J' J hJ' hJ W hW => ?_⟩` and prove the remaining obligations. Take `⟨W₀, hW₀⟩ : ∃ W₀ : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ, ∀ x, W₀ x = gw w x.left z (J (x.left ≫ F)) (J' x.left)` from `⟨_, fun _ => rfl⟩`.

Take `⟨α, hα⟩ : ∃ α : (T.left.presheaf.stalk z)ˣ, α = gm (Y` from `T.left) T.hom z ⊤ a := ⟨_, rfl⟩`. Establish `e : ∀ x, W x = α * W₀ x` using `fun x => by`. Establish `hm : x.left z ∈ (M.L.L.pull F).U (fun _ => J (x.left ≫ F)) ⊓ M'.L.L.U (J' x.left)` using `⟨mem_pull.2 (hJ (x.left ≫ F)), hJ' x.left⟩`. Rewrite using `[hW, hW₀, hα, ← Over.w x]`. Conclude with `(map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res x.left z le_top hm b).trans (gm_pull x.left G'.hom z ⊤ trivial a)) rfl)`.

Take `⟨a₁, a₂, a₃⟩` from `H.vals T z J' J hJ' hJ W₀ hW₀`. Use `⟨?_, fun x => ?_, fun x y u => ?_⟩` and prove the remaining obligations. Use `a₁.trans ((congrArg (W₀ 1 * ·) (ha _ T.hom z J' hJ')).trans ?_)` and prove the remaining obligations. Rewrite using `[e, hα, mul_comm _ (W₀ 1), _root_.mul_assoc]`. Establish `q : val M.sym (x.left ≫ F) z J * W₀ x = W₀ x⁻¹ * val M'.sym x.left z J'` using `(a₂ x).trans (congrArg (W₀ x⁻¹ * ·) (es _ x.left z J' hJ'))`.

Rewrite using `[e, e, mul_left_comm, q, _root_.mul_assoc]`. Establish `q` using `(a₃ x y u).trans (congrArg (W₀ (x * y * u) * W₀ x * W₀ y * W₀ u * ·) (ec T z J' hJ' x y u))`. Simplify using `only [e]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `q'` using `congrArg Additive.ofMul q`.

Simplify using `only [ofMul_mul] at q' ⊢`. Take the linear combination `(norm := abel) q'`.
-/
theorem exists_isCPMap_of_lbIso : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
    (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (F : G'.left ⟶ G.left) (hw : F ≫ G.hom = G'.hom ≫ f),
    (∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y) →
    Function.Surjective (G3 G').hom.appTop.hom → ∀ (P : GlobalTheory.UU.CP G) (P' : GlobalTheory.UU.CP G'),
    LBIso P'.L.L (P.L.L.pull F) → ∃ w, GlobalTheory.UU.IsCPMap P' P f F hw w := by
  intro S S' f G _ _ G' _ _ F hw mul h3 M M' ⟨w, hg⟩
  have h1 := surjective_of_cube G' h3
  obtain ⟨rig, hr, c, s, hs, h₂, h₃, H⟩ := exists_isCPMap M mul M'.L.L M'.L.isLB w hg
  let N : CP G' := ⟨⟨M'.L.L, rig, M'.L.isLB, hr⟩, c, s, hs, h₂, h₃⟩
  obtain ⟨a, ha⟩ := GlobalTheory.AbPackage.exists_unit_ratio M'.L.isLB (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1)
    hr M'.L.rigGen
  let b : Γ(G'.left, ⊤)ˣ := pullU G'.hom ⊤ a
  have es : ∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (J), Good M'.L.L z J → val s r z J = val M'.sym r z J :=
    gen_unique M'.L.isLB G'.hom (1 : 𝟙_ (Over S') ⟶ G').left (Over.w _) h1 hs M'.sym_gen
      fun y J hJ => (N.val_sym_one hJ).trans (M'.val_sym_one hJ).symm
  have ec : ∀ (T : Over S') (z : T.left) (J), Good M'.L.L z J → ∀ x y u : T ⟶ G',
      cubV c z J x y u = cubV M'.c z J x y u := fun T z J hJ x y u =>
    gen_unique M'.L.isLB (φ := thφ G' (x3 G')) (ε := thε) (G3 G').hom
      (lift (1 : 𝟙_ (Over S') ⟶ G') (lift 1 1)).left (Over.w _) h3 c.isGen M'.c.isGen
      (fun y J hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV M'.c hJ).face 1 1).symm) _ _ z J hJ
  refine ⟨scaleGen b w, mul, scaleGen_isGen b hg, fun T z J' J hJ' hJ W hW => ?_⟩
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
    ∀ x, W₀ x = gw w x.left z (J (x.left ≫ F)) (J' x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : (T.left.presheaf.stalk z)ˣ, α = gm (Y := T.left) T.hom z ⊤ a := ⟨_, rfl⟩
  have e : ∀ x, W x = α * W₀ x := fun x => by
    have hm : x.left z ∈ (M.L.L.pull F).U (fun _ => J (x.left ≫ F)) ⊓ M'.L.L.U (J' x.left) :=
      ⟨mem_pull.2 (hJ (x.left ≫ F)), hJ' x.left⟩
    rw [hW, hW₀, hα, ← Over.w x]
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res x.left z le_top hm b).trans
      (gm_pull x.left G'.hom z ⊤ trivial a)) rfl)
  obtain ⟨a₁, a₂, a₃⟩ := H.vals T z J' J hJ' hJ W₀ hW₀
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · refine a₁.trans ((congrArg (W₀ 1 * ·) (ha _ T.hom z J' hJ')).trans ?_)
    rw [e, hα, mul_comm _ (W₀ 1), _root_.mul_assoc]
  · have q : val M.sym (x.left ≫ F) z J * W₀ x = W₀ x⁻¹ * val M'.sym x.left z J' :=
      (a₂ x).trans (congrArg (W₀ x⁻¹ * ·) (es _ x.left z J' hJ'))
    rw [e, e, mul_left_comm, q, _root_.mul_assoc]
  · have q := (a₃ x y u).trans (congrArg (W₀ (x * y * u) * W₀ x * W₀ y * W₀ u * ·) (ec T z J' hJ' x y u))
    simp only [e]
    apply Additive.ofMul.injective
    have q' := congrArg Additive.ofMul q
    simp only [ofMul_mul] at q' ⊢
    linear_combination (norm := abel) q'

end GlobalTheory.PkgBaseChange
