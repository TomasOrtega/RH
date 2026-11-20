import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `hψ.1.hom_ext` to reduce the goal to its premises. Set `x₀ : Over.mk (T.hom ≫ f) ⟶ G` to `Over.homMk (x.left ≫ φ) (by show (x.left ≫ φ) ≫ G.hom = T.hom ≫ f`. Rewrite using `[Category.assoc, hφ.1.w, ← Category.assoc, Over.w])`. Set `y₀ : Over.mk (T.hom ≫ f) ⟶ G` to `Over.homMk (y.left ≫ φ) (by show (y.left ≫ φ) ≫ G.hom = T.hom ≫ f`.

Rewrite using `[Category.assoc, hφ.1.w, ← Category.assoc, Over.w])`. Set `x₁ : Over.mk (T.hom ≫ f) ⟶ H` to `Over.homMk ((x ≫ a').left ≫ ψ) (by show ((x ≫ a').left ≫ ψ) ≫ H.hom = T.hom ≫ f`. Rewrite using `[Category.assoc, hψ.1.w, ← Category.assoc, Over.w])`. Set `y₁ : Over.mk (T.hom ≫ f) ⟶ H` to `Over.homMk ((y ≫ a').left ≫ ψ) (by show ((y ≫ a').left ≫ ψ) ≫ H.hom = T.hom ≫ f`. Rewrite using `[Category.assoc, hψ.1.w, ← Category.assoc, Over.w])`.

Establish `e1` using `hφ.2 T x y x₀ y₀ rfl rfl`. Establish `e2` using `hψ.2 T (x ≫ a') (y ≫ a') x₁ y₁ rfl rfl`. Establish `e3 : x₁ = x₀ ≫ a`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `only [x₁, x₀, Over.comp_left, Over.homMk_left, Category.assoc, h]`.

Establish `e4 : y₁ = y₀ ≫ a`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `only [y₁, y₀, Over.comp_left, Over.homMk_left, Category.assoc, h]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Over.comp_left, Category.assoc, h]`.

Use `_ = ((x₀ * y₀) ≫ a).left := by rw [← Category.assoc, ← e1, Over.comp_left]`. Use `_ = (x₁ * y₁).left := by rw [MonObj.mul_comp, e3, e4]`. Use `_ = ((x ≫ a') * (y ≫ a')).left ≫ ψ := e2`. Rewrite using `[Over.w, Over.w]`.
-/
private theorem comp_mul_of_isGrpPullback_lift {G H : Over S} {G' H' : Over S'} [GrpObj G] [GrpObj H]
    [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G f φ)
    (hψ : IsGrpPullback H' H f ψ) (a : G ⟶ H) [IsMonHom a] (a' : G' ⟶ H') (h : a'.left ≫ ψ = φ ≫ a.left)
    {T : Over S'} (x y : T ⟶ G') : (x * y) ≫ a' = (x ≫ a') * (y ≫ a') := by
  apply Over.OverMorphism.ext
  apply hψ.1.hom_ext
  · let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk (x.left ≫ φ) (by
      show (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w])
    let y₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk (y.left ≫ φ) (by
      show (y.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w])
    let x₁ : Over.mk (T.hom ≫ f) ⟶ H := Over.homMk ((x ≫ a').left ≫ ψ) (by
      show ((x ≫ a').left ≫ ψ) ≫ H.hom = T.hom ≫ f
      rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w])
    let y₁ : Over.mk (T.hom ≫ f) ⟶ H := Over.homMk ((y ≫ a').left ≫ ψ) (by
      show ((y ≫ a').left ≫ ψ) ≫ H.hom = T.hom ≫ f
      rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w])
    have e1 := hφ.2 T x y x₀ y₀ rfl rfl
    have e2 := hψ.2 T (x ≫ a') (y ≫ a') x₁ y₁ rfl rfl
    have e3 : x₁ = x₀ ≫ a := by
      apply Over.OverMorphism.ext
      simp only [x₁, x₀, Over.comp_left, Over.homMk_left, Category.assoc, h]
    have e4 : y₁ = y₀ ≫ a := by
      apply Over.OverMorphism.ext
      simp only [y₁, y₀, Over.comp_left, Over.homMk_left, Category.assoc, h]
    calc ((x * y) ≫ a').left ≫ ψ = (x * y).left ≫ φ ≫ a.left := by
          rw [Over.comp_left, Category.assoc, h]
      _ = ((x₀ * y₀) ≫ a).left := by rw [← Category.assoc, ← e1, Over.comp_left]
      _ = (x₁ * y₁).left := by rw [MonObj.mul_comp, e3, e4]
      _ = ((x ≫ a') * (y ≫ a')).left ≫ ψ := e2
  · rw [Over.w, Over.w]

/- English proof (translation)
Establish `key` using `fun (T : Over S') (x y : T ⟶ G') => comp_mul_of_isGrpPullback_lift hφ hψ a a' h x y`. Establish `hmul : μ ≫ a' = (a' ⊗ₘ a') ≫ μ`. Use `key (G' ⊗ G') (fst G' G') (snd G' G')` as an intermediate fact. Simplify `this` using `[Hom.mul_def]`. Establish `h1 : (1 : 𝟙_ (Over S') ⟶ G') = η`.

Rewrite using `[Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]`. Establish `h1' : (1 : 𝟙_ (Over S') ⟶ H') = η`. Rewrite using `[Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]`. Establish `hone : η ≫ a' = η`. Establish `e` using `key _ (1 : 𝟙_ (Over S') ⟶ G') 1`.

Rewrite `e` using `[_root_.mul_one]`. Establish `e' : ((1 : 𝟙_ (Over S') ⟶ G') ≫ a') * 1 = ((1 : 𝟙_ (Over S') ⟶ G') ≫ a') * ((1 : 𝟙_ (Over S') ⟶ G') ≫ a')`. Rewrite using `[_root_.mul_one]`. Conclude with `e`. Establish `e''` using `(mul_left_cancel e').symm`.

Rewrite `e''` using `[h1, h1']`. Conclude with `e''`. Conclude with `{ one_hom := hone, mul_hom := hmul }`.
-/
theorem isMonHom_of_over_isMonHom {G H : Over S} {G' H' : Over S'} [GrpObj G] [GrpObj H] [GrpObj G'] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G f φ) (hψ : IsGrpPullback H' H f ψ)
    (a : G ⟶ H) [IsMonHom a] (a' : G' ⟶ H') (h : a'.left ≫ ψ = φ ≫ a.left) : IsMonHom a' := by
  have key := fun (T : Over S') (x y : T ⟶ G') => comp_mul_of_isGrpPullback_lift hφ hψ a a' h x y
  have hmul : μ ≫ a' = (a' ⊗ₘ a') ≫ μ := by
    have := key (G' ⊗ G') (fst G' G') (snd G' G')
    simpa [Hom.mul_def] using this
  have h1 : (1 : 𝟙_ (Over S') ⟶ G') = η := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have h1' : (1 : 𝟙_ (Over S') ⟶ H') = η := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have hone : η ≫ a' = η := by
    have e := key _ (1 : 𝟙_ (Over S') ⟶ G') 1
    rw [_root_.mul_one] at e
    have e' : ((1 : 𝟙_ (Over S') ⟶ G') ≫ a') * 1 = ((1 : 𝟙_ (Over S') ⟶ G') ≫ a') * ((1 : 𝟙_ (Over S') ⟶ G') ≫ a') := by
      rw [_root_.mul_one]; exact e
    have e'' := (mul_left_cancel e').symm
    rw [h1, h1'] at e''
    exact e''
  exact { one_hom := hone, mul_hom := hmul }

/- English proof (translation)
Establish `h1 : (1 : 𝟙_ (Over S') ⟶ G') = η[G']`. Rewrite using `[Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]`. Set `P : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G` to `Over.homMk ((η[G']).left ≫ φ) (by show ((η[G']).left ≫ φ) ≫ G.hom = (𝟙_ (Over S')).hom ≫ f`. Rewrite using `[Category.assoc, hφ.1.w, ← Category.assoc, Over.w])`. Establish `e` using `hφ.2 (𝟙_ (Over S')) η[G'] η[G'] P P rfl rfl`.

Establish `hP : P * P = P`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[e, ← h1, _root_.mul_one, h1]`. Both sides reduce to the same expression. Establish `hP1 : P = 1` using `mul_eq_left.mp hP`.

Establish `hl` using `congrArg Over.Hom.left hP1`. Rewrite `hl` using `[Hom.one_def, Over.comp_left]`. Express the relevant statement in the definitionally equal form `(η[G']).left ≫ φ = _ at hl`. Rewrite using `[hl]`. Use `congr 1`.
-/
theorem eSec_comp_of_isGrpPullback {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (hφ : IsGrpPullback G' G f φ) : (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have h1 : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  let P : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G := Over.homMk ((η[G']).left ≫ φ) (by
    show ((η[G']).left ≫ φ) ≫ G.hom = (𝟙_ (Over S')).hom ≫ f
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w])
  have e := hφ.2 (𝟙_ (Over S')) η[G'] η[G'] P P rfl rfl
  have hP : P * P = P := by
    apply Over.OverMorphism.ext
    rw [e, ← h1, _root_.mul_one, h1]
    rfl
  have hP1 : P = 1 := mul_eq_left.mp hP
  have hl := congrArg Over.Hom.left hP1
  rw [Hom.one_def, Over.comp_left] at hl
  change (η[G']).left ≫ φ = _ at hl
  rw [hl]
  congr 1

/- English proof (translation)
Take `⟨τ, hτ, hχ, hτi⟩` from `hi`. Introduce `Z' t' g' h₁ h₂`. Set `Z : Over S` to `Over.mk (Z'.hom ≫ f)`. Set `t : Z ⟶ splitTorus S X` to `Over.homMk (t'.left ≫ τ) (by show (t'.left ≫ τ) ≫ (splitTorus S X).hom = Z'.hom ≫ f`. Rewrite using `[Category.assoc, hτ, ← Category.assoc, Over.w])`.

Set `g : Z ⟶ G` to `Over.homMk (g'.left ≫ F) (by show (g'.left ≫ F) ≫ G.hom = Z'.hom ≫ f`. Rewrite using `[Category.assoc, hF.1.w, ← Category.assoc, Over.w])`. Set `x₀ : Z ⟶ G` to `Over.homMk ((t' ≫ i').left ≫ F) (by show ((t' ≫ i').left ≫ F) ≫ G.hom = Z'.hom ≫ f`. Rewrite using `[Category.assoc, hF.1.w, ← Category.assoc, Over.w])`. Establish `hx₀ : t ≫ i = x₀`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `only [t, x₀, Over.comp_left, Over.homMk_left, Category.assoc, hτi]`. Establish `hmul : (t ≫ i * g).left = (t' ≫ i' * g').left ≫ F`. Rewrite using `[hx₀]`. Conclude with `hF.2 Z' (t' ≫ i') g' x₀ g rfl rfl`.

Establish `h₁' : ⊤ ≤ (t ≫ i * g).left ⁻¹ᵁ V`. Rewrite using `[hmul]`. Introduce `x _`. Conclude with `hV (h₁ trivial)`. Establish `h₂' : ⊤ ≤ g.left ⁻¹ᵁ V`.

Introduce `x _`. Conclude with `hV (h₂ trivial)`. Establish `key` using `hu Z t g h₁' h₂'`. Establish `hcong : ∀ (a b : Z'.left ⟶ G.left) (hab : a = b) (ha : ⊤ ≤ a ⁻¹ᵁ V) (hb : ⊤ ≤ b ⁻¹ᵁ V), (a.appLE V ⊤ ha).hom u = (b.appLE V ⊤ hb).hom u`. Introduce `a b hab ha hb`.

Substitute `hab` using the available equality. Both sides reduce to the same expression. Establish `e1 : ((t' ≫ i' * g').left.appLE V' ⊤ h₁).hom ((F.appLE V V' hV).hom u) = (((t' ≫ i' * g').left ≫ F).appLE V ⊤ (by intro x _; exact hV (h₁ trivial))).hom u`. Rewrite using `[← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]`. Establish `e2 : (g'.left.appLE V' ⊤ h₂).hom ((F.appLE V V' hV).hom u) = ((g'.left ≫ F).appLE V ⊤ (by intro x _; exact hV (h₂ trivial))).hom u`.

Rewrite using `[← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]`. Establish `hc : (t.left.appTop).hom (charUnit S X χ).val = (t'.left.appTop).hom (charUnit S' X χ).val` using `by show ((t'.left ≫ τ).appTop).hom _ = _`. Rewrite using `[Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hχ]`. Rewrite using `[e1, e2]`. Conclude with `(hcong _ _ hmul.symm _ h₁').trans (key.trans (congrArg₂ (· * ·) hc (hcong _ _ rfl h₂' _)))`.
-/
theorem IsWt.pull {X : Type} [AddCommGroup X] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'}
    (hi : TorusCompat f F i' i) {V : G.left.Opens} {V' : G'.left.Opens} (hV : V' ≤ F ⁻¹ᵁ V) {u : Γ(G.left, V)}
    {χ : X} (hu : IsWt i V u χ) : IsWt i' V' ((F.appLE V V' hV).hom u) χ := by
  obtain ⟨τ, hτ, hχ, hτi⟩ := hi
  intro Z' t' g' h₁ h₂
  let Z : Over S := Over.mk (Z'.hom ≫ f)
  let t : Z ⟶ splitTorus S X := Over.homMk (t'.left ≫ τ) (by
    show (t'.left ≫ τ) ≫ (splitTorus S X).hom = Z'.hom ≫ f
    rw [Category.assoc, hτ, ← Category.assoc, Over.w])
  let g : Z ⟶ G := Over.homMk (g'.left ≫ F) (by
    show (g'.left ≫ F) ≫ G.hom = Z'.hom ≫ f
    rw [Category.assoc, hF.1.w, ← Category.assoc, Over.w])
  let x₀ : Z ⟶ G := Over.homMk ((t' ≫ i').left ≫ F) (by
    show ((t' ≫ i').left ≫ F) ≫ G.hom = Z'.hom ≫ f
    rw [Category.assoc, hF.1.w, ← Category.assoc, Over.w])
  have hx₀ : t ≫ i = x₀ := by
    apply Over.OverMorphism.ext
    simp only [t, x₀, Over.comp_left, Over.homMk_left, Category.assoc, hτi]
  have hmul : (t ≫ i * g).left = (t' ≫ i' * g').left ≫ F := by
    rw [hx₀]
    exact hF.2 Z' (t' ≫ i') g' x₀ g rfl rfl
  have h₁' : ⊤ ≤ (t ≫ i * g).left ⁻¹ᵁ V := by
    rw [hmul]
    intro x _
    exact hV (h₁ trivial)
  have h₂' : ⊤ ≤ g.left ⁻¹ᵁ V := by
    intro x _
    exact hV (h₂ trivial)
  have key := hu Z t g h₁' h₂'
  have hcong : ∀ (a b : Z'.left ⟶ G.left) (hab : a = b) (ha : ⊤ ≤ a ⁻¹ᵁ V) (hb : ⊤ ≤ b ⁻¹ᵁ V),
      (a.appLE V ⊤ ha).hom u = (b.appLE V ⊤ hb).hom u := by
    intro a b hab ha hb
    subst hab
    rfl
  have e1 : ((t' ≫ i' * g').left.appLE V' ⊤ h₁).hom ((F.appLE V V' hV).hom u) =
      (((t' ≫ i' * g').left ≫ F).appLE V ⊤ (by intro x _; exact hV (h₁ trivial))).hom u := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have e2 : (g'.left.appLE V' ⊤ h₂).hom ((F.appLE V V' hV).hom u) =
      ((g'.left ≫ F).appLE V ⊤ (by intro x _; exact hV (h₂ trivial))).hom u := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have hc : (t.left.appTop).hom (charUnit S X χ).val = (t'.left.appTop).hom (charUnit S' X χ).val := by
    show ((t'.left ≫ τ).appTop).hom _ = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hχ]
  rw [e1, e2]
  exact (hcong _ _ hmul.symm _ h₁').trans (key.trans (congrArg₂ (· * ·) hc (hcong _ _ rfl h₂' _)))

/- English proof (translation)
Introduce `S S' f X _ G _ G' _ F hF Q`. Use `letI := Q.grp`. Use `letI := Q.comm`. Use `haveI := Q.q_hom`. Use `haveI := Q.i_hom`.

Take `⟨i', hi', -⟩` from `existsUnique_torusCompat hF.1 Q.i`. Use `haveI : IsMonHom i' := TorusCompat.isMonHom hF hi'`. Establish `hB` using `isGrpPullback_pullback Q.B f`. Set `q' : G' ⟶ (Over.pullback f).obj Q.B` to `Over.homMk (pullback.lift (F ≫ Q.q.left) G'.hom (by rw [Category.assoc, Over.w Q.q, hF.1.w])) (by exact pullback.lift_snd _ _ _)`. Establish `hq'fst : q'.left ≫ pullback.fst Q.B.hom f = F ≫ Q.q.left` using `pullback.lift_fst _ _ _`.

Use `haveI : IsMonHom q' := isMonHom_of_over_isMonHom hF hB Q.q q' hq'fst`. Establish `hBsq : IsPullback F q'.left Q.q.left (pullback.fst Q.B.hom f)`. Use `IsPullback.of_bot ?_ hq'fst.symm (IsPullback.of_hasPullback Q.B.hom f)` and prove the remaining obligations. Establish `e1 : q'.left ≫ pullback.snd Q.B.hom f = G'.hom` using `pullback.lift_snd _ _ _`. Rewrite using `[e1, Over.w Q.q]`.

Conclude with `hF.1`. Establish `hAb : IsAbelianScheme ((Over.pullback f).obj Q.B)` using `by haveI := Q.isAb.smooth haveI := Q.isAb.proper haveI := Q.isAb.geomConnected`. Conclude with `⟨inferInstance, by simp only [Over.pullback_obj_hom]; infer_instance, by simp only [Over.pullback_obj_hom]; infer_instance, by simp only [Over.pullback_obj_hom]; infer_instance⟩`. Establish `hη : (η[(Over.pullback f).obj Q.B]).left ≫ pullback.fst Q.B.hom f = f ≫ (η[Q.B]).left` using `eSec_comp_of_isGrpPullback hB`. Establish `hT' : (toUnit (splitTorus S' X)).left = (splitTorus S' X).hom`.

Use `Over.w (toUnit (splitTorus S' X))` as an intermediate fact. Simplify using `using this`. Establish `hT : (toUnit (splitTorus S X)).left = (splitTorus S X).hom`. Use `Over.w (toUnit (splitTorus S X))` as an intermediate fact. Simplify using `using this`.

Establish `hker0 : IsPullback Q.i.left (splitTorus S X).hom Q.q.left (η[Q.B]).left`. Establish `h0 : IsPullback Q.i.left (toUnit (splitTorus S X)).left Q.q.left (η[Q.B]).left` using `Q.isKernel.map (Over.forget S)`. Rewrite `h0` using `[hT]`. Conclude with `h0`. Establish `hcomp : IsPullback (i'.left ≫ F) (splitTorus S' X).hom Q.q.left ((η[(Over.pullback f).obj Q.B]).left ≫ pullback.fst Q.B.hom f)`.

Rewrite using `[← torusCompat_iff.mp hi', hη]`. Conclude with `(SplitTorus.isGrpPullback_bcMap f X).1.paste_horiz hker0`. Establish `hcommA : i'.left ≫ q'.left = (splitTorus S' X).hom ≫ (η[(Over.pullback f).obj Q.B]).left`. Apply `hB.1.hom_ext` to reduce the goal to its premises. Simplify `hcomp.w` using `only [Category.assoc, hq'fst]`.

Rewrite using `[Category.assoc, Over.w q', Over.w i', Category.assoc, Over.w η[(Over.pullback f).obj Q.B]]`. Simplify using the standard rewrite rules. Establish `hA : IsPullback i'.left (splitTorus S' X).hom q'.left (η[(Over.pullback f).obj Q.B]).left` using `IsPullback.of_right hcomp hcommA hBsq`. Establish `hker : IsPullback i' (toUnit (splitTorus S' X)) q' η`. Apply `IsPullback.of_map (Over.forget S')` to reduce the goal to its premises.

Apply `Over.OverMorphism.ext show i'.left ≫ q'.left = (toUnit (splitTorus S' X)).left ≫ (η[(Over.pullback f).obj Q.B]).left` to reduce the goal to its premises. Rewrite using `[hT']`. Conclude with `hcommA`. Use `show IsPullback i'.left (toUnit (splitTorus S' X)).left q'.left (η[(Over.pullback f).obj Q.B]).left`. Rewrite using `[hT']`.

Conclude with `hA`. Establish `hloc : ∀ (b : ((Over.pullback f).obj Q.B).left) (χ : X), ∃ V, b ∈ V ∧ ∃ u : (Γ(G'.left, q'.left ⁻¹ᵁ V))ˣ, IsWt i' (q'.left ⁻¹ᵁ V) (↑u) χ`. Introduce `b χ`. Take `⟨V, hbV, u, hu⟩` from `Q.loc ((pullback.fst Q.B.hom f).base b) χ`. Establish `hle : q'.left ⁻¹ᵁ (pullback.fst Q.B.hom f ⁻¹ᵁ V) ≤ F ⁻¹ᵁ (Q.q.left ⁻¹ᵁ V)`.

Rewrite using `[← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hq'fst]`. Use `⟨pullback.fst Q.B.hom f ⁻¹ᵁ V, hbV, Units.map (F.appLE _ _ hle).hom.toMonoidHom u, ?_⟩` and prove the remaining obligations. Conclude with `IsWt.pull hF hi' hle hu`. Conclude with `⟨TQ.mk _ hAb q' i' inferInstance inferInstance (MorphismProperty.of_isPullback (P := @Flat) hBsq Q.q_flat) (MorphismProperty.of_isPullback (P := @Surjective) hBsq Q.q_surj) (MorphismProperty.of_isPullback (P := @IsAffineHom) hBsq Q.q_affine) hker hloc, hi'⟩`.
-/
theorem exists_tq_baseChange : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G]
    (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F →
    ∀ Q : TQ G X, ∃ Q' : TQ G' X, TorusCompat f F Q'.i Q.i := by
  intro S S' f X _ G _ G' _ F hF Q
  letI := Q.grp
  letI := Q.comm
  haveI := Q.q_hom
  haveI := Q.i_hom
  obtain ⟨i', hi', -⟩ := existsUnique_torusCompat hF.1 Q.i
  haveI : IsMonHom i' := TorusCompat.isMonHom hF hi'
  have hB := isGrpPullback_pullback Q.B f
  let q' : G' ⟶ (Over.pullback f).obj Q.B :=
    Over.homMk (pullback.lift (F ≫ Q.q.left) G'.hom (by rw [Category.assoc, Over.w Q.q, hF.1.w]))
      (by exact pullback.lift_snd _ _ _)
  have hq'fst : q'.left ≫ pullback.fst Q.B.hom f = F ≫ Q.q.left := pullback.lift_fst _ _ _
  haveI : IsMonHom q' := isMonHom_of_over_isMonHom hF hB Q.q q' hq'fst
  have hBsq : IsPullback F q'.left Q.q.left (pullback.fst Q.B.hom f) := by
    refine IsPullback.of_bot ?_ hq'fst.symm (IsPullback.of_hasPullback Q.B.hom f)
    have e1 : q'.left ≫ pullback.snd Q.B.hom f = G'.hom := pullback.lift_snd _ _ _
    rw [e1, Over.w Q.q]
    exact hF.1
  have hAb : IsAbelianScheme ((Over.pullback f).obj Q.B) := by
    haveI := Q.isAb.smooth
    haveI := Q.isAb.proper
    haveI := Q.isAb.geomConnected
    exact ⟨inferInstance, by simp only [Over.pullback_obj_hom]; infer_instance,
      by simp only [Over.pullback_obj_hom]; infer_instance, by simp only [Over.pullback_obj_hom]; infer_instance⟩
  have hη : (η[(Over.pullback f).obj Q.B]).left ≫ pullback.fst Q.B.hom f = f ≫ (η[Q.B]).left :=
    eSec_comp_of_isGrpPullback hB
  have hT' : (toUnit (splitTorus S' X)).left = (splitTorus S' X).hom := by
    have := Over.w (toUnit (splitTorus S' X))
    simpa using this
  have hT : (toUnit (splitTorus S X)).left = (splitTorus S X).hom := by
    have := Over.w (toUnit (splitTorus S X))
    simpa using this
  have hker0 : IsPullback Q.i.left (splitTorus S X).hom Q.q.left (η[Q.B]).left := by
    have h0 : IsPullback Q.i.left (toUnit (splitTorus S X)).left Q.q.left (η[Q.B]).left :=
      Q.isKernel.map (Over.forget S)
    rw [hT] at h0
    exact h0
  have hcomp : IsPullback (i'.left ≫ F) (splitTorus S' X).hom Q.q.left
      ((η[(Over.pullback f).obj Q.B]).left ≫ pullback.fst Q.B.hom f) := by
    rw [← torusCompat_iff.mp hi', hη]
    exact (SplitTorus.isGrpPullback_bcMap f X).1.paste_horiz hker0
  have hcommA : i'.left ≫ q'.left = (splitTorus S' X).hom ≫ (η[(Over.pullback f).obj Q.B]).left := by
    apply hB.1.hom_ext
    · simpa only [Category.assoc, hq'fst] using hcomp.w
    · rw [Category.assoc, Over.w q', Over.w i', Category.assoc, Over.w η[(Over.pullback f).obj Q.B]]
      simp
  have hA : IsPullback i'.left (splitTorus S' X).hom q'.left (η[(Over.pullback f).obj Q.B]).left :=
    IsPullback.of_right hcomp hcommA hBsq
  have hker : IsPullback i' (toUnit (splitTorus S' X)) q' η := by
    apply IsPullback.of_map (Over.forget S')
    · apply Over.OverMorphism.ext
      show i'.left ≫ q'.left = (toUnit (splitTorus S' X)).left ≫ (η[(Over.pullback f).obj Q.B]).left
      rw [hT']
      exact hcommA
    · show IsPullback i'.left (toUnit (splitTorus S' X)).left q'.left (η[(Over.pullback f).obj Q.B]).left
      rw [hT']
      exact hA
  have hloc : ∀ (b : ((Over.pullback f).obj Q.B).left) (χ : X),
      ∃ V, b ∈ V ∧ ∃ u : (Γ(G'.left, q'.left ⁻¹ᵁ V))ˣ, IsWt i' (q'.left ⁻¹ᵁ V) (↑u) χ := by
    intro b χ
    obtain ⟨V, hbV, u, hu⟩ := Q.loc ((pullback.fst Q.B.hom f).base b) χ
    have hle : q'.left ⁻¹ᵁ (pullback.fst Q.B.hom f ⁻¹ᵁ V) ≤ F ⁻¹ᵁ (Q.q.left ⁻¹ᵁ V) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hq'fst]
    refine ⟨pullback.fst Q.B.hom f ⁻¹ᵁ V, hbV, Units.map (F.appLE _ _ hle).hom.toMonoidHom u, ?_⟩
    exact IsWt.pull hF hi' hle hu
  exact ⟨TQ.mk _ hAb q' i' inferInstance inferInstance
    (MorphismProperty.of_isPullback (P := @Flat) hBsq Q.q_flat)
    (MorphismProperty.of_isPullback (P := @Surjective) hBsq Q.q_surj)
    (MorphismProperty.of_isPullback (P := @IsAffineHom) hBsq Q.q_affine) hker hloc, hi'⟩

end GlobalTheory.UU
end
