import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIntegralTensorLeftOfSmoothGrpObj
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

/- English proof (translation)
Take `⟨a, ha⟩` from `φ.stalkMap_surjective y (Y'.presheaf.germ U' y hy f')`. Establish `hau : IsUnit a`. Establish `: IsUnit (φ.stalkMap y a)` using `ha ▸ hf'.map _`. Conclude with `(isUnit_map_iff (φ.stalkMap y).hom a).1 this`. Take `⟨U₀, hU₀, f₀, rfl⟩` from `Y.presheaf.germ_exist a`.

Establish `hb : φ y ∈ Y.basicOpen f₀` using `(Y.mem_basicOpen f₀ _ hU₀).2 hau`. Set `f : Γ(Y, Y.basicOpen f₀)` to `Y.presheaf.map (homOfLE (Y.basicOpen_le f₀)).op f₀`. Establish `hf : IsUnit f` using `RingedSpace.isUnit_res_basicOpen Y.toRingedSpace f₀`. Establish `e : Y'.presheaf.germ (φ ⁻¹ᵁ Y.basicOpen f₀) y hb (φ.app _ f) = Y'.presheaf.germ U' y hy f'`. Rewrite using `[← φ.germ_stalkMap_apply _ y hb, ← ha]`.

Use `congr 1`. Conclude with `Y.presheaf.germ_res_apply _ _ _ _`. Take `⟨V, hV, i₁, i₂, hi⟩` from `Y'.presheaf.germ_eq y _ _ _ _ e`. Use `⟨_, f, V, hV, hf, i₂.le, i₁.le, fun Z r h h₁ h₂ => ?_⟩` and prove the remaining obligations. Establish `a₁` using `congrArg (fun q => q.hom (φ.app _ f)) (r.map_appLE h i₁.op)`.

Establish `a₂` using `congrArg (fun q => q.hom f') (r.map_appLE h i₂.op)`. Establish `a₃` using `congrArg (fun q => q.hom f) (Scheme.Hom.comp_appLE r φ _ ⊤ h₁)`. Conclude with `a₃.trans (a₁.symm.trans ((congrArg (r.appLE V ⊤ h).hom hi).trans a₂))`.
-/
private theorem spread_unit {Y Y' : Scheme.{0}} (φ : Y' ⟶ Y) [SurjectiveOnStalks φ] (U' : Y'.Opens) (f' : Γ(Y', U'))
    (hf' : IsUnit f') (y : Y') (hy : y ∈ U') :
    ∃ (U : Y.Opens) (f : Γ(Y, U)) (V : Y'.Opens), y ∈ V ∧ IsUnit f ∧ V ≤ U' ∧ V ≤ φ ⁻¹ᵁ U ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (_ : ⊤ ≤ r ⁻¹ᵁ V) (h₁ : ⊤ ≤ (r ≫ φ) ⁻¹ᵁ U) (h₂ : ⊤ ≤ r ⁻¹ᵁ U'),
        ((r ≫ φ).appLE U ⊤ h₁).hom f = (r.appLE U' ⊤ h₂).hom f' := by
  obtain ⟨a, ha⟩ := φ.stalkMap_surjective y (Y'.presheaf.germ U' y hy f')
  have hau : IsUnit a := by
    have : IsUnit (φ.stalkMap y a) := ha ▸ hf'.map _
    exact (isUnit_map_iff (φ.stalkMap y).hom a).1 this
  obtain ⟨U₀, hU₀, f₀, rfl⟩ := Y.presheaf.germ_exist a
  have hb : φ y ∈ Y.basicOpen f₀ := (Y.mem_basicOpen f₀ _ hU₀).2 hau
  let f : Γ(Y, Y.basicOpen f₀) := Y.presheaf.map (homOfLE (Y.basicOpen_le f₀)).op f₀
  have hf : IsUnit f := RingedSpace.isUnit_res_basicOpen Y.toRingedSpace f₀
  have e : Y'.presheaf.germ (φ ⁻¹ᵁ Y.basicOpen f₀) y hb (φ.app _ f) = Y'.presheaf.germ U' y hy f' := by
    rw [← φ.germ_stalkMap_apply _ y hb, ← ha]
    congr 1
    exact Y.presheaf.germ_res_apply _ _ _ _
  obtain ⟨V, hV, i₁, i₂, hi⟩ := Y'.presheaf.germ_eq y _ _ _ _ e
  refine ⟨_, f, V, hV, hf, i₂.le, i₁.le, fun Z r h h₁ h₂ => ?_⟩
  have a₁ := congrArg (fun q => q.hom (φ.app _ f)) (r.map_appLE h i₁.op)
  have a₂ := congrArg (fun q => q.hom f') (r.map_appLE h i₂.op)
  have a₃ := congrArg (fun q => q.hom f) (Scheme.Hom.comp_appLE r φ _ ⊤ h₁)
  exact a₃.trans (a₁.symm.trans ((congrArg (r.appLE V ⊤ h).hom hi).trans a₂))

/- English proof (translation)
Use `⟨(Dense.preimage g.denseRange hf).mono ?_⟩` and prove the remaining obligations. Introduce and unpack `a ⟨b, hb⟩`. Take `⟨p, hp, -⟩` from `Scheme.exists_preimage_of_isPullback h a b hb.symm`. Conclude with `⟨p, hp⟩`.
-/
private theorem isDominant_of_isPullback {P X Y S : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : IsPullback fst snd f g) (hf : IsOpenMap f) [IsDominant g] : IsDominant fst := by
  refine ⟨(Dense.preimage g.denseRange hf).mono ?_⟩
  rintro a ⟨b, hb⟩
  obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback h a b hb.symm
  exact ⟨p, hp⟩

/- English proof (translation)
Introduce `hW k _ _ C _ hC K _ x hx G _ hG X _ _ _ u hu G' _ φ u' hφ hT χ U' f' ⟨y, hy⟩ hf' hwt`. Use `LieSemineg.isIntegral_curve hC.1 hC.2.2` as an intermediate fact. Use `hx.1` as an intermediate fact. Use `hx.2` as an intermediate fact. Use `hG.smooth` as an intermediate fact.

Use `hG.geomConnected` as an intermediate fact. Establish `hu' : IsMonHom u'` using `hT.isMonHom hφ`. Take `⟨-, -, -, -, h1, -, -, h2, -⟩` from `(splitTorus_properties C).1 X`. Establish `: Smooth (splitTorus C X).hom` using `SmoothOfRelativeDimension.smooth (Module.finrank ℤ X) _`. Establish `: Smooth (splitTorus C X ⊗ G).hom` using `inferInstanceAs (Smooth (pullback.fst (splitTorus C X).hom G.hom ≫ (splitTorus C X).hom))`.

Establish `: GeometricallyConnected (splitTorus C X ⊗ G).hom` using `GeometricallyConnected.comp (pullback.fst (splitTorus C X).hom G.hom) (splitTorus C X).hom`. Establish `hI : IsIntegral (splitTorus C X ⊗ G).left` using `isIntegral_of_isPullback_of_smooth (IsPullback.id_horiz (splitTorus C X ⊗ G).hom)`. Establish `: IsPreimmersion φ` using `MorphismProperty.of_isPullback (P := @IsPreimmersion) hφ.1.flip hx.2`. Take `⟨U, f, V, hV, hf, hVU', hVU, H⟩` from `spread_unit φ U' f' hf' y hy`. Use `⟨U, f, ⟨φ y, hVU hV⟩, hf, ?_⟩` and prove the remaining obligations.

Set `τ` to `SplitTorus.bcMap x X`. Set `P'` to `splitTorus (Sp K) X ⊗ G'`. Set `ψ : P'.left ⟶ (splitTorus C X ⊗ G).left` to `pullback.lift ((fst _ _ : P' ⟶ _).left ≫ τ) ((snd _ _ : P' ⟶ _).left ≫ φ) (by`. Rewrite using `[Category.assoc, Category.assoc, SplitTorus.bcMap_hom, hφ.1.w, Over.w_assoc, Over.w_assoc])`. Establish `hψ₁ : ψ ≫ (fst _ _ : splitTorus C X ⊗ G ⟶ _).left = (fst _ _ : P' ⟶ _).left ≫ τ` using `pullback.lift_fst _ _ _`.

Establish `hψ₂ : ψ ≫ (snd _ _ : splitTorus C X ⊗ G ⟶ _).left = (snd _ _ : P' ⟶ _).left ≫ φ` using `pullback.lift_snd _ _ _`. Establish `sq : IsPullback ψ P'.hom (splitTorus C X ⊗ G).hom x`. Establish `s₁ : IsPullback (fst _ _ : splitTorus C X ⊗ G ⟶ _).left (snd _ _ : splitTorus C X ⊗ G ⟶ _).left (splitTorus C X).hom G.hom` using `IsPullback.of_hasPullback _ _`. Establish `s₂ : IsPullback (fst _ _ : P' ⟶ _).left (snd _ _ : P' ⟶ _).left (splitTorus (Sp K) X).hom G'.hom` using `IsPullback.of_hasPullback _ _`. Establish `s₃` using `s₂.paste_horiz (SplitTorus.isPullback_bcMap x X)`.

Rewrite `s₃` using `[← hψ₁, ← hφ.1.w]`. Establish `s₄` using `(s₃.of_right hψ₂ s₁).paste_vert hφ.1`. Rewrite `s₄` using `[Over.w, Over.w]`. Then use the resulting hypothesis. Establish `: IsIntegral P'.left` using `isIntegral_of_isPullback_of_smooth sq`. Establish `: IsDominant ψ` using `isDominant_of_isPullback sq (splitTorus C X ⊗ G).hom.isOpenMap`.

Set `O : P'.left.Opens` to `((fst _ _ ≫ u') * snd _ _ : P' ⟶ G').left ⁻¹ᵁ V ⊓ (snd _ _ : P' ⟶ G').left ⁻¹ᵁ V`. Establish `hO : (O : Set P'.left).Nonempty`. Set `s : G' ⟶ P'` to `lift 1 (𝟙 G')`. Establish `e₁ : s ≫ ((fst _ _ ≫ u') * snd _ _ : P' ⟶ G') = 𝟙 G'`. Rewrite using `[MonObj.comp_mul, lift_fst_assoc, lift_snd, MonObj.one_comp, _root_.one_mul]`.

Establish `e₂ : s ≫ (snd _ _ : P' ⟶ G') = 𝟙 G'` using `lift_snd _ _`. Use `⟨s.left y, ?_, ?_⟩` and prove the remaining obligations. Use `show (s ≫ ((fst _ _ ≫ u') * snd _ _ : P' ⟶ G')).left y ∈ V`. Rewrite using `[e₁]`. Conclude with `hV`.

Use `show (s ≫ (snd _ _ : P' ⟶ G')).left y ∈ V`. Rewrite using `[e₂]`. Conclude with `hV`. Establish `: IsDominant O.ι` using `⟨by`. Use `O.isOpen.dense hO` as an intermediate fact.

Rewrite using `[DenseRange, Scheme.Opens.range_ι]⟩` and apply the resulting hypothesis. Set `Z' : Over (Sp K)` to `Over.mk (O.ι ≫ P'.hom)`. Set `j : Z' ⟶ P'` to `Over.homMk O.ι rfl`. Set `t' : Z' ⟶ splitTorus (Sp K) X` to `j ≫ fst _ _`. Set `g' : Z' ⟶ G'` to `j ≫ snd _ _`.

Set `t : Over.mk (Z'.hom ≫ x) ⟶ splitTorus C X` to `Over.homMk (t'.left ≫ τ) (by`. Rewrite using `[Category.assoc, SplitTorus.bcMap_hom, Over.w_assoc]`. Use the proof step `rfl)`. Set `g : Over.mk (Z'.hom ≫ x) ⟶ G` to `Over.homMk (g'.left ≫ φ) (by`. Rewrite using `[Category.assoc, hφ.1.w, Over.w_assoc]`.

Use the proof step `rfl)`. Establish `hm : ((t ≫ u) * g).left = ((t' ≫ u') * g').left ≫ φ` using `hφ.2 Z' _ _ _ _ (by`. Rewrite using `[Over.comp_left, Over.comp_left, Category.assoc, ← torusCompat_iff.1 hT, ← Category.assoc]`. Use the proof step `rfl) rfl`. Establish `hd : (lift t g).left = O.ι ≫ ψ`.

Use `pullback.hom_ext ?_ ?_` and prove the remaining obligations. Conclude with `(congrArg (·.left) (lift_fst t g)).trans ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (O.ι ≫ ·) hψ₁)).symm)`. Conclude with `(congrArg (·.left) (lift_snd t g)).trans ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (O.ι ≫ ·) hψ₂)).symm)`. Establish `k₁ : ⊤ ≤ ((t' ≫ u') * g').left ⁻¹ᵁ V`. Establish `: (t' ≫ u') * g' = j ≫ ((fst _ _ ≫ u') * snd _ _ : P' ⟶ G')`.

Rewrite using `[MonObj.comp_mul, Category.assoc]`. Rewrite using `[this]`. Conclude with `fun z _ => z.2.1`. Establish `k₂ : ⊤ ≤ g'.left ⁻¹ᵁ V` using `fun z _ => z.2.2`. Establish `l₁ : ⊤ ≤ (((t' ≫ u') * g').left ≫ φ) ⁻¹ᵁ U` using `fun z hz => hVU (k₁ hz)`.

Establish `l₂ : ⊤ ≤ (g'.left ≫ φ) ⁻¹ᵁ U` using `fun z hz => hVU (k₂ hz)`. Use `hW C G X u hI U f χ _ t g (by rw [hd]; infer_instance) (by rw [hm]; exact l₁) l₂ ?_` and prove the remaining obligations. Establish `b₁` using `H _ _ k₁ l₁ (fun z hz => hVU' (k₁ hz))`. Establish `b₂` using `H _ _ k₂ l₂ (fun z hz => hVU' (k₂ hz))`. Establish `b₃ : t.left.appTop.hom (charUnit C X χ).val = t'.left.appTop.hom (charUnit (Sp K) X χ).val`.

Rewrite using `[← bcMap_charUnit x χ]`. Both sides reduce to the same expression. Establish `b₄ : ∀ (r r' : Z'.left ⟶ G.left) (e : r = r') h h', (r.appLE U ⊤ h).hom f = (r'.appLE U ⊤ h').hom f`. Introduce `r r' e h h'`. Substitute `e` using the available equality.

Both sides reduce to the same expression. Conclude with `(b₄ _ _ hm _ l₁).trans (b₁.trans ((hwt Z' t' g' _ _).trans (congrArg₂ (· * ·) b₃.symm b₂.symm)))`.
-/
theorem UpperTheory.split_torus_pullback_generic_fibre :
    WtGeneric → ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ (K : Type) [Field K] (x : Sp K ⟶ C), IsGen x →
        ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus C X ⟶ G), IsMonHom u →
        ∀ (G' : Over (Sp K)) [GrpObj G'] (φ : G'.left ⟶ G.left) (u' : splitTorus (Sp K) X ⟶ G'), IsGrpPullback G' G x φ →
        TorusCompat x φ u' u → ∀ (χ : X) (U' : G'.left.Opens) (f' : Γ(G'.left, U')), (U' : Set G'.left).Nonempty → IsUnit f' →
        Wt u' U' f' χ → ∃ (U : G.left.Opens) (f : Γ(G.left, U)), (U : Set G.left).Nonempty ∧ IsUnit f ∧ Wt u U f χ := by
  intro hW k _ _ C _ hC K _ x hx G _ hG X _ _ _ u hu G' _ φ u' hφ hT χ U' f' ⟨y, hy⟩ hf' hwt
  have := LieSemineg.isIntegral_curve hC.1 hC.2.2
  have := hx.1
  have := hx.2
  have := hG.smooth
  have := hG.geomConnected
  have hu' : IsMonHom u' := hT.isMonHom hφ
  obtain ⟨-, -, -, -, h1, -, -, h2, -⟩ := (splitTorus_properties C).1 X
  have : Smooth (splitTorus C X).hom := SmoothOfRelativeDimension.smooth (Module.finrank ℤ X) _
  have : Smooth (splitTorus C X ⊗ G).hom :=
    inferInstanceAs (Smooth (pullback.fst (splitTorus C X).hom G.hom ≫ (splitTorus C X).hom))
  have : GeometricallyConnected (splitTorus C X ⊗ G).hom :=
    GeometricallyConnected.comp (pullback.fst (splitTorus C X).hom G.hom) (splitTorus C X).hom
  have hI : IsIntegral (splitTorus C X ⊗ G).left :=
    isIntegral_of_isPullback_of_smooth (IsPullback.id_horiz (splitTorus C X ⊗ G).hom)
  have : IsPreimmersion φ := MorphismProperty.of_isPullback (P := @IsPreimmersion) hφ.1.flip hx.2
  obtain ⟨U, f, V, hV, hf, hVU', hVU, H⟩ := spread_unit φ U' f' hf' y hy
  refine ⟨U, f, ⟨φ y, hVU hV⟩, hf, ?_⟩
  let τ := SplitTorus.bcMap x X
  let P' := splitTorus (Sp K) X ⊗ G'
  let ψ : P'.left ⟶ (splitTorus C X ⊗ G).left :=
    pullback.lift ((fst _ _ : P' ⟶ _).left ≫ τ) ((snd _ _ : P' ⟶ _).left ≫ φ) (by
      rw [Category.assoc, Category.assoc, SplitTorus.bcMap_hom, hφ.1.w, Over.w_assoc, Over.w_assoc])
  have hψ₁ : ψ ≫ (fst _ _ : splitTorus C X ⊗ G ⟶ _).left = (fst _ _ : P' ⟶ _).left ≫ τ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ (snd _ _ : splitTorus C X ⊗ G ⟶ _).left = (snd _ _ : P' ⟶ _).left ≫ φ := pullback.lift_snd _ _ _
  have sq : IsPullback ψ P'.hom (splitTorus C X ⊗ G).hom x := by
    have s₁ : IsPullback (fst _ _ : splitTorus C X ⊗ G ⟶ _).left (snd _ _ : splitTorus C X ⊗ G ⟶ _).left
      (splitTorus C X).hom G.hom := IsPullback.of_hasPullback _ _
    have s₂ : IsPullback (fst _ _ : P' ⟶ _).left (snd _ _ : P' ⟶ _).left
      (splitTorus (Sp K) X).hom G'.hom := IsPullback.of_hasPullback _ _
    have s₃ := s₂.paste_horiz (SplitTorus.isPullback_bcMap x X)
    rw [← hψ₁, ← hφ.1.w] at s₃
    have s₄ := (s₃.of_right hψ₂ s₁).paste_vert hφ.1
    rwa [Over.w, Over.w] at s₄
  have : IsIntegral P'.left := isIntegral_of_isPullback_of_smooth sq
  have : IsDominant ψ := isDominant_of_isPullback sq (splitTorus C X ⊗ G).hom.isOpenMap
  let O : P'.left.Opens := ((fst _ _ ≫ u') * snd _ _ : P' ⟶ G').left ⁻¹ᵁ V ⊓ (snd _ _ : P' ⟶ G').left ⁻¹ᵁ V
  have hO : (O : Set P'.left).Nonempty := by
    let s : G' ⟶ P' := lift 1 (𝟙 G')
    have e₁ : s ≫ ((fst _ _ ≫ u') * snd _ _ : P' ⟶ G') = 𝟙 G' := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, MonObj.one_comp, _root_.one_mul]
    have e₂ : s ≫ (snd _ _ : P' ⟶ G') = 𝟙 G' := lift_snd _ _
    refine ⟨s.left y, ?_, ?_⟩
    · show (s ≫ ((fst _ _ ≫ u') * snd _ _ : P' ⟶ G')).left y ∈ V
      rw [e₁]; exact hV
    · show (s ≫ (snd _ _ : P' ⟶ G')).left y ∈ V
      rw [e₂]; exact hV
  have : IsDominant O.ι := ⟨by
    have := O.isOpen.dense hO
    rwa [DenseRange, Scheme.Opens.range_ι]⟩
  let Z' : Over (Sp K) := Over.mk (O.ι ≫ P'.hom)
  let j : Z' ⟶ P' := Over.homMk O.ι rfl
  let t' : Z' ⟶ splitTorus (Sp K) X := j ≫ fst _ _
  let g' : Z' ⟶ G' := j ≫ snd _ _
  let t : Over.mk (Z'.hom ≫ x) ⟶ splitTorus C X := Over.homMk (t'.left ≫ τ) (by
    rw [Category.assoc, SplitTorus.bcMap_hom, Over.w_assoc]; rfl)
  let g : Over.mk (Z'.hom ≫ x) ⟶ G := Over.homMk (g'.left ≫ φ) (by
    rw [Category.assoc, hφ.1.w, Over.w_assoc]; rfl)
  have hm : ((t ≫ u) * g).left = ((t' ≫ u') * g').left ≫ φ :=
    hφ.2 Z' _ _ _ _ (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, ← torusCompat_iff.1 hT, ← Category.assoc]; rfl) rfl
  have hd : (lift t g).left = O.ι ≫ ψ := by
    refine pullback.hom_ext ?_ ?_
    · exact (congrArg (·.left) (lift_fst t g)).trans
        ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (O.ι ≫ ·) hψ₁)).symm)
    · exact (congrArg (·.left) (lift_snd t g)).trans
        ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (O.ι ≫ ·) hψ₂)).symm)
  have k₁ : ⊤ ≤ ((t' ≫ u') * g').left ⁻¹ᵁ V := by
    have : (t' ≫ u') * g' = j ≫ ((fst _ _ ≫ u') * snd _ _ : P' ⟶ G') := by
      rw [MonObj.comp_mul, Category.assoc]
    rw [this]
    exact fun z _ => z.2.1
  have k₂ : ⊤ ≤ g'.left ⁻¹ᵁ V := fun z _ => z.2.2
  have l₁ : ⊤ ≤ (((t' ≫ u') * g').left ≫ φ) ⁻¹ᵁ U := fun z hz => hVU (k₁ hz)
  have l₂ : ⊤ ≤ (g'.left ≫ φ) ⁻¹ᵁ U := fun z hz => hVU (k₂ hz)
  refine hW C G X u hI U f χ _ t g (by rw [hd]; infer_instance) (by rw [hm]; exact l₁) l₂ ?_
  have b₁ := H _ _ k₁ l₁ (fun z hz => hVU' (k₁ hz))
  have b₂ := H _ _ k₂ l₂ (fun z hz => hVU' (k₂ hz))
  have b₃ : t.left.appTop.hom (charUnit C X χ).val = t'.left.appTop.hom (charUnit (Sp K) X χ).val := by
    rw [← bcMap_charUnit x χ]
    rfl
  have b₄ : ∀ (r r' : Z'.left ⟶ G.left) (e : r = r') h h', (r.appLE U ⊤ h).hom f = (r'.appLE U ⊤ h').hom f := by
    intro r r' e h h'
    subst e
    rfl
  exact (b₄ _ _ hm _ l₁).trans (b₁.trans ((hwt Z' t' g' _ _).trans (congrArg₂ (· * ·) b₃.symm b₂.symm)))
