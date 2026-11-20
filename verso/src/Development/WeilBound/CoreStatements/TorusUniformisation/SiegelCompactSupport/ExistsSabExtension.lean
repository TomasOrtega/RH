import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.SiegelCompactSupport.SiegProperSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSabExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedCubicalSymmetricExtensionNormalB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapIdOfCommonGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStructureAndSymmetricOfCubeGenStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRingStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsPullCubicalId

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.TripleExt

namespace PositivityTheory.Member.SiegelModularCharts.K6

/- English proof (translation)
Take `⟨N, hN, hc⟩` from `cls_surj (α - β)`. Use `sub_eq_zero.1 (hc ▸ (cls_eq_zero_iff hN).2 ?_)` and prove the remaining obligations. Use `GlobalTheory.T.exists_lineBundleGenerator_extending_densePart X U j hX inferInstance inferInstance inferInstance inferInstance P e N he hp hg hN ((cls_eq_zero_iff (pull_isLB hN _)).1 ?_) ((cls_eq_zero_iff (pull_isLB hN _)).1 ?_)` and prove the remaining obligations. Rewrite using `[cls_pull hN, hc, map_sub, h₂, sub_self]`. Rewrite using `[cls_pull hN, hc, ← hj.isoPullback_inv_fst, pull_comp, map_sub, h₁, sub_self, map_zero]`.
-/
theorem pic_ext {X U : Scheme.{0}} [IsLocallyNoetherian X] (hX : Geo.Tor.IsNormalScheme X) (j : U ⟶ X)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (P : Over X) (e : X ⟶ P.left) {HU : Scheme.{0}}
    (jH : HU ⟶ P.left) (pU : HU ⟶ U) (hp : Smooth P.hom) (hg : GeometricallyIntegral P.hom) (he : e ≫ P.hom = 𝟙 _)
    (hj : IsPullback jH pU P.hom j) (α β : Pic P.left) (h₁ : pull jH α = pull jH β) (h₂ : pull e α = pull e β) :
    α = β := by
  obtain ⟨N, hN, hc⟩ := cls_surj (α - β)
  refine sub_eq_zero.1 (hc ▸ (cls_eq_zero_iff hN).2 ?_)
  refine GlobalTheory.T.exists_lineBundleGenerator_extending_densePart X U j hX inferInstance inferInstance inferInstance inferInstance P e N he hp hg hN
    ((cls_eq_zero_iff (pull_isLB hN _)).1 ?_) ((cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
  · rw [cls_pull hN, hc, map_sub, h₂, sub_self]
  · rw [cls_pull hN, hc, ← hj.isoPullback_inv_fst, pull_comp, map_sub, h₁, sub_self, map_zero]

/- English proof (translation)
Establish `: ∀ x : X, _root_.IsReduced (X.presheaf.stalk x)` using `fun x => by`. Use `(hX x).1` as an intermediate fact. Use `infer_instance`. Conclude with `isReduced_of_isReduced_stalk X`.
-/
theorem isReduced_of_normal {X : Scheme.{0}} (hX : Geo.Tor.IsNormalScheme X) : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (hX x).1
    infer_instance
  exact isReduced_of_isReduced_stalk X

/- English proof (translation)
Establish `: ∀ x : U, _root_.IsReduced (U.presheaf.stalk x)` using `fun x => by`. Use `(hX (j x)).1` as an intermediate fact. Use `h x` as an intermediate fact. Conclude with `isReduced_of_injective (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv.symm (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv.symm.injective`. Conclude with `isReduced_of_isReduced_stalk U`.
-/
theorem isReduced_source {X U : Scheme.{0}} (hX : Geo.Tor.IsNormalScheme X) (j : U ⟶ X)
    (h : ∀ u : U, IsIso (j.stalkMap u)) : IsReduced U := by
  have : ∀ x : U, _root_.IsReduced (U.presheaf.stalk x) := fun x => by
    have := (hX (j x)).1
    have := h x
    exact isReduced_of_injective (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv.symm
      (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv.symm.injective
  exact isReduced_of_isReduced_stalk U

/- English proof (translation)
Use `semi.smooth` as an intermediate fact. Use `semi.geomConnected` as an intermediate fact. Take `⟨hgen, hst, -, -⟩` from `densePart_basic X U j inferInstance inferInstance inferInstance inferInstance`. Take `⟨PP, hPP⟩` from `NormalCubeExt.exists_rigidified h t₀.PP hM hMa`. Establish `hc₀ : cls t₀.PP.L t₀.PP.isLB = pull a (cls PP.L PP.isLB)` using `(cls_eq_iff t₀.PP.isLB (pull_isLB PP.isLB _)).2 hPP`.

Establish `hrig : pull (eSec G) (cls PP.L PP.isLB) = 0` using `(cls_eq_zero_iff (pull_isLB PP.isLB _)).2 ⟨PP.rig, PP.rigGen⟩`. Establish `pa : ∀ {T : Over U} (x : T ⟶ t₀.G) b, pushPt h.1.w (x ≫ t₀.act.act b) = pushPt h.1.w x ≫ act.act b` using `fun x b => Over.OverMorphism.ext (by show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _`. Rewrite using `[Category.assoc, hact, Category.assoc])`. Establish `ha1 : ∀ b, η[G] ≫ act.act b = η[G]` using `fun b => by have := act.hom b; exact IsMonHom.one_hom _`. Establish `s₂` using `CubeExtension.smooth_tensor G G`.

Establish `s₃` using `CubeExtension.smooth_tensor G (G ⊗ G)`. Establish `c₂` using `CubeExtension.geometricallyConnected_tensor G G`. Establish `c₃` using `CubeExtension.geometricallyConnected_tensor G (G ⊗ G)`. Establish `hy : ∀ (T : Over X) (y : T ⟶ G), ∃ y' : Over.mk (pullback.snd T.hom j) ⟶ t₀.G, pushPt h.1.w y' = (Over.homMk (pullback.fst T.hom j) pullback.condition : Over.mk ((Over.mk (pullback.snd T.hom j)).hom ≫ j) ⟶ T) ≫ y` using `fun T y => ⟨Over.homMk (h.1.lift (pullback.fst T.hom j ≫ y.left) (pullback.snd T.hom j) (by rw [Category.assoc, Over.w]; exact pullback.condition)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩`. Take `⟨hcub, hsym⟩` from `GlobalTheory.T.cubicalStructure_and_symmetric_of_cube_gen X G PP semi ⟨isReduced_of_normal hX, hgen.trans (range_subset_abLocus_of_isProper semi h.1)⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨cub⟩ : Nonempty (CubicalStr G PP) := by`. Use `hcub ((cls_eq_zero_iff (isLB_cube (x3 G) PP.isLB)).1 ?_)` and prove the remaining obligations. Rewrite using `[cls_cube _ PP.isLB]`. Set `T' : Over U` to `Over.mk (pullback.snd (G3 G).hom j)`. Set `u : Over.mk (T'.hom ≫ j) ⟶ G3 G` to `Over.homMk (pullback.fst (G3 G).hom j) pullback.condition`.

Use `choose y hy' using fun i => hy (G3 G) (x3 G i)`. Set `e : 𝟙_ (Over X) ⟶ G3 G` to `lift η[G] (lift η[G] η[G])`. Use `pic_ext hX j (G3 G) e.left u.left T'.hom s₃ (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w e) (IsPullback.of_hasPullback _ _) _ _ ?_ ?_` and prove the remaining obligations. Establish `h₀` using `(cls_eq_zero_iff (isLB_cube (x3 t₀.G) t₀.PP.isLB)).2 ⟨t₀.cub.t, t₀.cub.isGen⟩`. Rewrite `h₀` using `[cls_cube _ t₀.PP.isLB, hc₀]`.

Establish `h₁` using `congrArg (pull (lift (y 0) (lift (y 1) (y 2))).left) h₀`. Rewrite `h₁` using `[pull_cubeCls_pre, map_zero]`. Use `(pull_cubeCls_push h _ _ u (fun i => ?_) _).trans (h₁.trans (map_zero _).symm)` and prove the remaining obligations. Use `Eq.trans ?_ (hy' i)` and prove the remaining obligations. Use `congr 1`.

Apply the tactic sequence `fin_cases i <;> simp [x3]`. Use `(pull_cubeCls_pre e _ _).trans (Eq.trans ?_ (map_zero _).symm)` and prove the remaining obligations. Use `Eq.trans ?_ (cubeCls_one (n := 3) _ hrig)` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `fin_cases i <;> simp [e, x3]`. Establish `hs : PP.IsSymmetric`. Use `hsym ((cls_eq_iff PP.isLB (pull_isLB PP.isLB _)).1 ?_)` and prove the remaining obligations. Establish `hι : (ι[t₀.G]).left ≫ a = a ≫ (ι[G]).left`. Establish `e` using `congrArg (fun q => q.left) (map_inv (pushHom h t₀.G) (𝟙 t₀.G))`.

Simplify using `only [Hom.inv_def, Category.id_comp] at e`. Use `e.trans ?_` and prove the remaining obligations. Use `show (𝟙 _ ≫ a) ≫ _ = _`. Rewrite using `[Category.id_comp]`. Establish `e₂ : eSec G ≫ (ι[G]).left = eSec G`.

Rewrite using `[eSec, ← Over.comp_left, GrpObj.one_inv]`. Rewrite using `[cls_pull PP.isLB]`. Use `pic_ext hX j G (eSec G) a t₀.G.hom inferInstance (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w η[G]) h.1 _ _ ?_ ?_` and prove the remaining obligations. Take `⟨-, w, hw, -⟩` from `t₀.sym`. Establish `h₀` using `(cls_eq_iff t₀.PP.isLB (pull_isLB t₀.PP.isLB _)).2 ⟨w, hw⟩`.

Rewrite `h₀` using `[cls_pull t₀.PP.isLB, hc₀, ← pull_comp, hι, pull_comp]`. Conclude with `h₀`. Rewrite using `[← pull_comp, e₂]`. Establish `hadj : ∀ b, LBIso (cubeLB G ![fst G G ≫ act.act b, snd G G] PP.L) (cubeLB G ![fst G G, snd G G ≫ act.act (H.bar b)] PP.L)` using `fun b => by`. Use `(cls_eq_iff (isLB_cube _ PP.isLB) (isLB_cube _ PP.isLB)).1 ?_` and prove the remaining obligations.

Rewrite using `[cls_cube _ PP.isLB, cls_cube _ PP.isLB]`. Set `T' : Over U` to `Over.mk (pullback.snd (G ⊗ G).hom j)`. Set `u : Over.mk (T'.hom ≫ j) ⟶ G ⊗ G` to `Over.homMk (pullback.fst (G ⊗ G).hom j) pullback.condition`. Take `⟨y₁, hy₁⟩ : ∃ y' : T' ⟶ t₀.G, pushPt h.1.w y' = u ≫ fst G G` from `hy _ (fst G G)`. Take `⟨y₂, hy₂⟩ : ∃ y' : T' ⟶ t₀.G, pushPt h.1.w y' = u ≫ snd G G` from `hy _ (snd G G)`.

Set `e : 𝟙_ (Over X) ⟶ G ⊗ G` to `lift η[G] η[G]`. Use `pic_ext hX j (G ⊗ G) e.left u.left T'.hom s₂ (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w e) (IsPullback.of_hasPullback _ _) _ _ ?_ ?_` and prove the remaining obligations. Establish `h₀` using `(cls_eq_iff (isLB_cube _ t₀.PP.isLB) (isLB_cube _ t₀.PP.isLB)).2 (t₀.adj b)`. Rewrite `h₀` using `[cls_cube _ t₀.PP.isLB, cls_cube _ t₀.PP.isLB, hc₀]`. Establish `h₁` using `congrArg (pull (lift y₁ y₂).left) h₀`.

Rewrite `h₁` using `[pull_cubeCls_pre, pull_cubeCls_pre]`. Use `(pull_cubeCls_push h _ _ u (fun i => ?_) _).trans (h₁.trans (pull_cubeCls_push h _ _ u (fun i => ?_) _).symm)` and prove the remaining obligations. Use `fin_cases i`. Simplify using `[pa, hy₁]`. Simplify using `[hy₂]`.

Use `fin_cases i`. Simplify using `[hy₁]`. Simplify using `[pa, hy₂]`. Use `(pull_cubeCls_pre e _ _).trans (Eq.trans ?_ (pull_cubeCls_pre e _ _).symm)` and prove the remaining obligations. Use `congr 1`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [e, ha1]`. Establish `hprim : LBIso PP.L (cubeLB G ![𝟙 G, act.act H.w0] PP.L)`. Use `(cls_eq_iff PP.isLB (isLB_cube _ PP.isLB)).1 ?_` and prove the remaining obligations. Rewrite using `[cls_cube _ PP.isLB]`.

Use `pic_ext hX j G (eSec G) a t₀.G.hom inferInstance (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w η[G]) h.1 _ _ ?_ ?_` and prove the remaining obligations. Establish `h₀` using `(cls_eq_iff t₀.PP.isLB (isLB_cube _ t₀.PP.isLB)).2 t₀.prim`. Rewrite `h₀` using `[cls_cube _ t₀.PP.isLB, hc₀]`. Establish `h₁` using `pull_cubeCls_push h ![𝟙 t₀.G, t₀.act.act H.w0] ![𝟙 G, act.act H.w0] (pushPt h.1.w (𝟙 t₀.G)) (fun i => by fin_cases i`. Simplify using the standard rewrite rules.

Conclude with `(congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)) (cls PP.L PP.isLB)`. Establish `e : (pushPt h.1.w (𝟙 t₀.G)).left = a` using `Category.id_comp _`. Rewrite `h₁` using `[e]`. Conclude with `h₀.trans h₁.symm`. Use `hrig.trans (Eq.trans ?_ (pull_cubeCls_pre η[G] _ _).symm)` and prove the remaining obligations.

Use `(cubeCls_one (n := 2) _ hrig).symm.trans ?_` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [ha1]`. Take `⟨m, hm⟩` from `exists_sabMap_of_lbIso E H X U (SAB.mk G semi act PP cub hs hadj hprim) t₀ j a ⟨isReduced_source hX j hst, fun x _ => range_subset_abLocus_of_isProper t₀.semi (ObjRebase.isGrpPullback_id t₀.G).1 ⟨x, rfl⟩⟩ h hact hPP`.

Conclude with `⟨PP, cub, hs, hadj, hprim, m, hm⟩`.
-/
theorem exists_sab_extension {X U : Scheme.{0}} [IsLocallyNoetherian X] (hX : Geo.Tor.IsNormalScheme X) (j : U ⟶ X)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (G : Over X) [GrpObj G] [IsCommMonObj G] (semi : IsSemiAbelian G) (act : OAct (𝓞 E) G)
    (t₀ : SAB H U) (a : t₀.G.left ⟶ G.left) [IsProper t₀.G.hom] (h : IsGrpPullback t₀.G G j a)
    (hact : ∀ x, (t₀.act.act x).left ≫ a = a ≫ (act.act x).left) (M : LB G.left) (hM : M.IsLB)
    (hMa : LBIso (M.pull a) t₀.PP.L) :
    ∃ (PP : RigLB G) (cub : CubicalStr G PP) (h₁ : _) (h₂ : _) (h₃ : _)
      (m : SABMap t₀ (SAB.mk G semi act PP cub h₁ h₂ h₃) j), m.φ = a := by
  have := semi.smooth
  have := semi.geomConnected
  obtain ⟨hgen, hst, -, -⟩ := densePart_basic X U j inferInstance inferInstance inferInstance inferInstance
  obtain ⟨PP, hPP⟩ := NormalCubeExt.exists_rigidified h t₀.PP hM hMa
  have hc₀ : cls t₀.PP.L t₀.PP.isLB = pull a (cls PP.L PP.isLB) :=
    (cls_eq_iff t₀.PP.isLB (pull_isLB PP.isLB _)).2 hPP
  have hrig : pull (eSec G) (cls PP.L PP.isLB) = 0 :=
    (cls_eq_zero_iff (pull_isLB PP.isLB _)).2 ⟨PP.rig, PP.rigGen⟩
  have pa : ∀ {T : Over U} (x : T ⟶ t₀.G) b,
      pushPt h.1.w (x ≫ t₀.act.act b) = pushPt h.1.w x ≫ act.act b := fun x b =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have ha1 : ∀ b, η[G] ≫ act.act b = η[G] := fun b => by have := act.hom b; exact IsMonHom.one_hom _
  have s₂ := CubeExtension.smooth_tensor G G
  have s₃ := CubeExtension.smooth_tensor G (G ⊗ G)
  have c₂ := CubeExtension.geometricallyConnected_tensor G G
  have c₃ := CubeExtension.geometricallyConnected_tensor G (G ⊗ G)
  have hy : ∀ (T : Over X) (y : T ⟶ G), ∃ y' : Over.mk (pullback.snd T.hom j) ⟶ t₀.G, pushPt h.1.w y' =
      (Over.homMk (pullback.fst T.hom j) pullback.condition :
        Over.mk ((Over.mk (pullback.snd T.hom j)).hom ≫ j) ⟶ T) ≫ y := fun T y =>
    ⟨Over.homMk (h.1.lift (pullback.fst T.hom j ≫ y.left) (pullback.snd T.hom j)
      (by rw [Category.assoc, Over.w]; exact pullback.condition)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  obtain ⟨hcub, hsym⟩ := GlobalTheory.T.cubicalStructure_and_symmetric_of_cube_gen X G PP semi
    ⟨isReduced_of_normal hX, hgen.trans (range_subset_abLocus_of_isProper semi h.1)⟩
  obtain ⟨cub⟩ : Nonempty (CubicalStr G PP) := by
    refine hcub ((cls_eq_zero_iff (isLB_cube (x3 G) PP.isLB)).1 ?_)
    rw [cls_cube _ PP.isLB]
    let T' : Over U := Over.mk (pullback.snd (G3 G).hom j)
    let u : Over.mk (T'.hom ≫ j) ⟶ G3 G := Over.homMk (pullback.fst (G3 G).hom j) pullback.condition
    choose y hy' using fun i => hy (G3 G) (x3 G i)
    let e : 𝟙_ (Over X) ⟶ G3 G := lift η[G] (lift η[G] η[G])
    refine pic_ext hX j (G3 G) e.left u.left T'.hom s₃
      (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w e)
      (IsPullback.of_hasPullback _ _) _ _ ?_ ?_
    · have h₀ := (cls_eq_zero_iff (isLB_cube (x3 t₀.G) t₀.PP.isLB)).2 ⟨t₀.cub.t, t₀.cub.isGen⟩
      rw [cls_cube _ t₀.PP.isLB, hc₀] at h₀
      have h₁ := congrArg (pull (lift (y 0) (lift (y 1) (y 2))).left) h₀
      rw [pull_cubeCls_pre, map_zero] at h₁
      refine (pull_cubeCls_push h _ _ u (fun i => ?_) _).trans (h₁.trans (map_zero _).symm)
      refine Eq.trans ?_ (hy' i)
      congr 1
      fin_cases i <;> simp [x3]
    · refine (pull_cubeCls_pre e _ _).trans (Eq.trans ?_ (map_zero _).symm)
      refine Eq.trans ?_ (cubeCls_one (n := 3) _ hrig)
      congr 1
      funext i
      fin_cases i <;> simp [e, x3]
  have hs : PP.IsSymmetric := by
    refine hsym ((cls_eq_iff PP.isLB (pull_isLB PP.isLB _)).1 ?_)
    have hι : (ι[t₀.G]).left ≫ a = a ≫ (ι[G]).left := by
      have e := congrArg (fun q => q.left) (map_inv (pushHom h t₀.G) (𝟙 t₀.G))
      simp only [Hom.inv_def, Category.id_comp] at e
      refine e.trans ?_
      show (𝟙 _ ≫ a) ≫ _ = _
      rw [Category.id_comp]
    have e₂ : eSec G ≫ (ι[G]).left = eSec G := by
      rw [eSec, ← Over.comp_left, GrpObj.one_inv]
    rw [cls_pull PP.isLB]
    refine pic_ext hX j G (eSec G) a t₀.G.hom inferInstance
      (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w η[G]) h.1 _ _ ?_ ?_
    · obtain ⟨-, w, hw, -⟩ := t₀.sym
      have h₀ := (cls_eq_iff t₀.PP.isLB (pull_isLB t₀.PP.isLB _)).2 ⟨w, hw⟩
      rw [cls_pull t₀.PP.isLB, hc₀, ← pull_comp, hι, pull_comp] at h₀
      exact h₀
    · rw [← pull_comp, e₂]
  have hadj : ∀ b, LBIso (cubeLB G ![fst G G ≫ act.act b, snd G G] PP.L)
      (cubeLB G ![fst G G, snd G G ≫ act.act (H.bar b)] PP.L) := fun b => by
    refine (cls_eq_iff (isLB_cube _ PP.isLB) (isLB_cube _ PP.isLB)).1 ?_
    rw [cls_cube _ PP.isLB, cls_cube _ PP.isLB]
    let T' : Over U := Over.mk (pullback.snd (G ⊗ G).hom j)
    let u : Over.mk (T'.hom ≫ j) ⟶ G ⊗ G := Over.homMk (pullback.fst (G ⊗ G).hom j) pullback.condition
    obtain ⟨y₁, hy₁⟩ : ∃ y' : T' ⟶ t₀.G, pushPt h.1.w y' = u ≫ fst G G := hy _ (fst G G)
    obtain ⟨y₂, hy₂⟩ : ∃ y' : T' ⟶ t₀.G, pushPt h.1.w y' = u ≫ snd G G := hy _ (snd G G)
    let e : 𝟙_ (Over X) ⟶ G ⊗ G := lift η[G] η[G]
    refine pic_ext hX j (G ⊗ G) e.left u.left T'.hom s₂
      (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w e)
      (IsPullback.of_hasPullback _ _) _ _ ?_ ?_
    · have h₀ := (cls_eq_iff (isLB_cube _ t₀.PP.isLB) (isLB_cube _ t₀.PP.isLB)).2 (t₀.adj b)
      rw [cls_cube _ t₀.PP.isLB, cls_cube _ t₀.PP.isLB, hc₀] at h₀
      have h₁ := congrArg (pull (lift y₁ y₂).left) h₀
      rw [pull_cubeCls_pre, pull_cubeCls_pre] at h₁
      refine (pull_cubeCls_push h _ _ u (fun i => ?_) _).trans
        (h₁.trans (pull_cubeCls_push h _ _ u (fun i => ?_) _).symm)
      · fin_cases i
        · simp [pa, hy₁]
        · simp [hy₂]
      · fin_cases i
        · simp [hy₁]
        · simp [pa, hy₂]
    · refine (pull_cubeCls_pre e _ _).trans (Eq.trans ?_ (pull_cubeCls_pre e _ _).symm)
      congr 1
      funext i
      fin_cases i <;> simp [e, ha1]
  have hprim : LBIso PP.L (cubeLB G ![𝟙 G, act.act H.w0] PP.L) := by
    refine (cls_eq_iff PP.isLB (isLB_cube _ PP.isLB)).1 ?_
    rw [cls_cube _ PP.isLB]
    refine pic_ext hX j G (eSec G) a t₀.G.hom inferInstance
      (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w η[G]) h.1 _ _ ?_ ?_
    · have h₀ := (cls_eq_iff t₀.PP.isLB (isLB_cube _ t₀.PP.isLB)).2 t₀.prim
      rw [cls_cube _ t₀.PP.isLB, hc₀] at h₀
      have h₁ := pull_cubeCls_push h ![𝟙 t₀.G, t₀.act.act H.w0] ![𝟙 G, act.act H.w0] (pushPt h.1.w (𝟙 t₀.G))
        (fun i => by
          fin_cases i
          · simp
          · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)) (cls PP.L PP.isLB)
      have e : (pushPt h.1.w (𝟙 t₀.G)).left = a := Category.id_comp _
      rw [e] at h₁
      exact h₀.trans h₁.symm
    · refine hrig.trans (Eq.trans ?_ (pull_cubeCls_pre η[G] _ _).symm)
      refine (cubeCls_one (n := 2) _ hrig).symm.trans ?_
      congr 1
      funext i
      fin_cases i <;> simp [ha1]
  obtain ⟨m, hm⟩ := exists_sabMap_of_lbIso E H X U (SAB.mk G semi act PP cub hs hadj hprim) t₀ j a
    ⟨isReduced_source hX j hst, fun x _ => range_subset_abLocus_of_isProper t₀.semi
      (ObjRebase.isGrpPullback_id t₀.G).1 ⟨x, rfl⟩⟩ h hact hPP
  exact ⟨PP, cub, hs, hadj, hprim, m, hm⟩

end PositivityTheory.Member.SiegelModularCharts.K6

namespace PositivityTheory.Member.SiegelModularCharts

/- English proof (translation)
Introduce `E _ _ _ H X U j z hX hz₁ hz₂ hz₃ hj₁ hj₂ hj₃ hj₄ hU G _ semi t₀ a a₂ P hp h hsq hP hL`. Use `semi.comm` as an intermediate fact. Establish `: IsLocallyNoetherian X` using `LocallyOfFiniteType.isLocallyNoetherian z`. Take `⟨-, -, hdom, -⟩` from `densePart_basic X U j hj₁ hj₂ hj₃ hj₄`. Use `hdom (K6.isReduced_of_normal hX)` as an intermediate fact.

Take `⟨_, _⟩` from `ExtUnique.flat_and_isSeparated_of_isSemiAbelian G semi`. Take `⟨act, hact, -⟩` from `ExtUnique.existsUnique_oAct_of_isGrpPullback h t₀.act fun x => by`. Take `⟨e, he, hφ⟩` from `grpPullback_iso h (isGrpPullback_pullback G j)`. Use `t₀.act.hom x` as an intermediate fact. Take `⟨F, ⟨-, hFf⟩, -⟩` from `GlobalTheory.T.existsUnique_hom_extension_semiAbelian_normal_base_alt GlobalTheory.T.homExtension_semiAbelian_discreteValuationRing X U j ⟨hX, z, hz₁, hz₂⟩ hj₁ hj₂ hj₃ hj₄ G G semi semi (e.inv ≫ t₀.act.act x ≫ e.hom) inferInstance`.

Use `⟨F, ?_⟩` and prove the remaining obligations. Rewrite using `[← hφ, Category.assoc, ← ExtUnique.pullback_map_left_fst j F, hFf, ← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, e.hom_inv_id_assoc]`. Set `d : G ⟶ G2 G` to `lift (𝟙 G) (act.act H.w0)`. Set `d₀ : t₀.G ⟶ G2 t₀.G` to `lift (𝟙 t₀.G) (t₀.act.act H.w0)`. Establish `hd : a ≫ d.left = d₀.left ≫ a₂`.

Establish `e₁ : d.left ≫ (fst G G).left = 𝟙 _` using `by rw [← Over.comp_left, lift_fst, Over.id_left]`. Establish `e₂ : d.left ≫ (snd G G).left = (act.act H.w0).left` using `by rw [← Over.comp_left, lift_snd]`. Establish `e₃ : d₀.left ≫ (fst t₀.G t₀.G).left = 𝟙 _` using `by rw [← Over.comp_left, lift_fst, Over.id_left]`. Establish `e₄ : d₀.left ≫ (snd t₀.G t₀.G).left = (t₀.act.act H.w0).left` using `by rw [← Over.comp_left, lift_snd]`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Use `show (a ≫ d.left) ≫ (fst G G).left = (d₀.left ≫ a₂) ≫ (fst G G).left`. Rewrite using `[Category.assoc, Category.assoc, hsq.1, e₁, reassoc_of% e₃, Category.comp_id]`. Use `show (a ≫ d.left) ≫ (snd G G).left = (d₀.left ≫ a₂) ≫ (snd G G).left`. Rewrite using `[Category.assoc, Category.assoc, hsq.2, e₂, reassoc_of% e₄, hact]`. Take `⟨PP, cub, h₁, h₂, h₃, m, hm⟩` from `K6.exists_sab_extension hX j H G semi act t₀ a h hact (P.pull d.left) (pull_isLB hP _) (by`.

Use `(cls_eq_iff (pull_isLB (pull_isLB hP _) _) t₀.PP.isLB).1 ?_` and prove the remaining obligations. Establish `h₀` using `(cls_eq_iff t₀.PP.isLB (isLB_cube _ t₀.PP.isLB)).2 t₀.prim`. Establish `h₁` using `(cls_eq_iff (isLB_cube (x2 t₀.G) t₀.PP.isLB) (pull_isLB hP _)).2 hL`. Rewrite `h₀`, `h₁` using `[cls_cube _ t₀.PP.isLB]`. Rewrite using `[cls_pull (pull_isLB hP _), cls_pull hP, ← pull_comp, hd, pull_comp, ← cls_pull hP a₂ (pull_isLB hP _), ← h₁, pull_cubeCls_pre]`.

Use `Eq.trans ?_ h₀.symm` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [d₀, x2])`. Conclude with `⟨_, 𝟙 _, m, ObjRebase.isGrpPullback_id G, (Category.comp_id _).trans hm⟩`.
-/
theorem tripleExt : TripleExtSt := by
  intro E _ _ _ H X U j z hX hz₁ hz₂ hz₃ hj₁ hj₂ hj₃ hj₄ hU G _ semi t₀ a a₂ P hp h hsq hP hL
  have := semi.comm
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian z
  obtain ⟨-, -, hdom, -⟩ := densePart_basic X U j hj₁ hj₂ hj₃ hj₄
  have := hdom (K6.isReduced_of_normal hX)
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian G semi
  obtain ⟨act, hact, -⟩ := ExtUnique.existsUnique_oAct_of_isGrpPullback h t₀.act fun x => by
    obtain ⟨e, he, hφ⟩ := grpPullback_iso h (isGrpPullback_pullback G j)
    have := t₀.act.hom x
    obtain ⟨F, ⟨-, hFf⟩, -⟩ := GlobalTheory.T.existsUnique_hom_extension_semiAbelian_normal_base_alt GlobalTheory.T.homExtension_semiAbelian_discreteValuationRing X U j ⟨hX, z, hz₁, hz₂⟩ hj₁ hj₂ hj₃ hj₄ G G semi semi
      (e.inv ≫ t₀.act.act x ≫ e.hom) inferInstance
    refine ⟨F, ?_⟩
    rw [← hφ, Category.assoc, ← ExtUnique.pullback_map_left_fst j F, hFf, ← Category.assoc, ← Category.assoc,
      ← Over.comp_left, ← Over.comp_left, e.hom_inv_id_assoc]
  let d : G ⟶ G2 G := lift (𝟙 G) (act.act H.w0)
  let d₀ : t₀.G ⟶ G2 t₀.G := lift (𝟙 t₀.G) (t₀.act.act H.w0)
  have hd : a ≫ d.left = d₀.left ≫ a₂ := by
    have e₁ : d.left ≫ (fst G G).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst, Over.id_left]
    have e₂ : d.left ≫ (snd G G).left = (act.act H.w0).left := by rw [← Over.comp_left, lift_snd]
    have e₃ : d₀.left ≫ (fst t₀.G t₀.G).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst, Over.id_left]
    have e₄ : d₀.left ≫ (snd t₀.G t₀.G).left = (t₀.act.act H.w0).left := by rw [← Over.comp_left, lift_snd]
    apply pullback.hom_ext
    · show (a ≫ d.left) ≫ (fst G G).left = (d₀.left ≫ a₂) ≫ (fst G G).left
      rw [Category.assoc, Category.assoc, hsq.1, e₁, reassoc_of% e₃, Category.comp_id]
    · show (a ≫ d.left) ≫ (snd G G).left = (d₀.left ≫ a₂) ≫ (snd G G).left
      rw [Category.assoc, Category.assoc, hsq.2, e₂, reassoc_of% e₄, hact]
  obtain ⟨PP, cub, h₁, h₂, h₃, m, hm⟩ := K6.exists_sab_extension hX j H G semi act t₀ a h hact (P.pull d.left)
    (pull_isLB hP _) (by
      refine (cls_eq_iff (pull_isLB (pull_isLB hP _) _) t₀.PP.isLB).1 ?_
      have h₀ := (cls_eq_iff t₀.PP.isLB (isLB_cube _ t₀.PP.isLB)).2 t₀.prim
      have h₁ := (cls_eq_iff (isLB_cube (x2 t₀.G) t₀.PP.isLB) (pull_isLB hP _)).2 hL
      rw [cls_cube _ t₀.PP.isLB] at h₀ h₁
      rw [cls_pull (pull_isLB hP _), cls_pull hP, ← pull_comp, hd, pull_comp, ← cls_pull hP a₂ (pull_isLB hP _), ← h₁,
        pull_cubeCls_pre]
      refine Eq.trans ?_ h₀.symm
      congr 1
      funext i
      fin_cases i <;> simp [d₀, x2])
  exact ⟨_, 𝟙 _, m, ObjRebase.isGrpPullback_id G, (Category.comp_id _).trans hm⟩

end PositivityTheory.Member.SiegelModularCharts
