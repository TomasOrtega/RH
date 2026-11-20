import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionPrimitiveBundleTranslateLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointTranslatePrimitiveOfAmpleKTrivialStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.PrimitiveAmpleLocal
open GlobalTheory.CechPic GlobalTheory.StabFlat
open GlobalTheory.PrimitiveOverLocalRing hiding exists_section_translate
open GlobalTheory.PrimitiveOverValuationRing hiding exists_geometric_point exists_section_translate

/- English proof (translation)
Take `⟨t, ht⟩` from `hΘ`. Set `U : Over.mk ((G3 G').hom ≫ f) ⟶ G3 G` to `lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2)))`. Apply the tactic sequence `have hx : ∀ i, pushPt h.1.w (x3 G' i) = U ≫ x3 G i := fun i => by fin_cases i <;> simp [U, x3]`. Conclude with `gen_chartPull (chartPullLinComb L φ (thφ G' (x3 G')) (thφ G (x3 G)) thε U.left fun k => psum_push h _ _ U hx k.down) t ht`.
-/
theorem theta_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left}
    (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) : ∃ t : LB.Gen (Theta G' (L.pull φ)), t.IsGen := by
  obtain ⟨t, ht⟩ := hΘ
  let U : Over.mk ((G3 G').hom ≫ f) ⟶ G3 G :=
    lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2)))
  have hx : ∀ i, pushPt h.1.w (x3 G' i) = U ≫ x3 G i := fun i => by fin_cases i <;> simp [U, x3]
  exact gen_chartPull (chartPullLinComb L φ (thφ G' (x3 G')) (thφ G (x3 G)) thε U.left
    fun k => psum_push h _ _ U hx k.down) t ht

/- English proof (translation)
Take `⟨B', _, _, g, h, hB'⟩ : ∃ (B' : Over (Spec (CommRingCat.of K))) (_ : GrpObj B') (_ : IsCommMonObj B') (g : B'.left ⟶ B.left), IsGrpPullback B' B f g ∧ IsAbelianScheme B'` from `⟨(Over.pullback f).obj B, inferInstance, (TLinPf.isAb_pullback f B hB).comm, _, isGrpPullback_pullback B f, TLinPf.isAb_pullback f B hB⟩`. Establish `hg` using `h.1`. Establish `hm : ∀ (T : Over (Spec (CommRingCat.of K))) (x y : T ⟶ B'), toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y` using `fun T x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm`. Establish `hL'` using `pull_isLB hL g`. Establish `hd' : SmoothOfRelativeDimension d B'.hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hg hd`.

Take `⟨w₀, hw₀⟩ : LBIso (L.pull g) (L.pull g)` from `⟨idIso _, idIso_isGen hL'⟩`. Establish `ha' : RelAmple B' (L.pull g)` using `relAmple_pull hg hL hL' ((isGen_iff w₀).1 hw₀) ⊤ (isAffineOpen_top _) (fun _ => trivial) ha`. Establish `hk' : KTriv B' (L.pull g)` using `kTriv_pull h hL hL' ((isGen_iff w₀).1 hw₀) hk`. Establish `hΘ'` using `theta_pull h hΘ`. Establish `hc : CechPic.pull g (cls L hL) = cls (L.pull g) hL'` using `(cls_pull hL _ _).symm`.

Establish `hO'` using `pull_isLB hO g`. Establish `one : ∀ T : Over (Spec (CommRingCat.of K)), toBase hg.w (1 : T ⟶ B') = 1` using `fun T => by`. Use `hm T 1 1` as an intermediate fact. Rewrite `this` using `[_root_.mul_one]`. Conclude with `left_eq_mul.1 this`.

Establish `lamO : lam (cls O hO) (fst B B) (snd B B) = 0` using `(cls_cube_two hO _ _ (LB.isLB_linComb hO _ _)).symm.trans ((cls_eq_zero_iff _).2 hu)`. Establish `lamO' : lam (cls _ hO') (fst B' B') (snd B' B') = 0`. Establish `e` using `congrArg (CechPic.pull (lift (toBase hg.w (fst B' B')) (toBase hg.w (snd B' B'))).left) lamO`. Rewrite `e` using `[pull_lam, lift_fst, lift_snd, map_zero, lam, ← hm, ← one]`. Rewrite using `[cls_pull hO, lam, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp]`.

Conclude with `e`. Take `⟨x', hx'⟩` from `GlobalTheory.T.exists_point_translate_primitive_of_ample_K_trivial K B' d (L.pull g) (O.pull g) hB' hd' hL' ha' hk' hΘ' hO' ((cls_eq_zero_iff (LB.isLB_linComb hO' _ _)).1 ((cls_cube_two hO' _ _ (LB.isLB_linComb hO' _ _)).trans lamO'))`. Establish `e` using `((cls_eq_iff hO' (LB.isLB_linComb hL' _ _)).2 hx').trans (cls_pair hL' _ _ _)`. Set `T : Over (Sp A)` to `Over.mk f`. Establish `wx : x'.left ≫ B'.hom = 𝟙 _` using `Over.w x'`.

Set `x : T ⟶ B` to `Over.homMk (x'.left ≫ g) (by show (x'.left ≫ g) ≫ B.hom = f`. Rewrite using `[Category.assoc, hg.w, ← Category.assoc, wx]`. Conclude with `Category.id_comp _)`. Establish `w : (snd T B).left ≫ B.hom = (fst T B).left ≫ f` using `(Over.w (snd T B)).trans (Over.w (fst T B)).symm`. Set `T' : Over (Spec (CommRingCat.of K))` to `Over.mk (Y := (T ⊗ B).left) (fst T B).left`.

Set `h : T' ⟶ B'` to `Over.homMk (hg.lift (snd T B).left (fst T B).left w) (hg.lift_snd _ _ _)`. Establish `hh : h.left ≫ g = (snd T B).left` using `hg.lift_fst _ _ _`. Set `u : Over.mk (T'.hom ≫ f) ⟶ T ⊗ B` to `Over.homMk (𝟙 _) ((Category.id_comp _).trans (Over.w (fst T B)).symm)`. Establish `b₁ : u ≫ snd T B = toBase hg.w h` using `Over.OverMorphism.ext ((Category.id_comp _).trans hh.symm)`. Establish `b₂ : u ≫ fst T B ≫ x = toBase hg.w (toUnit T' ≫ x')`.

Use `Over.OverMorphism.ext ((Category.id_comp _).trans ?_)` and prove the remaining obligations. Establish `: (toUnit T').left = (fst T B).left` using `(Category.comp_id _).symm.trans (Over.w (toUnit T'))`. Use `show (fst T B).left ≫ x'.left ≫ g = ((toUnit T').left ≫ x'.left) ≫ g`. Rewrite using `[this]`. Conclude with `(Category.assoc _ _ _).symm`.

Establish `b : h.left ≫ ((toUnit B' ≫ x') * 𝟙 B').left ≫ g = ((fst T B ≫ x) * snd T B).left`. Establish `b₃ : toBase hg.w (h ≫ ((toUnit B' ≫ x') * 𝟙 B')) = u ≫ ((fst T B ≫ x) * snd T B)`. Rewrite using `[MonObj.comp_mul, MonObj.comp_mul, b₁, b₂, ← hm, Category.comp_id, ← Category.assoc, comp_toUnit]`. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg CommaMorphism.left b₃).trans (Category.id_comp _))`. Establish `e'` using `congrArg (CechPic.pull h.left) e`.

Rewrite `e'` using `[cls_pull hO, ← hc, pull_id, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, Category.assoc, b, hh]`. Establish `h₁ : (translDiff B L x).IsLB` using `LB.isLB_linComb hL _ _`. Establish `h₂` using `pull_isLB hO (snd T B).left`. Use `⟨x, (cls_eq_zero_iff (LB.isLB_div h₁ h₂)).1 ?_⟩` and prove the remaining obligations. Rewrite using `[cls_div h₁ h₂, sub_eq_zero]`.

Conclude with `(cls_pair hL _ _ h₁).trans e'.symm`.
-/
theorem exists_geometric_point {A : Type} [CommRing A] {B : Over (Sp A)} [GrpObj B] [IsCommMonObj B] {d : ℕ}
    {L O : LB B.left} (hB : IsAbelianScheme B) (hd : SmoothOfRelativeDimension d B.hom) (hL : L.IsLB)
    (ha : RelAmple B L) (hk : KTriv B L) (hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen) (hO : O.IsLB)
    (hu : ∃ u : LB.Gen (abelian₂ B O), u.IsGen) (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ Sp A) :
    ∃ x : Over.mk f ⟶ B, Triv (LB.div (translDiff B L x) (O.pull (snd (Over.mk f) B).left)) := by
  obtain ⟨B', _, _, g, h, hB'⟩ : ∃ (B' : Over (Spec (CommRingCat.of K))) (_ : GrpObj B') (_ : IsCommMonObj B')
      (g : B'.left ⟶ B.left), IsGrpPullback B' B f g ∧ IsAbelianScheme B' :=
    ⟨(Over.pullback f).obj B, inferInstance, (TLinPf.isAb_pullback f B hB).comm, _, isGrpPullback_pullback B f,
      TLinPf.isAb_pullback f B hB⟩
  have hg := h.1
  have hm : ∀ (T : Over (Spec (CommRingCat.of K))) (x y : T ⟶ B'),
      toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y := fun T x y =>
    Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm
  have hL' := pull_isLB hL g
  have hd' : SmoothOfRelativeDimension d B'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hg hd
  obtain ⟨w₀, hw₀⟩ : LBIso (L.pull g) (L.pull g) := ⟨idIso _, idIso_isGen hL'⟩
  have ha' : RelAmple B' (L.pull g) :=
    relAmple_pull hg hL hL' ((isGen_iff w₀).1 hw₀) ⊤ (isAffineOpen_top _) (fun _ => trivial) ha
  have hk' : KTriv B' (L.pull g) := kTriv_pull h hL hL' ((isGen_iff w₀).1 hw₀) hk
  have hΘ' := theta_pull h hΘ
  have hc : CechPic.pull g (cls L hL) = cls (L.pull g) hL' := (cls_pull hL _ _).symm
  have hO' := pull_isLB hO g
  have one : ∀ T : Over (Spec (CommRingCat.of K)), toBase hg.w (1 : T ⟶ B') = 1 := fun T => by
    have := hm T 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have lamO : lam (cls O hO) (fst B B) (snd B B) = 0 :=
    (cls_cube_two hO _ _ (LB.isLB_linComb hO _ _)).symm.trans ((cls_eq_zero_iff _).2 hu)
  have lamO' : lam (cls _ hO') (fst B' B') (snd B' B') = 0 := by
    have e := congrArg (CechPic.pull (lift (toBase hg.w (fst B' B')) (toBase hg.w (snd B' B'))).left) lamO
    rw [pull_lam, lift_fst, lift_snd, map_zero, lam, ← hm, ← one] at e
    rw [cls_pull hO, lam, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp]
    exact e
  obtain ⟨x', hx'⟩ := GlobalTheory.T.exists_point_translate_primitive_of_ample_K_trivial K B' d (L.pull g) (O.pull g) hB' hd' hL' ha' hk' hΘ' hO'
    ((cls_eq_zero_iff (LB.isLB_linComb hO' _ _)).1 ((cls_cube_two hO' _ _ (LB.isLB_linComb hO' _ _)).trans lamO'))
  have e := ((cls_eq_iff hO' (LB.isLB_linComb hL' _ _)).2 hx').trans (cls_pair hL' _ _ _)
  let T : Over (Sp A) := Over.mk f
  have wx : x'.left ≫ B'.hom = 𝟙 _ := Over.w x'
  let x : T ⟶ B := Over.homMk (x'.left ≫ g) (by
    show (x'.left ≫ g) ≫ B.hom = f
    rw [Category.assoc, hg.w, ← Category.assoc, wx]
    exact Category.id_comp _)
  have w : (snd T B).left ≫ B.hom = (fst T B).left ≫ f := (Over.w (snd T B)).trans (Over.w (fst T B)).symm
  let T' : Over (Spec (CommRingCat.of K)) := Over.mk (Y := (T ⊗ B).left) (fst T B).left
  let h : T' ⟶ B' := Over.homMk (hg.lift (snd T B).left (fst T B).left w) (hg.lift_snd _ _ _)
  have hh : h.left ≫ g = (snd T B).left := hg.lift_fst _ _ _
  let u : Over.mk (T'.hom ≫ f) ⟶ T ⊗ B := Over.homMk (𝟙 _) ((Category.id_comp _).trans (Over.w (fst T B)).symm)
  have b₁ : u ≫ snd T B = toBase hg.w h := Over.OverMorphism.ext ((Category.id_comp _).trans hh.symm)
  have b₂ : u ≫ fst T B ≫ x = toBase hg.w (toUnit T' ≫ x') := by
    refine Over.OverMorphism.ext ((Category.id_comp _).trans ?_)
    have : (toUnit T').left = (fst T B).left := (Category.comp_id _).symm.trans (Over.w (toUnit T'))
    show (fst T B).left ≫ x'.left ≫ g = ((toUnit T').left ≫ x'.left) ≫ g
    rw [this]
    exact (Category.assoc _ _ _).symm
  have b : h.left ≫ ((toUnit B' ≫ x') * 𝟙 B').left ≫ g = ((fst T B ≫ x) * snd T B).left := by
    have b₃ : toBase hg.w (h ≫ ((toUnit B' ≫ x') * 𝟙 B')) = u ≫ ((fst T B ≫ x) * snd T B) := by
      rw [MonObj.comp_mul, MonObj.comp_mul, b₁, b₂, ← hm, Category.comp_id, ← Category.assoc, comp_toUnit]
    exact (Category.assoc _ _ _).symm.trans ((congrArg CommaMorphism.left b₃).trans (Category.id_comp _))
  have e' := congrArg (CechPic.pull h.left) e
  rw [cls_pull hO, ← hc, pull_id, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, Category.assoc, b, hh] at e'
  have h₁ : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _
  have h₂ := pull_isLB hO (snd T B).left
  refine ⟨x, (cls_eq_zero_iff (LB.isLB_div h₁ h₂)).1 ?_⟩
  rw [cls_div h₁ h₂, sub_eq_zero]
  exact (cls_pair hL _ _ h₁).trans e'.symm

/- English proof (translation)
Introduce `V _ _ _ B _ _ d L O hB hd hL ha hk hΘ hO hu`. Establish `hG : GlobalFnsSt` using `GlobalTheory.T.all_six_abelian_scheme_laws_hold.1.globalFns`. Establish `proj : IsProjBy B.hom`. Take `⟨d, -, n, s, hs⟩` from `(GlobalTheory.Unif.relAmple_iff_veryAmpleBy V B L hL).1 ha`. Conclude with `⟨_, isLB_pw hL _, n, s, hs⟩`.

Take `⟨H, j, hj, hH⟩` from `GlobalTheory.T.exists_closed_subscheme_translation_kernel hG V B hB proj L O hL hO`. Establish `fin : IsFinite H.hom` using `GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG V B hB L O hL hO ha H j hj hH`. Establish `mono : Mono H.hom` using `⟨fun {Z} a b e => by`. Set `a' : Over.mk (b ≫ H.hom) ⟶ H` to `Over.homMk a e`. Set `b' : Over.mk (b ≫ H.hom) ⟶ H` to `Over.homMk b rfl`.

Use `(inK_mul_inv hL hO (a' ≫ j) (b' ≫ j) ((hH _ _).2 ⟨_, rfl⟩) ((hH _ _).2 ⟨_, rfl⟩)).eq_one hk` as an intermediate fact. Rewrite `this` using `[mul_inv_eq_one]`. Conclude with `(cancel_mono j.left).1 (congrArg CommaMorphism.left this)⟩`. Establish `: IsClosedImmersion H.hom` using `(IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨fin, mono⟩`. Set `K : Type` to `AlgebraicClosure (IsLocalRing.ResidueField V)`.

Set `φ : V →+* K` to `(algebraMap (IsLocalRing.ResidueField V) K).comp (IsLocalRing.residue V)`. Establish `: IsLocalHom φ` using `RingHom.isLocalHom_comp _ _`. Take `⟨x₀, hx₀⟩` from `exists_geometric_point hB hd hL ha hk hΘ hO hu K (Spec.map (CommRingCat.ofHom φ))`. Take `⟨y, -⟩` from `(hH _ x₀).1 fun p => ⟨⊤, trivial, by`. Establish `hM` using `LB.isLB_div (show (translDiff B L x₀).IsLB from LB.isLB_linComb hL _ _) (pull_isLB hO (snd _ B).left)`.

Use `(cls_eq_zero_iff (pull_isLB hM _)).1 ?_` and prove the remaining obligations. Rewrite using `[cls_pull hM, (cls_eq_zero_iff hM).2 hx₀, map_zero]⟩`. Set `y' : Spec (CommRingCat.of K) ⟶ H.left` to `y.left`. Establish `hy : H.hom (y' (IsLocalRing.closedPoint K)) = IsLocalRing.closedPoint V` using `(congrArg (fun q => q (IsLocalRing.closedPoint K)) (Over.w y)).trans (IsLocalRing.comap_closedPoint φ)`. Take `⟨R, _, _, _, _, ξ, g₀, hfl, hξ, hξV, hg₀, hξK, hreg, hdim⟩` from `FibreAcyclic.exists_localRing B.hom d hd (y' ≫ j.left) (by`.

Use `j.left.isClosedEmbedding.isClosedMap _ (isClosed_of_isFinite H.hom _ hy)` as an intermediate fact. Rewrite using `[Set.image_singleton] at this) ((congrArg (fun q => q (y' (IsLocalRing.closedPoint K))) (Over.w j)).trans hy)` and apply the resulting hypothesis. Take `⟨I, C, c₁, ⟨n, c₂⟩, ⟨e⟩, c₃, hI⟩` from `exists_ideal_complex hG B hB proj hd hL hO hΘ hu j hH R ξ K g₀ hg₀ ⟨y', hξK.symm⟩`. Establish `hI₀ : I ≠ ⊤` using `ne_top_of_le_ne_top (RingHom.ker_ne_top g₀) ((hI K g₀).1 ⟨y', hξK.symm⟩)`. Establish `: Nontrivial (R ⧸ I)` using `Ideal.Quotient.nontrivial_iff.2 hI₀`.

Establish `: IsLocalRing (R ⧸ I)` using `IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective`. Take `⟨w, hw⟩` from `(hI (R ⧸ I) (Ideal.Quotient.mk I)).2 Ideal.mk_ker.ge`. Establish `hwV : w ≫ H.hom = Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I)))`. Rewrite using `[← Over.w j, ← Category.assoc, hw, Category.assoc, hξV, ← Spec.map_comp]`. Both sides reduce to the same expression.

Establish `hN : (IsLocalRing.maximalIdeal V).map (algebraMap V R) ≤ IsLocalRing.maximalIdeal R` using `IsLocalRing.le_maximalIdeal (Ideal.Quotient.nontrivial_iff.1 inferInstance)`. Establish `hloc : IsLocalHom (algebraMap V R)` using `((IsLocalRing.local_hom_TFAE (algebraMap V R)).out 2 0).1 hN`. Establish `hsurj : Function.Surjective (algebraMap V (R ⧸ I))`. Establish `: IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))` using `IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective`. Establish `: IsPreimmersion (w ≫ j.left)` using `hw ▸ inferInstance`.

Establish `: IsPreimmersion w` using `IsPreimmersion.of_comp w j.left`. Establish `h₁ : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I))))` using `hwV ▸ inferInstance`. Establish `: IsLocalHom (Ideal.Quotient.mk I)` using `IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective`. Establish `: IsLocalHom (algebraMap V (R ⧸ I))` using `RingHom.isLocalHom_comp (Ideal.Quotient.mk I) (algebraMap V R)`. Conclude with `RingHom.surjectiveOnStalks_iff_of_isLocalHom.1 ((IsPreimmersion.SpecMap_iff _).1 h₁).2`.

Establish `hinj : Function.Injective (algebraMap V (R ⧸ I))`. Establish `hfree` using `fun i => (c₁ i).1`. Establish `hfin` using `fun i => (c₁ i).2`. Use `FibreAcyclic.injective_of_exact (C.d 0 1).hom (C.d 1 2).hom (DualCokernel.d_d_apply C 0 1 2) ?_ I hI₀ e hsurj` and prove the remaining obligations. Use `FibreAcyclic.exact_hom_one _ hN _ (fun s hs x => ?_) d (FibreAcyclic.extZero_quotient _ _ hdim) C c₁ n c₂ fun p hp hNp => ?_` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hs, zero_mul]`. Take `⟨K', _, ψ, hψ, hex⟩` from `c₃ p hp`. Use `⟨K', inferInstance, ψ, hψ, fun i hi => hex i (hi.imp_left fun hne hIp => hne ?_)⟩` and prove the remaining obligations. Use `(IsLocalRing.le_maximalIdeal hp.ne_top).antisymm fun s hs => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `hsurj (Ideal.Quotient.mk I s)`.

Establish `h₁ : algebraMap V R a - s ∈ I` using `Ideal.Quotient.eq.1 ha`. Establish `h₂ : algebraMap V R a ∈ IsLocalRing.maximalIdeal R`. Simplify using `using add_mem (IsLocalRing.le_maximalIdeal hI₀ h₁) hs`. Establish `h₃ : a ∈ IsLocalRing.maximalIdeal V` using `fun h => h₂ (h.map _)`. Simplify using `using sub_mem (hNp (Ideal.mem_map_of_mem _ h₃)) (hIp h₁)`.

Establish `: IsIso (CommRingCat.ofHom (algebraMap V (R ⧸ I)))` using `(ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj, hsurj⟩`. Set `σ : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ H` to `Over.homMk (inv (Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I)))) ≫ w) (by`. Rewrite using `[Category.assoc, hwV]`. Conclude with `IsIso.inv_hom_id _)`. Take `⟨U, hU, ht⟩` from `(hH _ (σ ≫ j)).2 ⟨σ, rfl⟩ (IsLocalRing.closedPoint V)`.

Take `rfl : U = ⊤` from `(IsLocalRing.closedPoint_mem_iff U).1 hU`. Establish `e` using `pull_eq_zero_of_mem ((fst _ B).left ⁻¹ᵁ ⊤) (lift (toUnit B) (𝟙 B)).left (fun _ => trivial) ((triv_iff hL hO (σ ≫ j) _).1 ht)`. Rewrite `e` using `[map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul, lift_snd, lift_fst_assoc, sub_eq_zero, Over.id_left, pull_id (cls O hO)]`. Conclude with `⟨σ ≫ j, (cls_eq_iff hO (LB.isLB_linComb hL _ _)).1 (e.symm.trans (cls_pair hL _ _ _).symm)⟩`.
-/
theorem exists_section_translate : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L O : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∃ t : LB.Gen (Theta B L), t.IsGen) → O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ B, LBIso O (LB.LinComb L (K := Fin 2) ![((toUnit B ≫ x) * 𝟙 B).left, 𝟙 B.left] ![1, -1]) := by
  intro V _ _ _ B _ _ d L O hB hd hL ha hk hΘ hO hu
  have hG : GlobalFnsSt := GlobalTheory.T.all_six_abelian_scheme_laws_hold.1.globalFns
  have proj : IsProjBy B.hom := by
    obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy V B L hL).1 ha
    exact ⟨_, isLB_pw hL _, n, s, hs⟩
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hG V B hB proj L O hL hO
  have fin : IsFinite H.hom := GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG V B hB L O hL hO
    ha H j hj hH
  have mono : Mono H.hom := ⟨fun {Z} a b e => by
    let a' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk a e
    let b' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk b rfl
    have := (inK_mul_inv hL hO (a' ≫ j) (b' ≫ j) ((hH _ _).2 ⟨_, rfl⟩) ((hH _ _).2 ⟨_, rfl⟩)).eq_one hk
    rw [mul_inv_eq_one] at this
    exact (cancel_mono j.left).1 (congrArg CommaMorphism.left this)⟩
  have : IsClosedImmersion H.hom := (IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨fin, mono⟩
  let K : Type := AlgebraicClosure (IsLocalRing.ResidueField V)
  let φ : V →+* K := (algebraMap (IsLocalRing.ResidueField V) K).comp (IsLocalRing.residue V)
  have : IsLocalHom φ := RingHom.isLocalHom_comp _ _
  obtain ⟨x₀, hx₀⟩ := exists_geometric_point hB hd hL ha hk hΘ hO hu K (Spec.map (CommRingCat.ofHom φ))
  obtain ⟨y, -⟩ := (hH _ x₀).1 fun p => ⟨⊤, trivial, by
    have hM := LB.isLB_div (show (translDiff B L x₀).IsLB from LB.isLB_linComb hL _ _)
      (pull_isLB hO (snd _ B).left)
    refine (cls_eq_zero_iff (pull_isLB hM _)).1 ?_
    rw [cls_pull hM, (cls_eq_zero_iff hM).2 hx₀, map_zero]⟩
  let y' : Spec (CommRingCat.of K) ⟶ H.left := y.left
  have hy : H.hom (y' (IsLocalRing.closedPoint K)) = IsLocalRing.closedPoint V :=
    (congrArg (fun q => q (IsLocalRing.closedPoint K)) (Over.w y)).trans (IsLocalRing.comap_closedPoint φ)
  obtain ⟨R, _, _, _, _, ξ, g₀, hfl, hξ, hξV, hg₀, hξK, hreg, hdim⟩ :=
    FibreAcyclic.exists_localRing B.hom d hd (y' ≫ j.left) (by
      have := j.left.isClosedEmbedding.isClosedMap _ (isClosed_of_isFinite H.hom _ hy)
      rwa [Set.image_singleton] at this) ((congrArg (fun q => q (y' (IsLocalRing.closedPoint K))) (Over.w j)).trans hy)
  obtain ⟨I, C, c₁, ⟨n, c₂⟩, ⟨e⟩, c₃, hI⟩ := exists_ideal_complex hG B hB proj hd hL hO
    hΘ hu j hH R ξ K g₀ hg₀ ⟨y', hξK.symm⟩
  have hI₀ : I ≠ ⊤ := ne_top_of_le_ne_top (RingHom.ker_ne_top g₀) ((hI K g₀).1 ⟨y', hξK.symm⟩)
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI₀
  have : IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨w, hw⟩ := (hI (R ⧸ I) (Ideal.Quotient.mk I)).2 Ideal.mk_ker.ge
  have hwV : w ≫ H.hom = Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I))) := by
    rw [← Over.w j, ← Category.assoc, hw, Category.assoc, hξV, ← Spec.map_comp]
    rfl
  have hN : (IsLocalRing.maximalIdeal V).map (algebraMap V R) ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (Ideal.Quotient.nontrivial_iff.1 inferInstance)
  have hloc : IsLocalHom (algebraMap V R) := ((IsLocalRing.local_hom_TFAE (algebraMap V R)).out 2 0).1 hN
  have hsurj : Function.Surjective (algebraMap V (R ⧸ I)) := by
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : IsPreimmersion (w ≫ j.left) := hw ▸ inferInstance
    have : IsPreimmersion w := IsPreimmersion.of_comp w j.left
    have h₁ : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I)))) := hwV ▸ inferInstance
    have : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have : IsLocalHom (algebraMap V (R ⧸ I)) := RingHom.isLocalHom_comp (Ideal.Quotient.mk I) (algebraMap V R)
    exact RingHom.surjectiveOnStalks_iff_of_isLocalHom.1 ((IsPreimmersion.SpecMap_iff _).1 h₁).2
  have hinj : Function.Injective (algebraMap V (R ⧸ I)) := by
    have hfree := fun i => (c₁ i).1
    have hfin := fun i => (c₁ i).2
    refine FibreAcyclic.injective_of_exact (C.d 0 1).hom (C.d 1 2).hom (DualCokernel.d_d_apply C 0 1 2) ?_ I hI₀ e hsurj
    refine FibreAcyclic.exact_hom_one _ hN _ (fun s hs x => ?_) d (FibreAcyclic.extZero_quotient _ _ hdim) C c₁ n c₂
      fun p hp hNp => ?_
    · rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hs, zero_mul]
    · obtain ⟨K', _, ψ, hψ, hex⟩ := c₃ p hp
      refine ⟨K', inferInstance, ψ, hψ, fun i hi => hex i (hi.imp_left fun hne hIp => hne ?_)⟩
      refine (IsLocalRing.le_maximalIdeal hp.ne_top).antisymm fun s hs => ?_
      obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk I s)
      have h₁ : algebraMap V R a - s ∈ I := Ideal.Quotient.eq.1 ha
      have h₂ : algebraMap V R a ∈ IsLocalRing.maximalIdeal R := by
        simpa using add_mem (IsLocalRing.le_maximalIdeal hI₀ h₁) hs
      have h₃ : a ∈ IsLocalRing.maximalIdeal V := fun h => h₂ (h.map _)
      simpa using sub_mem (hNp (Ideal.mem_map_of_mem _ h₃)) (hIp h₁)
  have : IsIso (CommRingCat.ofHom (algebraMap V (R ⧸ I))) := (ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj, hsurj⟩
  let σ : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ H :=
    Over.homMk (inv (Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I)))) ≫ w) (by
      rw [Category.assoc, hwV]
      exact IsIso.inv_hom_id _)
  obtain ⟨U, hU, ht⟩ := (hH _ (σ ≫ j)).2 ⟨σ, rfl⟩ (IsLocalRing.closedPoint V)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
  have e := pull_eq_zero_of_mem ((fst _ B).left ⁻¹ᵁ ⊤) (lift (toUnit B) (𝟙 B)).left (fun _ => trivial)
    ((triv_iff hL hO (σ ≫ j) _).1 ht)
  rw [map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul,
    lift_snd, lift_fst_assoc, sub_eq_zero, Over.id_left, pull_id (cls O hO)] at e
  exact ⟨σ ≫ j, (cls_eq_iff hO (LB.isLB_linComb hL _ _)).1 (e.symm.trans (cls_pair hL _ _ _).symm)⟩

end GlobalTheory.PrimitiveAmpleLocal
