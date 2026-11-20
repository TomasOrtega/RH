import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfGroupPullbackDataBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueWitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRepUniversalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixRepOfUniversalStatement

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomGlue

/- English proof (translation)
Introduce `S A B _ _ L M hL hM X u hu W T y πT hy hloc`. Take `⟨c, hc, -⟩` from `hu T y`. Establish `hcW : Set.range c ⊆ ((u.t ⁻¹ᵁ W).ι).opensRange`. Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[Scheme.Opens.opensRange_ι]`.

Use `show u.t (c z) ∈ W`. Establish `e : c ≫ u.t = πT ≫ W.ι` using `by rw [← hy, ← hc]; rfl`. Rewrite using `[← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]`. Conclude with `(πT z).2`. Set `c'` to `IsOpenImmersion.lift (u.t ⁻¹ᵁ W).ι c (by simpa using hcW)`.

Establish `hc' : c' ≫ (u.t ⁻¹ᵁ W).ι = c` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hx : (u.map hL hM (u.t ⁻¹ᵁ W).ι).t = (u.t ∣_ W) ≫ W.ι`. Rewrite using `[HomGlue.Pt.map_t, morphismRestrict_ι]`. Take `⟨d, hd, -⟩` from `hloc _ (u.map hL hM (u.t ⁻¹ᵁ W).ι) (u.t ∣_ W) hx`. Establish `h1 : c' ≫ d = 𝟙 T`.

Use `(hloc T y πT hy).unique ?_ ?_` and prove the remaining obligations. Rewrite using `[HomGlue.Pt.map_comp, hd, ← HomGlue.Pt.map_comp, hc', hc]`. Conclude with `HomGlue.Pt.map_id hL hM y`. Establish `h2 : d ≫ c' = 𝟙 _`. Establish `: d ≫ c = (u.t ⁻¹ᵁ W).ι` using `(hu _ (u.map hL hM (u.t ⁻¹ᵁ W).ι)).unique (by rw [HomGlue.Pt.map_comp, hc, hd]) rfl`.

Rewrite using `[← cancel_mono (u.t ⁻¹ᵁ W).ι, Category.assoc, hc', this, Category.id_comp]`. Use `⟨⟨c', d, h1, h2⟩, ?_⟩` and prove the remaining obligations. Use `show c' ≫ (u.t ∣_ W) = πT`. Rewrite using `[← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hc', ← hy, ← hc]`. Both sides reduce to the same expression.
-/
theorem reps_iso : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (X : Scheme.{0}) (u : HomGlue.Pt A B L M X), (∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z), ∃! c : Z ⟶ X, u.map hL hM c = x) → ∀ (W : S.Opens) (T : Scheme.{0}) (y : HomGlue.Pt A B L M T) (πT : T ⟶ W), y.t = πT ≫ W.ι → (∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z) (b : Z ⟶ W), x.t = b ≫ W.ι → ∃! c : Z ⟶ T, y.map hL hM c = x) → ∃ e : T ≅ (u.t ⁻¹ᵁ W).toScheme, e.hom ≫ (u.t ∣_ W) = πT := by
  intro S A B _ _ L M hL hM X u hu W T y πT hy hloc
  obtain ⟨c, hc, -⟩ := hu T y
  have hcW : Set.range c ⊆ ((u.t ⁻¹ᵁ W).ι).opensRange := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.opensRange_ι]
    show u.t (c z) ∈ W
    have e : c ≫ u.t = πT ≫ W.ι := by rw [← hy, ← hc]; rfl
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
    exact (πT z).2
  let c' := IsOpenImmersion.lift (u.t ⁻¹ᵁ W).ι c (by simpa using hcW)
  have hc' : c' ≫ (u.t ⁻¹ᵁ W).ι = c := IsOpenImmersion.lift_fac _ _ _
  have hx : (u.map hL hM (u.t ⁻¹ᵁ W).ι).t = (u.t ∣_ W) ≫ W.ι := by
    rw [HomGlue.Pt.map_t, morphismRestrict_ι]
  obtain ⟨d, hd, -⟩ := hloc _ (u.map hL hM (u.t ⁻¹ᵁ W).ι) (u.t ∣_ W) hx
  have h1 : c' ≫ d = 𝟙 T := by
    refine (hloc T y πT hy).unique ?_ ?_
    · rw [HomGlue.Pt.map_comp, hd, ← HomGlue.Pt.map_comp, hc', hc]
    · exact HomGlue.Pt.map_id hL hM y
  have h2 : d ≫ c' = 𝟙 _ := by
    have : d ≫ c = (u.t ⁻¹ᵁ W).ι := (hu _ (u.map hL hM (u.t ⁻¹ᵁ W).ι)).unique
      (by rw [HomGlue.Pt.map_comp, hc, hd]) rfl
    rw [← cancel_mono (u.t ⁻¹ᵁ W).ι, Category.assoc, hc', this, Category.id_comp]
  refine ⟨⟨c', d, h1, h2⟩, ?_⟩
  show c' ≫ (u.t ∣_ W) = πT
  rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hc', ← hy, ← hc]
  rfl

/- English proof (translation)
Substitute `h` using the available equality. Use `hf (𝟙 _) (Category.id_comp _) (Category.id_comp _)` as an intermediate fact. Rewrite `this` using `[Category.id_comp]`. Substitute `this` using the available equality. Conclude with `w`.
-/
theorem wit_of_eq {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
    {Z : Scheme.{0}} {t t' : Z ⟶ S} {f : pullback A.hom t ⟶ B.left} {f' : pullback A.hom t' ⟶ B.left} (h : t = t')
    (hf : ∀ e : pullback A.hom t' ⟶ pullback A.hom t, e ≫ pullback.fst _ _ = pullback.fst _ _ →
      e ≫ pullback.snd _ _ = pullback.snd _ _ → e ≫ f = f') (w : HomGlue.Wit A B L M t f) :
    HomGlue.Wit A B L M t' f' := by
  subst h
  have := hf (𝟙 _) (Category.id_comp _) (Category.id_comp _)
  rw [Category.id_comp] at this
  subst this
  exact w

/- English proof (translation)
Introduce `hiso S A B _ _ _ _ L M hL hM hA hB hrA hrB Z 𝒰 x hx`. Take `⟨t, f, h⟩` from `GlobalTheory.T.exists_glued_morphism_of_compatible_family S A B L M hL hM Z 𝒰 x hx`. Establish `hw : ∀ i, HomGlue.Wit A B L M (𝒰.f i ≫ t) (HomGlue.pmap A t (𝒰.f i) ≫ f)`. Introduce `i`. Establish `hc : pullback.fst A.hom (x i).t ≫ A.hom = (pullback.snd A.hom (x i).t ≫ 𝒰.f i) ≫ t`.

Rewrite using `[pullback.condition, Category.assoc, (h i).1]`. Use `wit_of_eq (h i).1.symm (fun e e1 e2 => ?_) (x i).wit` and prove the remaining obligations. Rewrite using `[← (h i).2 (pullback.lift _ _ hc) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _), ← Category.assoc]`. Use `congr 1`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, pullback.lift_fst, e1, pullback.lift_fst]`. Rewrite using `[Category.assoc, pullback.lift_snd, ← Category.assoc, e2, pullback.lift_snd]`. Use `⟨⟨t, f, GlobalTheory.T.glue_wit_alt hiso S A B L M hL hM hA hB hrA hrB Z 𝒰 t f hw⟩, fun i => ?_⟩` and prove the remaining obligations. Use `HomGlue.Pt.ext' (h i).1 ?_` and prove the remaining obligations. Use `show _ ≫ HomGlue.pmap A t (𝒰.f i) ≫ f = _`.

Conclude with `(Category.assoc _ _ _).symm.trans ((h i).2 _ ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans (pullback.lift_fst _ _ _))) ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans ((Category.assoc _ _ _).symm.trans (congrAr …`.
-/
theorem glue_pts : (∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left)) → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB), IsAbelianScheme A → IsAbelianScheme B → Out.Rigidified A L → Out.Rigidified B M → ∀ (Z : Scheme.{0}) (𝒰 : Z.OpenCover) (x : ∀ i, HomGlue.Pt A B L M (𝒰.X i)), (∀ i j (T : Scheme.{0}) (b : T ⟶ 𝒰.X i) (c : T ⟶ 𝒰.X j), b ≫ 𝒰.f i = c ≫ 𝒰.f j → (x i).map hL hM b = (x j).map hL hM c) → ∃ y : HomGlue.Pt A B L M Z, ∀ i, y.map hL hM (𝒰.f i) = x i := by
  intro hiso S A B _ _ _ _ L M hL hM hA hB hrA hrB Z 𝒰 x hx
  obtain ⟨t, f, h⟩ := GlobalTheory.T.exists_glued_morphism_of_compatible_family S A B L M hL hM Z 𝒰 x hx
  have hw : ∀ i, HomGlue.Wit A B L M (𝒰.f i ≫ t) (HomGlue.pmap A t (𝒰.f i) ≫ f) := by
    intro i
    have hc : pullback.fst A.hom (x i).t ≫ A.hom = (pullback.snd A.hom (x i).t ≫ 𝒰.f i) ≫ t := by
      rw [pullback.condition, Category.assoc, (h i).1]
    refine wit_of_eq (h i).1.symm (fun e e1 e2 => ?_) (x i).wit
    rw [← (h i).2 (pullback.lift _ _ hc) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _), ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, e1, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, e2, pullback.lift_snd]
  refine ⟨⟨t, f, GlobalTheory.T.glue_wit_alt hiso S A B L M hL hM hA hB hrA hrB Z 𝒰 t f hw⟩, fun i => ?_⟩
  refine HomGlue.Pt.ext' (h i).1 ?_
  show _ ≫ HomGlue.pmap A t (𝒰.f i) ≫ f = _
  exact (Category.assoc _ _ _).symm.trans ((h i).2 _
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans (pullback.lift_fst _ _ _)))
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ 𝒰.f i) (pullback.lift_snd _ _ _))))))

/- English proof (translation)
Introduce `hiso S A B _ _ _ _ L M hL hM hA hB hrA hrB`. Rewrite using `[Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]`. Introduce and unpack `Y P hP`. Take `⟨(𝒰 : Scheme.OpenCover Y), rfl⟩` from `Scheme.exists_cover_of_mem_pretopology hP`. Rewrite using `[Presieve.isSheafFor_arrows_iff]`.

Introduce `x hx`. Conclude with `existsUnique_of_exists_of_unique (glue_pts hiso S A B L M hL hM hA hB hrA hrB Y 𝒰 x fun i j T b c h => hx i j T b c h) fun y y' h h' => GlobalTheory.T.homGlue_pt_ext_of_openCover S A B L M hL hM Y 𝒰 y y' fun i => (h i).trans (h' i).symm`.
-/
theorem isSheaf_homFun : (∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left)) → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB), IsAbelianScheme A → IsAbelianScheme B → Out.Rigidified A L → Out.Rigidified B M → Presieve.IsSheaf Scheme.zariskiTopology (HomGlue.homFun A B L M hL hM) := by
  intro hiso S A B _ _ _ _ L M hL hM hA hB hrA hrB
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y P hP
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hP
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  exact existsUnique_of_exists_of_unique
    (glue_pts hiso S A B L M hL hM hA hB hrA hrB Y 𝒰 x fun i j T b c h => hx i j T b c h)
    fun y y' h h' => GlobalTheory.T.homGlue_pt_ext_of_openCover S A B L M hL hM Y 𝒰 y y' fun i => (h i).trans (h' i).symm

/- English proof (translation)
Introduce `hiso S A B _ _ _ _ L M hA hB hL hM hrA hrB Ix V j hj hcov hR`. Use `choose A' B' gA gB φA φB R hpA hpB hqc hsep hlft using hR`. Establish `hy : ∀ i, ∃ y : HomGlue.Pt A B L M (R i).H, y.t = (R i).π ≫ j i ∧ ∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z) (b : Z ⟶ V i), x.t = b ≫ j i → ∃! c : Z ⟶ (R i).H, y.map hL hM c = x`. Introduce `i`. Use `letI := gA i`.

Use `letI := gB i`. Conclude with `GlobalTheory.T.exists_universal_pt_of_isGrpPullback S A B L M hL hM (V i) (j i) (A' i) (B' i) (φA i) (φB i) (R i) (hpA i) (hpB i)`. Use `choose y hyt hyu using hy`. Set `W : Ix → S.Opens` to `fun i => (j i).opensRange`. Establish `hW : iSup W = ⊤`.

Use `top_le_iff.1 fun s _ => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `hcov s`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩`. Set `πW : ∀ i, (R i).H ⟶ W i` to `fun i => (R i).π ≫ (j i).isoOpensRange.hom`. Establish `hπW : ∀ i, πW i ≫ (W i).ι = (R i).π ≫ j i` using `fun i => by`.

Simplify using `[πW, W]`. Establish `hloc : ∀ i (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z) (b : Z ⟶ W i), x.t = b ≫ (W i).ι → ∃! c : Z ⟶ (R i).H, (y i).map hL hM c = x`. Introduce `i Z x b hb`. Use `hyu i Z x (b ≫ (j i).isoOpensRange.inv) ?_` and prove the remaining obligations. Rewrite using `[hb, Category.assoc]`.

Simplify using `[W]`. Establish `hrep : (HomGlue.homFun A B L M hL hM).IsRepresentable` using `GlobalTheory.GenTorsor.isRepresentable_of_cover _ (isSheaf_homFun hiso S A B L M hL hM hA hB hrA hrB) (HomGlue.homProj A B L M hL hM) W hW (fun i => (R i).H) y πW (fun i => (hyt i).trans (hπW i).symm) hloc`. Use `set F := HomGlue.homFun A B L M hL hM`. Set `X` to `F.reprX`. Set `u : HomGlue.Pt A B L M X` to `F.reprx`.

Establish `huniv : ∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z), ∃! c : Z ⟶ X, u.map hL hM c = x`. Introduce `Z x`. Establish `key : ∀ c : Z ⟶ X, u.map hL hM c = F.representableBy.homEquiv c` using `fun c => by`. Rewrite using `[F.representableBy.homEquiv_eq c]`. Both sides reduce to the same expression.

Use `⟨F.representableBy.homEquiv.symm x, ?_, fun c hc => ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[key]`. Conclude with `F.representableBy.homEquiv.apply_symm_apply x`. Simplify using `only at hc`.

Rewrite `hc` using `[key]`. Rewrite using `[← hc]`. Conclude with `(F.representableBy.homEquiv.symm_apply_apply c).symm`. Take `⟨R0, e, he⟩` from `GlobalTheory.T.exists_homFixRep_iso_of_universal S A B L M hL hM X u huniv`. Establish `hloc' : ∀ i, ∃ e : (R i).H ≅ (u.t ⁻¹ᵁ W i).toScheme, e.hom ≫ (u.t ∣_ W i) = πW i` using `fun i => reps_iso S A B L M hL hM X u huniv (W i) (R i).H (y i) (πW i) ((hyt i).trans (hπW i).symm) (hloc i)`.

Use `choose ei hei using hloc'`. Establish `key : ∀ i, u.t ∣_ W i = (ei i).inv ≫ πW i` using `fun i => by`. Rewrite using `[← hei i, Iso.inv_hom_id_assoc]`. Establish `hP : ∀ (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P], (∀ i, P (R i).π) → P R0.π`. Introduce `P _ hR`.

Rewrite using `[← he]`. Use `(MorphismProperty.cancel_left_of_respectsIso P e.hom u.t).2 ?_` and prove the remaining obligations. Use `IsZariskiLocalAtTarget.of_iSup_eq_top W hW fun i => ?_` and prove the remaining obligations. Rewrite using `[key i]`. Use `(MorphismProperty.cancel_left_of_respectsIso P _ _).2 ?_` and prove the remaining obligations.

Conclude with `(MorphismProperty.cancel_right_of_respectsIso P _ _).2 (hR i)`. Establish `: IsZariskiLocalAtTarget @QuasiCompact.{0}` using `by set_option backward.isDefEq.respectTransparency.types false in exact inferInstance`. Establish `: IsZariskiLocalAtTarget @LocallyOfFiniteType.{0}` using `HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFiniteType)`. Conclude with `⟨R0, hP @QuasiCompact hqc, hP @IsSeparated hsep, hP @LocallyOfFiniteType hlft⟩`.
-/
theorem homFixRep_glue : (∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left)) → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → ∀ (Ix : Type) (V : Ix → Scheme.{0}) (j : ∀ i, V i ⟶ S), (∀ i, IsOpenImmersion (j i)) → (∀ s : S, ∃ i, s ∈ Set.range (j i)) → (∀ i, ∃ (A' B' : Over (V i)) (_ : GrpObj A') (_ : GrpObj B') (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (R : HomFixRep A' B' (L.pull φA) (M.pull φB)), IsGrpPullback A' A (j i) φA ∧ IsGrpPullback B' B (j i) φB ∧ QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro hiso S A B _ _ _ _ L M hA hB hL hM hrA hrB Ix V j hj hcov hR
  choose A' B' gA gB φA φB R hpA hpB hqc hsep hlft using hR
  have hy : ∀ i, ∃ y : HomGlue.Pt A B L M (R i).H, y.t = (R i).π ≫ j i ∧ ∀ (Z : Scheme.{0})
      (x : HomGlue.Pt A B L M Z) (b : Z ⟶ V i), x.t = b ≫ j i → ∃! c : Z ⟶ (R i).H, y.map hL hM c = x := by
    intro i
    letI := gA i; letI := gB i
    exact GlobalTheory.T.exists_universal_pt_of_isGrpPullback S A B L M hL hM (V i) (j i) (A' i) (B' i) (φA i) (φB i) (R i) (hpA i) (hpB i)
  choose y hyt hyu using hy
  let W : Ix → S.Opens := fun i => (j i).opensRange
  have hW : iSup W = ⊤ := by
    refine top_le_iff.1 fun s _ => ?_
    obtain ⟨i, hi⟩ := hcov s
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  let πW : ∀ i, (R i).H ⟶ W i := fun i => (R i).π ≫ (j i).isoOpensRange.hom
  have hπW : ∀ i, πW i ≫ (W i).ι = (R i).π ≫ j i := fun i => by
    simp [πW, W]
  have hloc : ∀ i (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z) (b : Z ⟶ W i), x.t = b ≫ (W i).ι →
      ∃! c : Z ⟶ (R i).H, (y i).map hL hM c = x := by
    intro i Z x b hb
    refine hyu i Z x (b ≫ (j i).isoOpensRange.inv) ?_
    rw [hb, Category.assoc]; simp [W]
  have hrep : (HomGlue.homFun A B L M hL hM).IsRepresentable :=
    GlobalTheory.GenTorsor.isRepresentable_of_cover _ (isSheaf_homFun hiso S A B L M hL hM hA hB hrA hrB) (HomGlue.homProj A B L M hL hM)
      W hW (fun i => (R i).H) y πW (fun i => (hyt i).trans (hπW i).symm) hloc
  set F := HomGlue.homFun A B L M hL hM
  let X := F.reprX
  let u : HomGlue.Pt A B L M X := F.reprx
  have huniv : ∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z), ∃! c : Z ⟶ X, u.map hL hM c = x := by
    intro Z x
    have key : ∀ c : Z ⟶ X, u.map hL hM c = F.representableBy.homEquiv c := fun c => by
      rw [F.representableBy.homEquiv_eq c]; rfl
    refine ⟨F.representableBy.homEquiv.symm x, ?_, fun c hc => ?_⟩
    · dsimp only; rw [key]; exact F.representableBy.homEquiv.apply_symm_apply x
    · dsimp only at hc; rw [key] at hc; rw [← hc]; exact (F.representableBy.homEquiv.symm_apply_apply c).symm
  obtain ⟨R0, e, he⟩ := GlobalTheory.T.exists_homFixRep_iso_of_universal S A B L M hL hM X u huniv
  have hloc' : ∀ i, ∃ e : (R i).H ≅ (u.t ⁻¹ᵁ W i).toScheme, e.hom ≫ (u.t ∣_ W i) = πW i := fun i =>
    reps_iso S A B L M hL hM X u huniv (W i) (R i).H (y i) (πW i) ((hyt i).trans (hπW i).symm) (hloc i)
  choose ei hei using hloc'
  have key : ∀ i, u.t ∣_ W i = (ei i).inv ≫ πW i := fun i => by
    rw [← hei i, Iso.inv_hom_id_assoc]
  have hP : ∀ (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P],
      (∀ i, P (R i).π) → P R0.π := by
    intro P _ hR
    rw [← he]
    refine (MorphismProperty.cancel_left_of_respectsIso P e.hom u.t).2 ?_
    refine IsZariskiLocalAtTarget.of_iSup_eq_top W hW fun i => ?_
    rw [key i]
    refine (MorphismProperty.cancel_left_of_respectsIso P _ _).2 ?_
    exact (MorphismProperty.cancel_right_of_respectsIso P _ _).2 (hR i)
  have : IsZariskiLocalAtTarget @QuasiCompact.{0} := by
    set_option backward.isDefEq.respectTransparency.types false in exact inferInstance
  have : IsZariskiLocalAtTarget @LocallyOfFiniteType.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFiniteType)
  exact ⟨R0, hP @QuasiCompact hqc, hP @IsSeparated hsep, hP @LocallyOfFiniteType hlft⟩

end GlobalTheory.EndLoc.HomGlue
