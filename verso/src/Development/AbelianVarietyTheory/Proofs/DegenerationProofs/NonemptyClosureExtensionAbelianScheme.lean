import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByOfSpans
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeZeroOfLe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionExtendingTorsionPointsSupportStatement
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ClosureLifting

/- English proof (translation)
Establish `hr : Set.range gp ⊆ Set.range j`. Rewrite using `[hgp, Set.singleton_subset_iff]`. Conclude with `(genericPoint_specializes (j (Classical.arbitrary Y))).mem_open j.isOpenEmbedding.isOpen_range ⟨_, rfl⟩`. Conclude with `⟨_, IsOpenImmersion.lift_fac j gp hr⟩`.
-/
theorem exists_lift {Z Y : Scheme.{0}} [IsIntegral Z] {K : Type} [Field K] (gp : Sp K ⟶ Z)
    (hgp : Set.range gp = {genericPoint Z}) (j : Y ⟶ Z) [IsOpenImmersion j] [Nonempty Y] :
    ∃ x : Sp K ⟶ Y, x ≫ j = gp := by
  have hr : Set.range gp ⊆ Set.range j := by
    rw [hgp, Set.singleton_subset_iff]
    exact (genericPoint_specializes (j (Classical.arbitrary Y))).mem_open
      j.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
  exact ⟨_, IsOpenImmersion.lift_fac j gp hr⟩

/- English proof (translation)
Use `HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)` as an intermediate fact. Use `IsZariskiLocalAtSource.of_openCover (P := @Flat) Z.affineOpenCover.openCover fun i => ?_` and prove the remaining obligations. Set `R` to `Z.affineOpenCover.X i`. Set `j : Spec R ⟶ Z` to `Z.affineOpenCover.f i`. Establish `: IsOpenImmersion j` using `Z.affineOpenCover.map_prop i`.

Express the relevant statement in the definitionally equal form `Flat (j ≫ π)`. Break down `isEmpty_or_nonempty (Spec R) with h | h` into its components or cases. Use `infer_instance`. Take `⟨x, -⟩` from `exists_lift gp hgp j`. Establish `: IsIntegral (Spec R)` using `isIntegral_of_isOpenImmersion j`.

Establish `: IsDomain R` using `(affine_isIntegral_iff R).1 this`. Establish `: CharZero R` using `(Spec.preimage x).hom.charZero`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (j ≫ π)`. Rewrite using `[← hφ, HasRingHomProperty.Spec_iff (P := @Flat)]`. Establish `e : φ.hom = algebraMap ℤ R` using `RingHom.ext_int _ _`.

Rewrite using `[e, RingHom.flat_algebraMap_iff]`. Use `infer_instance`.
-/
theorem flat_of_charZero {Z : Scheme.{0}} [IsIntegral Z] {K : Type} [Field K] [CharZero K] (gp : Sp K ⟶ Z)
    (hgp : Set.range gp = {genericPoint Z}) (π : Z ⟶ Sp ℤ) : Flat π := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  refine IsZariskiLocalAtSource.of_openCover (P := @Flat) Z.affineOpenCover.openCover fun i => ?_
  let R := Z.affineOpenCover.X i
  let j : Spec R ⟶ Z := Z.affineOpenCover.f i
  have : IsOpenImmersion j := Z.affineOpenCover.map_prop i
  change Flat (j ≫ π)
  rcases isEmpty_or_nonempty (Spec R) with h | h
  · infer_instance
  obtain ⟨x, -⟩ := exists_lift gp hgp j
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion j
  have : IsDomain R := (affine_isIntegral_iff R).1 this
  have : CharZero R := (Spec.preimage x).hom.charZero
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ π)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @Flat)]
  have e : φ.hom = algebraMap ℤ R := RingHom.ext_int _ _
  rw [e, RingHom.flat_algebraMap_iff]
  infer_instance

/- English proof (translation)
Use `choose W h hz hq hξ using H`. Establish `hd : IsDominant gp` using `⟨by`. Rewrite using `[DenseRange, hgp, dense_iff_closure_eq]`. Conclude with `genericPoint_spec Z⟩`. Establish `hx : ∀ z, ∃ x : Sp K ⟶ (W z).toScheme, x ≫ (W z).ι = gp` using `fun z =>`.

Establish `: Nonempty (W z).toScheme` using `⟨⟨z, hz z⟩⟩`. Use `exists_lift gp hgp _`. Use `choose x hx using hx`. Establish `hW : TopologicalSpace.IsOpenCover W` using `top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hz z⟩`. Set `𝒰` to `Z.openCoverOfIsOpenCover W hW`.

Establish `hc : ∀ a b, pullback.fst (W a).ι (W b).ι ≫ h a = pullback.snd (W a).ι (W b).ι ≫ h b`. Introduce `a b`. Set `m : Sp K ⟶ pullback (W a).ι (W b).ι` to `pullback.lift (x a) (x b) ((hx a).trans (hx b).symm)`. Establish `e : m ≫ pullback.fst _ _ ≫ (W a).ι = gp` using `by rw [pullback.lift_fst_assoc, hx]`. Establish `: IsDominant (m ≫ pullback.fst _ _ ≫ (W a).ι)` using `e ▸ hd`.

Establish `: IsDominant m` using `.of_comp_of_isOpenImmersion m (pullback.fst _ _ ≫ (W a).ι)`. Establish `: IsReduced (pullback (W a).ι (W b).ι)` using `isReduced_of_isOpenImmersion (pullback.fst _ _ ≫ (W a).ι)`. Use `ext_of_isDominant_of_isSeparated q ?_ m ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, hq, hq, pullback.condition]`. Rewrite using `[pullback.lift_fst_assoc, pullback.lift_snd_assoc, hξ _ _ (hx a), hξ _ _ (hx b)]`.

Establish `he : ∀ a, (W a).ι ≫ 𝒰.glueMorphisms h hc = h a` using `fun a => 𝒰.ι_glueMorphisms h hc a`. Use `⟨𝒰.glueMorphisms h hc, 𝒰.hom_ext _ _ fun (a : Z) => ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(W a).ι ≫ _ = (W a).ι ≫ _`. Rewrite using `[← Category.assoc, he, hq, Category.comp_id]`. Rewrite using `[← hx (genericPoint Z), Category.assoc, he, hξ _ _ (hx _)]`.
-/
theorem exists_section_of_local {Z G : Scheme.{0}} [IsIntegral Z] {K : Type} [Field K] (gp : Sp K ⟶ Z)
    (hgp : Set.range gp = {genericPoint Z}) (q : G ⟶ Z) [IsSeparated q] (ξ : Sp K ⟶ G)
    (H : ∀ z : Z, ∃ (W : Z.Opens) (h : W.toScheme ⟶ G), z ∈ W ∧ h ≫ q = W.ι ∧
      ∀ x : Sp K ⟶ W.toScheme, x ≫ W.ι = gp → x ≫ h = ξ) :
    ∃ e : Z ⟶ G, e ≫ q = 𝟙 Z ∧ gp ≫ e = ξ := by
  choose W h hz hq hξ using H
  have hd : IsDominant gp := ⟨by
    rw [DenseRange, hgp, dense_iff_closure_eq]
    exact genericPoint_spec Z⟩
  have hx : ∀ z, ∃ x : Sp K ⟶ (W z).toScheme, x ≫ (W z).ι = gp := fun z =>
    have : Nonempty (W z).toScheme := ⟨⟨z, hz z⟩⟩
    exists_lift gp hgp _
  choose x hx using hx
  have hW : TopologicalSpace.IsOpenCover W :=
    top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hz z⟩
  let 𝒰 := Z.openCoverOfIsOpenCover W hW
  have hc : ∀ a b, pullback.fst (W a).ι (W b).ι ≫ h a = pullback.snd (W a).ι (W b).ι ≫ h b := by
    intro a b
    let m : Sp K ⟶ pullback (W a).ι (W b).ι := pullback.lift (x a) (x b) ((hx a).trans (hx b).symm)
    have e : m ≫ pullback.fst _ _ ≫ (W a).ι = gp := by rw [pullback.lift_fst_assoc, hx]
    have : IsDominant (m ≫ pullback.fst _ _ ≫ (W a).ι) := e ▸ hd
    have : IsDominant m := .of_comp_of_isOpenImmersion m (pullback.fst _ _ ≫ (W a).ι)
    have : IsReduced (pullback (W a).ι (W b).ι) := isReduced_of_isOpenImmersion (pullback.fst _ _ ≫ (W a).ι)
    refine ext_of_isDominant_of_isSeparated q ?_ m ?_
    · rw [Category.assoc, Category.assoc, hq, hq, pullback.condition]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hξ _ _ (hx a), hξ _ _ (hx b)]
  have he : ∀ a, (W a).ι ≫ 𝒰.glueMorphisms h hc = h a := fun a => 𝒰.ι_glueMorphisms h hc a
  refine ⟨𝒰.glueMorphisms h hc, 𝒰.hom_ext _ _ fun (a : Z) => ?_, ?_⟩
  · change (W a).ι ≫ _ = (W a).ι ≫ _
    rw [← Category.assoc, he, hq, Category.comp_id]
  · rw [← hx (genericPoint Z), Category.assoc, he, hξ _ _ (hx _)]

/- English proof (translation)
Rewrite using `[eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq, ← pullback.condition_assoc]`. Conclude with `(pullback.lift_fst _ _ _).trans (by simp)`.
-/
theorem eSec_fst {B B' : Scheme.{0}} (u : B' ⟶ B) (A : Over B) [GrpObj A] :
    eSec ((Over.pullback u).obj A) ≫ pullback.fst A.hom u = u ≫ eSec A := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    ← pullback.condition_assoc]
  exact (pullback.lift_fst _ _ _).trans (by simp)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

/- English proof (translation)
Substitute `h` using the available equality. Unfold `ThetaSys.proj`. Rewrite using `[finsum_unique, S.ρ_one _ (by rw [AddSubgroup.mem_bot.1 (Subtype.prop _), smul_zero])]`. Simplify using the standard rewrite rules.
-/
theorem proj_zero_of_eq_bot {T : AddSubgroup S.Gam} (h : T = ⊥) : S.proj T 0 = 1 := by
  subst h
  unfold ThetaSys.proj
  rw [finsum_unique, S.ρ_one _ (by rw [AddSubgroup.mem_bot.1 (Subtype.prop _), smul_zero])]
  simp

/- English proof (translation)
Set `y' : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left` to `pullback.lift (f := (baseOver (Sp S.R)).hom) (g := ρ.P.A.hom) (y ≫ ρ.P.A.hom) y (Category.comp_id _)`. Establish `hM : (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))).IsLB` using `LB.isLB_linComb ρ.P.isLB _ _`. Take `⟨v, hv⟩` from `CrdCalc.crd_exists hM ρ.s y'`. Establish `hm : y' (IsLocalRing.closedPoint K) ∈ ⨆ i ∈ (Set.univ : Set S.J), nonzeroLocus (ρ.s i)`. Rewrite using `[(ThetaSys.Real.immBy_basis hL o Ω S ρ).1]`.

Discharge the goal by the elementary cases of `trivial`. Simplify using `only [TopologicalSpace.Opens.mem_iSup] at hm`. Take `⟨i, -, hi⟩` from `hm`. Conclude with `⟨v, i, ⟨y', pullback.lift_snd _ _ _, hv⟩, ((CrdCalc.crd_isUnit_iff i hv).2 ((CrdCalc.top_le_iff y' _).2 hi)).ne_zero⟩`.
-/
theorem exists_crd_ne_zero [ArithBase o Ω] (hL : GlobalTheory.UT.LL) (ρ : S.Real) {K : Type} [Field K]
    (y : Sp K ⟶ ρ.P.A.left) : ∃ v i, ρ.Crd y v ∧ v i ≠ 0 := by
  let y' : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left :=
    pullback.lift (f := (baseOver (Sp S.R)).hom) (g := ρ.P.A.hom) (y ≫ ρ.P.A.hom) y (Category.comp_id _)
  have hM : (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))).IsLB := LB.isLB_linComb ρ.P.isLB _ _
  obtain ⟨v, hv⟩ := CrdCalc.crd_exists hM ρ.s y'
  have hm : y' (IsLocalRing.closedPoint K) ∈ ⨆ i ∈ (Set.univ : Set S.J), nonzeroLocus (ρ.s i) := by
    rw [(ThetaSys.Real.immBy_basis hL o Ω S ρ).1]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, -, hi⟩ := hm
  exact ⟨v, i, ⟨y', pullback.lift_snd _ _ _, hv⟩,
    ((CrdCalc.crd_isUnit_iff i hv).2 ((CrdCalc.top_le_iff y' _).2 hi)).ne_zero⟩

variable {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J}

/- English proof (translation)
Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Take `⟨K, _, x, rfl⟩ : ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ pullback ρ.P.A.hom Q.u₀), x (IsLocalRing.closedPoint K) = w` from `⟨_, inferInstance, Scheme.fromSpecResidueField _ w, Scheme.fromSpecResidueField_apply w _⟩`. Take `⟨v, i, hv, hi⟩` from `exists_crd_ne_zero hL ρ (x ≫ pullback.fst _ _)`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective ((x ≫ Q.a₀) ≫ Q.P.hom ≫ M.s)`.

Establish `hz : ∀ s, ((x ≫ Q.a₀) ≫ Q.P.hom) s ∈ U₀` using `fun s => by`. Rewrite using `[Category.assoc, Q.cart.w, ← Category.assoc]`. Conclude with `((x ≫ pullback.snd _ _) s).2`. Establish `key` using `(OpenPart.le_preimage_G_iff o Ω S ρ M U₀ EE hB Q K (x ≫ Q.a₀) _ ψ.hom v Set.range_unique (Or.inr (hz _)) hψ.symm (Q.crd K x v hv)).2 ⟨i, by`. Rewrite using `[proj_zero_of_eq_bot (hB.gen _ (hz _)), Finset.sum_eq_single i (fun j _ hj => by rw [Matrix.one_apply_ne hj, map_zero, zero_mul]) (by simp)]`.

Simplify using `using hi⟩`. Conclude with `key (Set.mem_univ (IsLocalRing.closedPoint K))`.
-/
theorem range_subset [ArithBase o Ω] (hL : GlobalTheory.UT.LL) (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) :
    Set.range Q.a₀ ⊆ Set.range Q.G.ι := by
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Opens.range_ι]
  obtain ⟨K, _, x, rfl⟩ : ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ pullback ρ.P.A.hom Q.u₀),
      x (IsLocalRing.closedPoint K) = w :=
    ⟨_, inferInstance, Scheme.fromSpecResidueField _ w, Scheme.fromSpecResidueField_apply w _⟩
  obtain ⟨v, i, hv, hi⟩ := exists_crd_ne_zero hL ρ (x ≫ pullback.fst _ _)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective ((x ≫ Q.a₀) ≫ Q.P.hom ≫ M.s)
  have hz : ∀ s, ((x ≫ Q.a₀) ≫ Q.P.hom) s ∈ U₀ := fun s => by
    rw [Category.assoc, Q.cart.w, ← Category.assoc]
    exact ((x ≫ pullback.snd _ _) s).2
  have key := (OpenPart.le_preimage_G_iff o Ω S ρ M U₀ EE hB Q K (x ≫ Q.a₀) _ ψ.hom v
    Set.range_unique (Or.inr (hz _)) hψ.symm (Q.crd K x v hv)).2 ⟨i, by
      rw [proj_zero_of_eq_bot (hB.gen _ (hz _)),
        Finset.sum_eq_single i (fun j _ hj => by rw [Matrix.one_apply_ne hj, map_zero, zero_mul]) (by simp)]
      simpa using hi⟩
  exact key (Set.mem_univ (IsLocalRing.closedPoint K))

/- English proof (translation)
Introduce `hL o Ω _ _ _ _ S ρ M U₀ EE hB Q`. Use `ArithBase.char (o := o) (Ω := Ω)` as an intermediate fact. Use `M.sep` as an intermediate fact. Use `M.lft` as an intermediate fact. Use `M.qc` as an intermediate fact.

Use `Q.proper` as an intermediate fact. Establish `: LocallyOfFiniteType (spMap (algebraMap ℤ o))` using `(HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 (ArithBase.ft (o := o) (Ω := Ω)))`. Establish `h0 : ρ.pt 0 = 1`. Use `ρ.pt_add 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`.

Conclude with `left_eq_mul.1 this`. Establish `h1 : (ρ.pt 0).left = eSec ρ.P.A`. Establish `e : toUnit (baseOver (Sp S.R)) = 𝟙 (𝟙_ (Over (Sp S.R)))` using `toUnit_unique _ _`. Rewrite using `[h0, Hom.one_def, e]`. Conclude with `congrArg CommaMorphism.left (Category.id_comp _)`.

Set `a : pullback ρ.P.A.hom Q.u₀ ⟶ Q.G.toScheme` to `IsOpenImmersion.lift Q.G.ι Q.a₀ (range_subset hL hB Q)`. Establish `ha : a ≫ Q.G.ι = Q.a₀` using `IsOpenImmersion.lift_fac _ _ _`. Set `ε : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀` to `eSec ((Over.pullback Q.u₀).obj ρ.P.A)`. Establish `hε₁ : ε ≫ pullback.fst _ _ = Q.u₀ ≫ eSec ρ.P.A` using `eSec_fst Q.u₀ ρ.P.A`. Establish `hε₂ : ε ≫ pullback.snd _ _ = 𝟙 _` using `Over.w η[(Over.pullback Q.u₀).obj ρ.P.A]`.

Establish `: Nonempty U₀.toScheme` using `hB.ov.ne.to_subtype`. Take `⟨t, ht⟩` from `exists_lift M.pt M.gen U₀.ι`. Take `⟨e, he, he'⟩` from `exists_section_of_local M.pt M.gen (Q.G.ι ≫ Q.P.hom) (t ≫ ε ≫ a) fun z => by`. Take `⟨W, h, hz, hh, H⟩` from `GlobalTheory.T.exists_section_extending_torsionPoints_support hL o Ω S ρ M U₀ EE hB Q z 0 (zero_mem _)`. Use `⟨W, h, hz, hh, fun x hx => ?_⟩` and prove the remaining obligations.

Rewrite using `[← cancel_mono Q.G.ι, Category.assoc, H Ω x (t ≫ ε) ?_ ?_]`. Simplify using `only [Category.assoc, ha]`. Rewrite using `[Category.assoc, reassoc_of% hε₂, hx, ht]`. Rewrite using `[Category.assoc, Category.assoc, reassoc_of% hε₂, hε₁, h1]`. Establish `: IsDominant (t ≫ U₀.ι)` using `ht ▸ M.isDominant_pt`.

Establish `: IsDominant t` using `.of_comp_of_isOpenImmersion t U₀.ι`. Use `⟨{ π := M.s ≫ spMap (algebraMap ℤ o) flat := flat_of_charZero M.pt M.gen _ lft := inferInstance qc := inferInstance sep := inferInstance normal := hB.ov.normal ne := hB.ov.ne ab := TLinPf.isAb_pullback _ _ ρ.P.isAb dim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_i …` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `U₀.ι ≫ e = ε ≫ a`. Use `ext_of_isDominant_of_isSeparated (Q.G.ι ≫ Q.P.hom) ?_ t ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, he, Category.assoc, reassoc_of% ha, Q.cart.w, reassoc_of% hε₂, Category.comp_id]`.

Rewrite using `[← Category.assoc, ht, he']`.
-/
theorem nonempty_ext : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), Nonempty Q.Ext := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q
  have := ArithBase.char (o := o) (Ω := Ω)
  have := M.sep
  have := M.lft
  have := M.qc
  have := Q.proper
  have : LocallyOfFiniteType (spMap (algebraMap ℤ o)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
      (RingHom.finiteType_algebraMap.2 (ArithBase.ft (o := o) (Ω := Ω)))
  have h0 : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have h1 : (ρ.pt 0).left = eSec ρ.P.A := by
    have e : toUnit (baseOver (Sp S.R)) = 𝟙 (𝟙_ (Over (Sp S.R))) := toUnit_unique _ _
    rw [h0, Hom.one_def, e]
    exact congrArg CommaMorphism.left (Category.id_comp _)
  let a : pullback ρ.P.A.hom Q.u₀ ⟶ Q.G.toScheme := IsOpenImmersion.lift Q.G.ι Q.a₀ (range_subset hL hB Q)
  have ha : a ≫ Q.G.ι = Q.a₀ := IsOpenImmersion.lift_fac _ _ _
  let ε : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀ := eSec ((Over.pullback Q.u₀).obj ρ.P.A)
  have hε₁ : ε ≫ pullback.fst _ _ = Q.u₀ ≫ eSec ρ.P.A := eSec_fst Q.u₀ ρ.P.A
  have hε₂ : ε ≫ pullback.snd _ _ = 𝟙 _ := Over.w η[(Over.pullback Q.u₀).obj ρ.P.A]
  have : Nonempty U₀.toScheme := hB.ov.ne.to_subtype
  obtain ⟨t, ht⟩ := exists_lift M.pt M.gen U₀.ι
  obtain ⟨e, he, he'⟩ := exists_section_of_local M.pt M.gen (Q.G.ι ≫ Q.P.hom) (t ≫ ε ≫ a) fun z => by
    obtain ⟨W, h, hz, hh, H⟩ := GlobalTheory.T.exists_section_extending_torsionPoints_support hL o Ω S ρ M U₀ EE hB Q z 0 (zero_mem _)
    refine ⟨W, h, hz, hh, fun x hx => ?_⟩
    rw [← cancel_mono Q.G.ι, Category.assoc, H Ω x (t ≫ ε) ?_ ?_]
    · simp only [Category.assoc, ha]
    · rw [Category.assoc, reassoc_of% hε₂, hx, ht]
    · rw [Category.assoc, Category.assoc, reassoc_of% hε₂, hε₁, h1]
  have : IsDominant (t ≫ U₀.ι) := ht ▸ M.isDominant_pt
  have : IsDominant t := .of_comp_of_isOpenImmersion t U₀.ι
  refine ⟨{
    π := M.s ≫ spMap (algebraMap ℤ o)
    flat := flat_of_charZero M.pt M.gen _
    lft := inferInstance
    qc := inferInstance
    sep := inferInstance
    normal := hB.ov.normal
    ne := hB.ov.ne
    ab := TLinPf.isAb_pullback _ _ ρ.P.isAb
    dim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _)
      (ρ.g_eq ▸ ρ.P.smoothDim)
    a := a
    a_eq := ha
    e := e
    e_sec := he
    e_zero := ?_ }⟩
  change U₀.ι ≫ e = ε ≫ a
  refine ext_of_isDominant_of_isSeparated (Q.G.ι ≫ Q.P.hom) ?_ t ?_
  · rw [Category.assoc, he, Category.assoc, reassoc_of% ha, Q.cart.w, reassoc_of% hε₂, Category.comp_id]
  · rw [← Category.assoc, ht, he']

end GlobalTheory.ZH.ClosureLifting
end
