import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.TorusKernelSpreading

/- English proof (translation)
Rewrite using `[Hom.one_def, Over.comp_left]`. Use `congr 1`.
-/
theorem one_left {S : Scheme.{0}} (G : Over S) [GrpObj G] {Y : Scheme.{0}} (a : Y ⟶ S) :
    (1 : Over.mk a ⟶ G).left = a ≫ (η[G]).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

/- English proof (translation)
The claim follows from `Over.w η[G]`.
-/
theorem unit_w {S : Scheme.{0}} (G : Over S) [GrpObj G] : (η[G]).left ≫ G.hom = 𝟙 S := Over.w η[G]

noncomputable def pr (S : Scheme.{0}) (X : Type) [AddCommGroup X] :
    (splitTorus S X).left ⟶ Spec (torusRing ZU X) :=
  pullback.fst (splitTorusAff ZU X).hom (toZ S)

noncomputable def cv {S : Scheme.{0}} {X : Type} [AddCommGroup X] {A : Type} [CommRing A]
    (f : Sp A ⟶ (splitTorus S X).left) : AddMonoidAlgebra (ULift.{0} ℤ) X →+* A :=
  (Spec.preimage (f ≫ pr S X)).hom

/- English proof (translation)
Establish `: Spec.preimage ((spMap k ≫ f) ≫ pr S X) = Spec.preimage (f ≫ pr S X) ≫ CommRingCat.ofHom k`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Category.assoc]`. Conclude with `congrArg CommRingCat.Hom.hom this`.
-/
theorem cv_comp {S : Scheme.{0}} {X : Type} [AddCommGroup X] {A B : Type} [CommRing A] [CommRing B]
    (k : A →+* B) (f : Sp A ⟶ (splitTorus S X).left) : cv (spMap k ≫ f) = k.comp (cv f) := by
  have : Spec.preimage ((spMap k ≫ f) ≫ pr S X) = Spec.preimage (f ≫ pr S X) ≫ CommRingCat.ofHom k := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Category.assoc]
  exact congrArg CommRingCat.Hom.hom this

/- English proof (translation)
Establish `hmul : ∀ x y : X, (AddMonoidAlgebra.single (x + y) 1 : AddMonoidAlgebra (ULift.{0} ℤ) X) = AddMonoidAlgebra.single x 1 * AddMonoidAlgebra.single y 1`. Introduce `x y`. Rewrite using `[AddMonoidAlgebra.single_mul_single, _root_.one_mul]`. Establish `h0 : (AddMonoidAlgebra.single (0 : X) 1 : AddMonoidAlgebra (ULift.{0} ℤ) X) = 1` using `rfl`. Establish `hall : ∀ x : X, cv f (AddMonoidAlgebra.single x 1) = cv g (AddMonoidAlgebra.single x 1)`.

Introduce `x`. Establish `hx : x ∈ AddSubgroup.closure s`. Rewrite using `[← Submodule.span_int_eq_addSubgroupClosure, hs]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hx using AddSubgroup.closure_induction with`.

Consider the case `mem x hx => exact h x hx`. Consider the case `zero => rw [h0, map_one, map_one]`. Consider the case `add x y _ _ hx hy => rw [hmul, map_mul, map_mul, hx, hy]`. Consider the case `neg x _ hx`. Establish `e1 : cv f (AddMonoidAlgebra.single (-x) 1) * cv f (AddMonoidAlgebra.single x 1) = 1`.

Rewrite using `[← map_mul, ← hmul, neg_add_cancel, h0, map_one]`. Establish `e2 : cv g (AddMonoidAlgebra.single x 1) * cv g (AddMonoidAlgebra.single (-x) 1) = 1`. Rewrite using `[← map_mul, ← hmul, add_neg_cancel, h0, map_one]`. Rewrite `e1` using `[hx]`. Conclude with `left_inv_eq_right_inv e1 e2`.

Establish `hcv : cv f = cv g`. Use `AddMonoidAlgebra.ringHom_ext (fun r => ?_) hall` and prove the remaining obligations. Establish `: (cv f).comp AddMonoidAlgebra.singleZeroRingHom = (cv g).comp AddMonoidAlgebra.singleZeroRingHom`. Establish `h2 : ((cv f).comp AddMonoidAlgebra.singleZeroRingHom).comp (ULift.ringEquiv.{0, 0} (R` using `ℤ)).symm.toRingHom = ((cv g).comp AddMonoidAlgebra.singleZeroRingHom).comp (ULift.ringEquiv.{0, 0} (R := ℤ)).symm.toRingHom := RingHom.ext_int _ _`. Use extensionality with `z`.

Conclude with `RingHom.congr_fun h2 z.down`. Conclude with `RingHom.congr_fun this r`. Establish `hp : f ≫ pr S X = g ≫ pr S X`. Establish `: Spec.preimage (f ≫ pr S X) = Spec.preimage (g ≫ pr S X)` using `CommRingCat.hom_ext hcv`. Rewrite using `[← Spec.map_preimage (f ≫ pr S X), this, Spec.map_preimage]`.

Conclude with `pullback.hom_ext hp hw`.
-/
theorem ext_of_span {S : Scheme.{0}} {X : Type} [AddCommGroup X] {A : Type} [CommRing A]
    (f g : Sp A ⟶ (splitTorus S X).left) (hw : f ≫ (splitTorus S X).hom = g ≫ (splitTorus S X).hom)
    (s : Set X) (hs : Submodule.span ℤ s = ⊤)
    (h : ∀ x ∈ s, cv f (AddMonoidAlgebra.single x 1) = cv g (AddMonoidAlgebra.single x 1)) : f = g := by
  have hmul : ∀ x y : X, (AddMonoidAlgebra.single (x + y) 1 : AddMonoidAlgebra (ULift.{0} ℤ) X) =
      AddMonoidAlgebra.single x 1 * AddMonoidAlgebra.single y 1 := by
    intro x y
    rw [AddMonoidAlgebra.single_mul_single, _root_.one_mul]
  have h0 : (AddMonoidAlgebra.single (0 : X) 1 : AddMonoidAlgebra (ULift.{0} ℤ) X) = 1 := rfl
  have hall : ∀ x : X, cv f (AddMonoidAlgebra.single x 1) = cv g (AddMonoidAlgebra.single x 1) := by
    intro x
    have hx : x ∈ AddSubgroup.closure s := by
      rw [← Submodule.span_int_eq_addSubgroupClosure, hs]; trivial
    induction hx using AddSubgroup.closure_induction with
    | mem x hx => exact h x hx
    | zero => rw [h0, map_one, map_one]
    | add x y _ _ hx hy => rw [hmul, map_mul, map_mul, hx, hy]
    | neg x _ hx =>
      have e1 : cv f (AddMonoidAlgebra.single (-x) 1) * cv f (AddMonoidAlgebra.single x 1) = 1 := by
        rw [← map_mul, ← hmul, neg_add_cancel, h0, map_one]
      have e2 : cv g (AddMonoidAlgebra.single x 1) * cv g (AddMonoidAlgebra.single (-x) 1) = 1 := by
        rw [← map_mul, ← hmul, add_neg_cancel, h0, map_one]
      rw [hx] at e1
      exact left_inv_eq_right_inv e1 e2
  have hcv : cv f = cv g := by
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) hall
    have : (cv f).comp AddMonoidAlgebra.singleZeroRingHom = (cv g).comp AddMonoidAlgebra.singleZeroRingHom := by
      have h2 : ((cv f).comp AddMonoidAlgebra.singleZeroRingHom).comp (ULift.ringEquiv.{0, 0} (R := ℤ)).symm.toRingHom =
          ((cv g).comp AddMonoidAlgebra.singleZeroRingHom).comp (ULift.ringEquiv.{0, 0} (R := ℤ)).symm.toRingHom :=
        RingHom.ext_int _ _
      ext z
      exact RingHom.congr_fun h2 z.down
    exact RingHom.congr_fun this r
  have hp : f ≫ pr S X = g ≫ pr S X := by
    have : Spec.preimage (f ≫ pr S X) = Spec.preimage (g ≫ pr S X) := CommRingCat.hom_ext hcv
    rw [← Spec.map_preimage (f ≫ pr S X), this, Spec.map_preimage]
  exact pullback.hom_ext hp hw

/- English proof (translation)
The claim follows from `isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g) h`.
-/
theorem aff_snd {P Q T : Scheme.{0}} (f : P ⟶ T) (g : Q ⟶ T) (h : IsAffineHom f) : IsAffineHom (pullback.snd f g) :=
  isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g) h

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem cl_id (S : Scheme.{0}) : IsClosedImmersion (𝟙 S) := inferInstance

/- English proof (translation)
Establish `hcl : IsClosedImmersion (η[G]).left`. Establish `: IsClosedImmersion ((η[G]).left ≫ G.hom)`. Rewrite using `[unit_w]`. Conclude with `cl_id S`. Conclude with `IsClosedImmersion.of_comp _ G.hom`.

Establish `haT : IsAffineHom (splitTorus S X).hom`. Establish `: IsAffine (splitTorusAff ZU X).left` using `inferInstanceAs (IsAffine (Spec (torusRing ZU X)))`. Establish `: IsAffineHom (splitTorusAff ZU X).hom` using `inferInstance`. Conclude with `aff_snd _ _ this`. Establish `hq : pullback.snd u.left (η[G]).left = pullback.fst u.left (η[G]).left ≫ (splitTorus S X).hom`.

Rewrite using `[← Over.w u, ← Category.assoc, pullback.condition, Category.assoc, unit_w]`. Conclude with `(Category.comp_id _).symm`. Establish `haq : IsAffineHom (pullback.snd u.left (η[G]).left)` using `by rw [hq]; infer_instance`. Set `e : Sp R ⟶ G.left` to `w ≫ (η[G]).left`. Establish `hK : IsAffine (pullback u.left e)`.

Establish `: IsAffine (pullback (pullback.snd u.left (η[G]).left) w)` using `inferInstance`. Conclude with `.of_isIso (pullbackLeftPullbackSndIso u.left (η[G]).left w).inv`. Set `K` to `pullback u.left e`. Set `ψ : CommRingCat.of R ⟶ Γ(K, ⊤)` to `Spec.preimage (K.isoSpec.inv ≫ pullback.snd u.left e)`. Establish `hψ : spMap ψ.hom = K.isoSpec.inv ≫ pullback.snd u.left e` using `Spec.map_preimage _`.

Establish `hu : (K.isoSpec.inv ≫ pullback.fst u.left e) ≫ u.left = spMap ψ.hom ≫ e`. Rewrite using `[hψ, Category.assoc, Category.assoc, pullback.condition]`. Use `⟨Γ(K, ⊤), inferInstance, ψ.hom, K.isoSpec.inv ≫ pullback.fst u.left e, ?_, hu, ?_⟩` and prove the remaining obligations. Rewrite using `[← Over.w u, ← Category.assoc, hu]`. Simplify using `only [e, Category.assoc, unit_w, Category.comp_id]`.

Introduce `A _ h t ht`. Set `l : Sp A ⟶ K` to `pullback.lift t (spMap h) ht`. Set `k : Γ(K, ⊤) ⟶ CommRingCat.of A` to `Spec.preimage (l ≫ K.isoSpec.hom)`. Establish `hk : spMap k.hom = l ≫ K.isoSpec.hom` using `Spec.map_preimage _`. Use `⟨k.hom, ?_, ?_⟩` and prove the remaining obligations.

Establish `: ψ ≫ k = CommRingCat.ofHom h`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp]`. Express the relevant statement in the definitionally equal form `spMap k.hom ≫ spMap ψ.hom = _`. Rewrite using `[hk, hψ, Category.assoc, Iso.hom_inv_id_assoc]`.

Conclude with `pullback.lift_snd _ _ _`. Conclude with `congrArg CommRingCat.Hom.hom this`. Rewrite using `[hk, Category.assoc, Iso.hom_inv_id_assoc]`. Conclude with `pullback.lift_fst _ _ _`.
-/
theorem exists_univ {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsSeparated G.hom] {X : Type} [AddCommGroup X]
    (u : splitTorus S X ⟶ G) {R : Type} [CommRing R] (w : Sp R ⟶ S) :
    ∃ (C : Type) (_ : CommRing C) (ψ : R →+* C) (t₀ : Sp C ⟶ (splitTorus S X).left),
      t₀ ≫ (splitTorus S X).hom = spMap ψ ≫ w ∧ t₀ ≫ u.left = spMap ψ ≫ w ≫ (η[G]).left ∧
      ∀ (A : Type) [CommRing A] (h : R →+* A) (t : Sp A ⟶ (splitTorus S X).left),
        t ≫ u.left = spMap h ≫ w ≫ (η[G]).left → ∃ k : C →+* A, k.comp ψ = h ∧ spMap k ≫ t₀ = t := by
  have hcl : IsClosedImmersion (η[G]).left := by
    have : IsClosedImmersion ((η[G]).left ≫ G.hom) := by
      rw [unit_w]; exact cl_id S
    exact IsClosedImmersion.of_comp _ G.hom
  have haT : IsAffineHom (splitTorus S X).hom := by
    have : IsAffine (splitTorusAff ZU X).left := inferInstanceAs (IsAffine (Spec (torusRing ZU X)))
    have : IsAffineHom (splitTorusAff ZU X).hom := inferInstance
    exact aff_snd _ _ this
  have hq : pullback.snd u.left (η[G]).left = pullback.fst u.left (η[G]).left ≫ (splitTorus S X).hom := by
    rw [← Over.w u, ← Category.assoc, pullback.condition, Category.assoc, unit_w]
    exact (Category.comp_id _).symm
  have haq : IsAffineHom (pullback.snd u.left (η[G]).left) := by rw [hq]; infer_instance
  let e : Sp R ⟶ G.left := w ≫ (η[G]).left
  have hK : IsAffine (pullback u.left e) := by
    have : IsAffine (pullback (pullback.snd u.left (η[G]).left) w) := inferInstance
    exact .of_isIso (pullbackLeftPullbackSndIso u.left (η[G]).left w).inv
  let K := pullback u.left e
  let ψ : CommRingCat.of R ⟶ Γ(K, ⊤) := Spec.preimage (K.isoSpec.inv ≫ pullback.snd u.left e)
  have hψ : spMap ψ.hom = K.isoSpec.inv ≫ pullback.snd u.left e := Spec.map_preimage _
  have hu : (K.isoSpec.inv ≫ pullback.fst u.left e) ≫ u.left = spMap ψ.hom ≫ e := by
    rw [hψ, Category.assoc, Category.assoc, pullback.condition]
  refine ⟨Γ(K, ⊤), inferInstance, ψ.hom, K.isoSpec.inv ≫ pullback.fst u.left e, ?_, hu, ?_⟩
  · rw [← Over.w u, ← Category.assoc, hu]
    simp only [e, Category.assoc, unit_w, Category.comp_id]
  · intro A _ h t ht
    let l : Sp A ⟶ K := pullback.lift t (spMap h) ht
    let k : Γ(K, ⊤) ⟶ CommRingCat.of A := Spec.preimage (l ≫ K.isoSpec.hom)
    have hk : spMap k.hom = l ≫ K.isoSpec.hom := Spec.map_preimage _
    refine ⟨k.hom, ?_, ?_⟩
    · have : ψ ≫ k = CommRingCat.ofHom h := by
        apply Spec.map_injective
        rw [Spec.map_comp]
        change spMap k.hom ≫ spMap ψ.hom = _
        rw [hk, hψ, Category.assoc, Iso.hom_inv_id_assoc]
        exact pullback.lift_snd _ _ _
      exact congrArg CommRingCat.Hom.hom this
    · rw [hk, Category.assoc, Iso.hom_inv_id_assoc]
      exact pullback.lift_fst _ _ _

/- English proof (translation)
Take `⟨e, rfl⟩` from `hj`. Use `functionField_isFractionRing_of_isAffineOpen Z W hW` as an intermediate fact. Set `g₀ : Z.functionField →+* A` to `IsLocalization.lift hm`. Establish `hg₀ : g₀.comp (algebraMap _ _) = m` using `IsLocalization.lift_comp hm`. Set `g : CommRingCat.of L ⟶ CommRingCat.of A` to `Spec.preimage (spMap g₀ ≫ e.inv)`.

Establish `hg : spMap g.hom = spMap g₀ ≫ e.inv` using `Spec.map_preimage _`. Use `⟨g.hom, ?_⟩` and prove the remaining obligations. Establish `hmem : genericPoint Z ∈ W` using `((genericPoint_spec Z).mem_open_set_iff W.isOpen).2 (by`. Take `⟨⟨x, hx⟩⟩` from `‹Nonempty W›`. Conclude with `⟨x, trivial, hx⟩)`.

Rewrite using `[hg, Category.assoc, Iso.inv_hom_id_assoc, ← hW.fromSpecStalk_eq_fromSpecStalk hmem, ← hg₀, IsAffineOpen.fromSpecStalk, ← Category.assoc]`. Use `congr 1`. Conclude with `(Spec.map_comp _ _).symm`.
-/
theorem exists_factor {Z : Scheme.{0}} [IsIntegral Z] {L : Type} [Field L] {j : Sp L ⟶ Z}
    (hj : GlobalTheory.IsGenericPointHom j) {W : Z.Opens} (hW : IsAffineOpen W) [Nonempty W] {A : Type} [CommRing A]
    (m : Γ(Z, W) →+* A) (hm : ∀ y : nonZeroDivisors Γ(Z, W), IsUnit (m y)) :
    ∃ g : L →+* A, spMap g ≫ j = spMap m ≫ hW.fromSpec := by
  obtain ⟨e, rfl⟩ := hj
  have := functionField_isFractionRing_of_isAffineOpen Z W hW
  let g₀ : Z.functionField →+* A := IsLocalization.lift hm
  have hg₀ : g₀.comp (algebraMap _ _) = m := IsLocalization.lift_comp hm
  let g : CommRingCat.of L ⟶ CommRingCat.of A := Spec.preimage (spMap g₀ ≫ e.inv)
  have hg : spMap g.hom = spMap g₀ ≫ e.inv := Spec.map_preimage _
  refine ⟨g.hom, ?_⟩
  have hmem : genericPoint Z ∈ W := ((genericPoint_spec Z).mem_open_set_iff W.isOpen).2 (by
    obtain ⟨⟨x, hx⟩⟩ := ‹Nonempty W›
    exact ⟨x, trivial, hx⟩)
  rw [hg, Category.assoc, Iso.inv_hom_id_assoc, ← hW.fromSpecStalk_eq_fromSpecStalk hmem, ← hg₀,
    IsAffineOpen.fromSpecStalk, ← Category.assoc]
  congr 1
  exact (Spec.map_comp _ _).symm

end PositivityTheory.Xgn.TorusKernelSpreading

open PositivityTheory.Xgn.TorusKernelSpreading in
/- English proof (translation)
Introduce `Z' _ G _ _ X _ _ _ u _ L' _ j hj H`. Take `⟨x₀⟩ : Nonempty Z'` from `inferInstance`. Take `⟨_, ⟨W, hW, rfl⟩, hx₀, -⟩` from `Z'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x₀) isOpen_univ`. Establish `: Nonempty W` using `⟨⟨x₀, hx₀⟩⟩`. Set `w : Sp Γ(Z', W) ⟶ Z'` to `hW.fromSpec`.

Establish `: IsOpenImmersion w` using `IsAffineOpen.isOpenImmersion_fromSpec hW`. Take `⟨C, _, ψ, t₀, ht₁, ht₂, huniv⟩` from `exists_univ G u w`. Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := ℤ) (M := X)`. Set `o : Sp C ⟶ (splitTorus Z' X).left` to `spMap ψ ≫ w ≫ (η[splitTorus Z' X]).left`. Set `M : Submonoid C` to `(nonZeroDivisors Γ(Z', W)).map ψ`.

Establish `hsp : ∀ {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D), spMap (g.comp f) = spMap g ≫ spMap f` using `fun f g => Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)`. Establish `hloc : spMap (algebraMap C (Localization M)) ≫ t₀ = spMap (algebraMap C (Localization M)) ≫ o`. Take `⟨g, hg⟩` from `exists_factor hj hW ((algebraMap C (Localization M)).comp ψ) (fun y => IsLocalization.map_units (Localization M) (⟨ψ y, y, y.2, rfl⟩ : M))`. Rewrite `hg` using `[hsp, Category.assoc]`. Establish `h1` using `H (Localization M) g (Over.homMk (spMap (algebraMap C (Localization M)) ≫ t₀) (by`.

Express the relevant statement in the definitionally equal form `(_ ≫ t₀) ≫ _ = spMap g ≫ j`. Rewrite using `[hg, Category.assoc, ht₁])) (by`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[one_left]`. Express the relevant statement in the definitionally equal form `(_ ≫ t₀) ≫ u.left = (spMap g ≫ j) ≫ _`.

Rewrite using `[hg]`. Simplify using `only [Category.assoc, ht₂, w])`. Establish `h2` using `congrArg (·.left) h1`. Simplify using `only [one_left, hg] at h2`. Simplify `h2` using `only [o, w, Category.assoc, Over.homMk_left]`.

Establish `hr : ∀ x : X, ∃ r : Γ(Z', W), r ≠ 0 ∧ ψ r * cv t₀ (AddMonoidAlgebra.single x 1) = ψ r * cv o (AddMonoidAlgebra.single x 1)`. Introduce `x`. Establish `h1` using `RingHom.congr_fun (congrArg cv hloc) (AddMonoidAlgebra.single x 1)`. Rewrite `h1` using `[cv_comp, cv_comp]`. Take `⟨⟨_, r, hr, rfl⟩, hc⟩` from `(IsLocalization.eq_iff_exists M (Localization M)).1 h1`.

Conclude with `⟨r, nonZeroDivisors.ne_zero hr, hc⟩`. Use `choose r hr0 hr using hr`. Set `p : Γ(Z', W)` to `∏ x ∈ s, r x`. Establish `hp : p ≠ 0` using `Finset.prod_ne_zero_iff.2 fun x _ => hr0 x`. Set `D : (Sp Γ(Z', W)).Opens` to `PrimeSpectrum.basicOpen p`.

Use `⟨w ''ᵁ D, ⟨w (⊥ : PrimeSpectrum Γ(Z', W)), (⊥ : PrimeSpectrum Γ(Z', W)), hp, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce `A _ a ha t ht`. Establish `hrange : Set.range a ⊆ Set.range w`. Introduce and unpack `_ ⟨y, rfl⟩`. Take `⟨z, -, hz⟩ : a y ∈ w ''ᵁ D` from `ha (Set.mem_univ y)`.

Conclude with `⟨z, hz⟩`. Set `l` to `IsOpenImmersion.lift w a hrange`. Establish `hl : l ≫ w = a` using `IsOpenImmersion.lift_fac _ _ _`. Set `h : Γ(Z', W) →+* A` to `(Spec.preimage l).hom`. Establish `hh : spMap h = l` using `Spec.map_preimage l`.

Establish `hunit : IsUnit (h p)`. Assume the negation of the conclusion as `hn`. Take `⟨m, hm, hmem⟩` from `exists_max_ideal_of_mem_nonunits hn`. Set `y : Sp A` to `(⟨m, hm.isPrime⟩ : PrimeSpectrum A)`. Take `⟨z, hzD, hz⟩ : a y ∈ w ''ᵁ D` from `ha (Set.mem_univ y)`.

Rewrite `hz` using `[← hl, Scheme.Hom.comp_apply]`. Establish `hz' : z = spMap h y` using `by rw [hh]; exact w.isOpenEmbedding.injective hz`. Substitute `hz'` using the available equality. Conclude with `hzD hmem`. Establish `ha' : a = spMap h ≫ w` using `by rw [hh, hl]`.

Establish `htu : t.left ≫ u.left = spMap h ≫ w ≫ (η[G]).left`. Use `congrArg (·.left) ht` as an intermediate fact. Simplify using `only [one_left, Over.comp_left] at this`. Rewrite using `[this, ← Category.assoc, ← ha']`. Take `⟨k, hk₁, hk₂⟩` from `huniv A h t.left htu`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Establish `ho : (1 : Over.mk a ⟶ splitTorus Z' X).left = spMap k ≫ o`. Rewrite using `[one_left, ha', ← hk₁, hsp]`. Simplify using `only [o, Category.assoc]`. Use `ext_of_span (A := A) _ _ ((Over.w t).trans (Over.w _).symm) s hs fun x hx => ?_` and prove the remaining obligations.

Establish `hux : IsUnit (k (ψ (r x)))`. Establish `: k (ψ (r x)) = h (r x)` using `RingHom.congr_fun hk₁ _`. Rewrite using `[this]`. Conclude with `isUnit_of_dvd_unit (map_dvd h (Finset.dvd_prod_of_mem r hx)) hunit`. Establish `e1` using `congrArg k (hr x)`.

Rewrite `e1` using `[map_mul, map_mul]`. Establish `e2` using `hux.mul_left_cancel e1`. Establish `e3 : cv (A` using `A) t.left = k.comp (cv t₀) := by rw [← cv_comp, hk₂]`. Establish `e4 : cv (A` using `A) (1 : Over.mk a ⟶ splitTorus Z' X).left = k.comp (cv o) := by rw [← cv_comp, ← ho]`. Rewrite using `[e3, e4]`.

Conclude with `e2`.
-/
theorem PositivityTheory.Xgn.torus_kernel_trivial_spreads_open : ∀ (Z' : Scheme.{0}) [IsIntegral Z'] (G : Over Z') [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus Z' X ⟶ G) [IsMonHom u] (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → (∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) → ∃ V : Z'.Opens, (V : Set Z').Nonempty ∧ ∀ (A : Type) [CommRing A] (a : Sp A ⟶ Z'), ⊤ ≤ a ⁻¹ᵁ V → ∀ t : Over.mk a ⟶ splitTorus Z' X, t ≫ u = 1 → t = 1 := by
  intro Z' _ G _ _ X _ _ _ u _ L' _ j hj H
  classical
  obtain ⟨x₀⟩ : Nonempty Z' := inferInstance
  obtain ⟨_, ⟨W, hW, rfl⟩, hx₀, -⟩ := Z'.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x₀) isOpen_univ
  have : Nonempty W := ⟨⟨x₀, hx₀⟩⟩
  let w : Sp Γ(Z', W) ⟶ Z' := hW.fromSpec
  have : IsOpenImmersion w := IsAffineOpen.isOpenImmersion_fromSpec hW
  obtain ⟨C, _, ψ, t₀, ht₁, ht₂, huniv⟩ := exists_univ G u w
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := X)
  let o : Sp C ⟶ (splitTorus Z' X).left := spMap ψ ≫ w ≫ (η[splitTorus Z' X]).left
  let M : Submonoid C := (nonZeroDivisors Γ(Z', W)).map ψ
  have hsp : ∀ {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D),
      spMap (g.comp f) = spMap g ≫ spMap f := fun f g => Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)
  have hloc : spMap (algebraMap C (Localization M)) ≫ t₀ = spMap (algebraMap C (Localization M)) ≫ o := by
    obtain ⟨g, hg⟩ := exists_factor hj hW ((algebraMap C (Localization M)).comp ψ)
      (fun y => IsLocalization.map_units (Localization M) (⟨ψ y, y, y.2, rfl⟩ : M))
    rw [hsp, Category.assoc] at hg
    have h1 := H (Localization M) g (Over.homMk (spMap (algebraMap C (Localization M)) ≫ t₀) (by
      change (_ ≫ t₀) ≫ _ = spMap g ≫ j
      rw [hg, Category.assoc, ht₁])) (by
      apply Over.OverMorphism.ext
      rw [one_left]
      change (_ ≫ t₀) ≫ u.left = (spMap g ≫ j) ≫ _
      rw [hg]
      simp only [Category.assoc, ht₂, w])
    have h2 := congrArg (·.left) h1
    simp only [one_left, hg] at h2
    simpa only [o, w, Category.assoc, Over.homMk_left] using h2
  have hr : ∀ x : X, ∃ r : Γ(Z', W), r ≠ 0 ∧
      ψ r * cv t₀ (AddMonoidAlgebra.single x 1) = ψ r * cv o (AddMonoidAlgebra.single x 1) := by
    intro x
    have h1 := RingHom.congr_fun (congrArg cv hloc) (AddMonoidAlgebra.single x 1)
    rw [cv_comp, cv_comp] at h1
    obtain ⟨⟨_, r, hr, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists M (Localization M)).1 h1
    exact ⟨r, nonZeroDivisors.ne_zero hr, hc⟩
  choose r hr0 hr using hr
  let p : Γ(Z', W) := ∏ x ∈ s, r x
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ => hr0 x
  let D : (Sp Γ(Z', W)).Opens := PrimeSpectrum.basicOpen p
  refine ⟨w ''ᵁ D, ⟨w (⊥ : PrimeSpectrum Γ(Z', W)), (⊥ : PrimeSpectrum Γ(Z', W)), hp, rfl⟩, ?_⟩
  intro A _ a ha t ht
  have hrange : Set.range a ⊆ Set.range w := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, -, hz⟩ : a y ∈ w ''ᵁ D := ha (Set.mem_univ y)
    exact ⟨z, hz⟩
  let l := IsOpenImmersion.lift w a hrange
  have hl : l ≫ w = a := IsOpenImmersion.lift_fac _ _ _
  let h : Γ(Z', W) →+* A := (Spec.preimage l).hom
  have hh : spMap h = l := Spec.map_preimage l
  have hunit : IsUnit (h p) := by
    by_contra hn
    obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hn
    let y : Sp A := (⟨m, hm.isPrime⟩ : PrimeSpectrum A)
    obtain ⟨z, hzD, hz⟩ : a y ∈ w ''ᵁ D := ha (Set.mem_univ y)
    rw [← hl, Scheme.Hom.comp_apply] at hz
    have hz' : z = spMap h y := by rw [hh]; exact w.isOpenEmbedding.injective hz
    subst hz'
    exact hzD hmem
  have ha' : a = spMap h ≫ w := by rw [hh, hl]
  have htu : t.left ≫ u.left = spMap h ≫ w ≫ (η[G]).left := by
    have := congrArg (·.left) ht
    simp only [one_left, Over.comp_left] at this
    rw [this, ← Category.assoc, ← ha']
  obtain ⟨k, hk₁, hk₂⟩ := huniv A h t.left htu
  apply Over.OverMorphism.ext
  have ho : (1 : Over.mk a ⟶ splitTorus Z' X).left = spMap k ≫ o := by
    rw [one_left, ha', ← hk₁, hsp]
    simp only [o, Category.assoc]
  refine ext_of_span (A := A) _ _ ((Over.w t).trans (Over.w _).symm) s hs fun x hx => ?_
  have hux : IsUnit (k (ψ (r x))) := by
    have : k (ψ (r x)) = h (r x) := RingHom.congr_fun hk₁ _
    rw [this]
    exact isUnit_of_dvd_unit (map_dvd h (Finset.dvd_prod_of_mem r hx)) hunit
  have e1 := congrArg k (hr x)
  rw [map_mul, map_mul] at e1
  have e2 := hux.mul_left_cancel e1
  have e3 : cv (A := A) t.left = k.comp (cv t₀) := by rw [← cv_comp, hk₂]
  have e4 : cv (A := A) (1 : Over.mk a ⟶ splitTorus Z' X).left = k.comp (cv o) := by rw [← cv_comp, ← ho]
  rw [e3, e4]
  exact e2
