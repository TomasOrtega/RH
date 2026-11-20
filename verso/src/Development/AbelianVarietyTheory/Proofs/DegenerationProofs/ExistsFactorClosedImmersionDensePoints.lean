import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.JetGlue
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueIsRatio
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValHomEq
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
namespace GlobalTheory.ZH.ToImm
open GlobalTheory.ZH.CrdCalc GlobalTheory.ZH.ImmSep

/- English proof (translation)
The claim follows from `ReciprocityTheory.ChartRestriction.G.TB.JGPf.ext_of_fromSpecStalk f g fun t => @h (T.presheaf.stalk t) _ (T.toLocallyRingedSpace.isLocalRing t) (T.fromSpecStalk t)`.
-/
theorem ext_local {T X : Scheme.{0}} (f g : T ⟶ X)
    (h : ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ T), y ≫ f = y ≫ g) : f = g :=
  ReciprocityTheory.ChartRestriction.G.TB.JGPf.ext_of_fromSpecStalk f g fun t =>
    @h (T.presheaf.stalk t) _ (T.toLocallyRingedSpace.isLocalRing t) (T.fromSpecStalk t)

/- English proof (translation)
Use `⟨V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec, fun R _ y h => ?_⟩` and prove the remaining obligations. Establish `h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U` using `hU.fromSpec_preimage_self.ge`. Establish `h' : ⊤ ≤ (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) ⁻¹ᵁ U` using `fun z _ => h0 (Set.mem_univ ((y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)) z))`. Use `⟨h', fun f => ?_⟩` and prove the remaining obligations. Establish `h1 : hU.fromSpec.appLE U ⊤ h0 = (Scheme.ΓSpecIso _).inv`.

Rewrite using `[Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]`. Conclude with `Category.comp_id _`. Establish `h2 : (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h' = hU.fromSpec.appLE U ⊤ h0 ≫ (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop` using `(Scheme.Hom.appLE_comp_appLE (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)) hU.fromSpec U ⊤ ⊤ h0 le_rfl).symm`. Establish `h3 : (y ≫ V.ι).appLE V ⊤ h = V.topIso.inv ≫ y.appTop`. Rewrite using `[← Scheme.Hom.appLE_comp_appLE y V.ι V ⊤ ⊤ (fun x _ => x.2) le_rfl]`.

Use `erw [Scheme.Opens.ι_appLE]`. Simplify using `only [Scheme.Opens.topIso_inv]`. Use `congr 1`. Establish `h4 : (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h' = CommRingCat.ofHom φ ≫ (y ≫ V.ι).appLE V ⊤ h`. Rewrite using `[h2, h1, h3, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop]`.

Simplify using `only [Category.assoc]`. Rewrite using `[Scheme.ΓSpecIso_naturality_assoc]`. Conclude with `Iso.inv_hom_id_assoc _ _`. Unfold `valHom`. Rewrite using `[h4]`.

Both sides reduce to the same expression.
-/
theorem exists_hom_of_ringHom {X Y : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (V : Y.Opens)
    (φ : Γ(X, U) →+* Γ(Y, V)) : ∃ g : V.toScheme ⟶ X, ∀ (R : Type) [CommRing R] (y : Sp R ⟶ V.toScheme)
      (h : ⊤ ≤ (y ≫ V.ι) ⁻¹ᵁ V), ∃ h' : ⊤ ≤ (y ≫ g) ⁻¹ᵁ U,
        ∀ f, valHom (y ≫ g) U h' f = valHom (y ≫ V.ι) V h (φ f) := by
  refine ⟨V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec, fun R _ y h => ?_⟩
  have h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have h' : ⊤ ≤ (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) ⁻¹ᵁ U :=
    fun z _ => h0 (Set.mem_univ ((y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)) z))
  refine ⟨h', fun f => ?_⟩
  have h1 : hU.fromSpec.appLE U ⊤ h0 = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact Category.comp_id _
  have h2 : (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h' =
      hU.fromSpec.appLE U ⊤ h0 ≫ (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop :=
    (Scheme.Hom.appLE_comp_appLE (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)) hU.fromSpec
      U ⊤ ⊤ h0 le_rfl).symm
  have h3 : (y ≫ V.ι).appLE V ⊤ h = V.topIso.inv ≫ y.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE y V.ι V ⊤ ⊤ (fun x _ => x.2) le_rfl]
    erw [Scheme.Opens.ι_appLE]
    simp only [Scheme.Opens.topIso_inv]
    congr 1
  have h4 : (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h' =
      CommRingCat.ofHom φ ≫ (y ≫ V.ι).appLE V ⊤ h := by
    rw [h2, h1, h3, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop]
    simp only [Category.assoc]
    rw [Scheme.ΓSpecIso_naturality_assoc]
    exact Iso.inv_hom_id_assoc _ _
  unfold valHom
  rw [h4]
  rfl

def constHom {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) : k →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem constHom_apply {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) (a : k) :
    constHom p U a = constFn p U a := rfl

/- English proof (translation)
Rewrite using `[← basicOpen_eq_bot_iff, eq_bot_iff]`. Introduce `z hz`. Take `⟨w, hw, hw'⟩` from `hd.inter_open_nonempty _ (Y.basicOpen f).isOpen ⟨z, hz⟩`. Take `⟨a, t, rfl⟩` from `Set.mem_iUnion.1 hw'`. Establish `h1 : ⊤ ≤ x a ⁻¹ᵁ Y.basicOpen f` using `fun t' _ => by`.

Establish `: t' = t` using `Subsingleton.elim (α := PrimeSpectrum K) _ _`. Substitute `this` using the available equality. Conclude with `hw`. Establish `h2 : ⊤ ≤ x a ⁻¹ᵁ V` using `h1.trans ((x a).preimage_mono (Y.basicOpen_le f))`. Use `(isUnit_valR_iff (x a) V h2 f).2 h1` as an intermediate fact.

Rewrite `this` using `[valR_eq _ _ h2, hf a h2]`. Conclude with `(not_isUnit_zero this).elim`.
-/
theorem eq_zero_of_dense {Y : Scheme.{0}} [IsReduced Y] {K : Type} [Field K] {A : Type}
    (x : A → (Sp K ⟶ Y)) (hd : Dense (⋃ a, Set.range (x a))) (V : Y.Opens) (f : Γ(Y, V))
    (hf : ∀ a (h : ⊤ ≤ x a ⁻¹ᵁ V), valHom (x a) V h f = 0) : f = 0 := by
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro z hz
  obtain ⟨w, hw, hw'⟩ := hd.inter_open_nonempty _ (Y.basicOpen f).isOpen ⟨z, hz⟩
  obtain ⟨a, t, rfl⟩ := Set.mem_iUnion.1 hw'
  have h1 : ⊤ ≤ x a ⁻¹ᵁ Y.basicOpen f := fun t' _ => by
    have : t' = t := Subsingleton.elim (α := PrimeSpectrum K) _ _
    subst this
    exact hw
  have h2 : ⊤ ≤ x a ⁻¹ᵁ V := h1.trans ((x a).preimage_mono (Y.basicOpen_le f))
  have := (isUnit_valR_iff (x a) V h2 f).2 h1
  rw [valR_eq _ _ h2, hf a h2] at this
  exact (not_isUnit_zero this).elim

/- English proof (translation)
Use `eq_of_valHom_eq _ _ ⊤ (isAffineOpen_top _) le_top le_top (RingHom.ext fun f => ?_)` and prove the remaining obligations. Take `⟨a, rfl⟩` from `(Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective f`. Use `e a` as an intermediate fact. Rewrite `this` using `[valHom_constFn, valHom_constFn]`. Conclude with `this`.
-/
theorem comp_eq_of_const {k R : Type} [CommRing k] [CommRing R] {X Y : Scheme.{0}} (p : X ⟶ Sp k)
    (p' : Y ⟶ Sp k) (x : Sp R ⟶ X) (y : Sp R ⟶ Y) {U : X.Opens} {V : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ y ⁻¹ᵁ V) (e : ∀ a, valHom x U h (constFn p U a) = valHom y V h' (constFn p' V a)) :
    x ≫ p = y ≫ p' := by
  refine eq_of_valHom_eq _ _ ⊤ (isAffineOpen_top _) le_top le_top (RingHom.ext fun f => ?_)
  obtain ⟨a, rfl⟩ := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective f
  have := e a
  rw [valHom_constFn, valHom_constFn] at this
  exact this

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {p' : Y ⟶ Sp k} {H : LB X} {H' : LB Y}
  {J : Type} {s : J → H.Sec} {s' : J → H'.Sec}

/- English proof (translation)
Take `⟨hA, r, hr, hc⟩` from `hI.2 i (Set.mem_univ i)`. Use `choose r' hr' using fun j => (GlobalTheory.SecRatio.existsUnique_isRatio hH' (s' j) (s' i) (nonzeroLocus (s' i)) le_rfl).exists`. Set `ev` to `MvPolynomial.eval₂Hom (constHom p (nonzeroLocus (s i))) r`. Set `ev'` to `MvPolynomial.eval₂Hom (constHom p' (nonzeroLocus (s' i))) r'`. Establish `hs : Function.Surjective ev`.

Rewrite using `[← RingHom.range_eq_top, eq_top_iff, ← hc, Subring.closure_le]`. Introduce and unpack `_ (⟨a, rfl⟩ | ⟨j, rfl⟩)`. Conclude with `⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩`. Conclude with `⟨MvPolynomial.X j, MvPolynomial.eval₂Hom_X' _ _ _⟩`. Establish `hk : RingHom.ker ev ≤ RingHom.ker ev'`.

Introduce `f hf`. Use `eq_zero_of_dense x hd _ _ fun a h => ?_` and prove the remaining obligations. Take `⟨e, v, hv', hv⟩` from `hx a`. Establish `hu : IsUnit (v i)` using `(crd_isUnit_iff i hv').2 h`. Establish `h'` using `(crd_isUnit_iff i hv).1 hu`.

Establish `: (valHom (x a) _ h).comp ev' = (valHom (x' a) _ h').comp ev`. Use `MvPolynomial.ringHom_ext (fun c => ?_) fun j => ?_` and prove the remaining obligations. Simplify using `only [ev, ev', RingHom.comp_apply, MvPolynomial.eval₂Hom_C, constHom_apply, valHom_constFn, e]`. Simplify using `only [ev, ev', RingHom.comp_apply, MvPolynomial.eval₂Hom_X']`. Establish `e` using `(crd_ratio hv' (hr' j) h).symm.trans (crd_ratio hv (hr j) h')`.

Rewrite `e` using `[valR_eq _ _ h, valR_eq _ _ h']`. Conclude with `hu.mul_right_cancel e`. Use `congrArg (fun q => q f) this` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`. Rewrite using `[this, (RingHom.mem_ker).1 hf, map_zero]`.

Set `φ` to `RingHom.liftOfSurjective ev hs ⟨ev', hk⟩`. Establish `hφ : ∀ f, φ (ev f) = ev' f` using `fun f => RingHom.liftOfSurjective_comp_apply ev hs ⟨ev', hk⟩ f`. Establish `hφc : ∀ a, φ (constFn p _ a) = constFn p' _ a` using `fun a => by`. Use `hφ (MvPolynomial.C a)` as an intermediate fact. Simplify `this` using `only [ev, ev', MvPolynomial.eval₂Hom_C, constHom_apply]`.

Establish `hφr : ∀ j, φ (r j) = r' j` using `fun j => by`. Use `hφ (MvPolynomial.X j)` as an intermediate fact. Simplify `this` using `only [ev, ev', MvPolynomial.eval₂Hom_X']`. Take `⟨g, hg⟩` from `exists_hom_of_ringHom hA _ φ`. Use `⟨g, fun R _ _ y => ?_⟩` and prove the remaining obligations.

Establish `h : ⊤ ≤ (y ≫ (nonzeroLocus (s' i)).ι) ⁻¹ᵁ nonzeroLocus (s' i)` using `fun z _ => (y z).2`. Take `⟨h', hv⟩` from `hg R y h`. Use `⟨comp_eq_of_const p p' _ _ h' h fun a => by rw [hv, hφc], fun v hv' => ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `crd_exists hH s (y ≫ g)`. Establish `hu : IsUnit (v i)` using `(crd_isUnit_iff i hv').2 h`.

Establish `hu' : IsUnit (w i)` using `(crd_isUnit_iff i hw).2 h'`. Use `crd_smul (hu.unit * hu'.unit⁻¹) hw` as an intermediate fact. Use `this using 2 with j` and compare the differences between its conclusion and the goal. Rewrite using `[crd_ratio hv' (hr' j) h, crd_ratio hw (hr j) h', valR_eq _ _ h, valR_eq _ _ h', hv, hφr, mul_left_comm, Units.val_mul, _root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one, IsUnit.unit_spec]`.
-/
theorem exists_chart [IsReduced Y] (hH : H.IsLB) (hH' : H'.IsLB) (hI : ImmBy p H s Set.univ)
    {K : Type} [Field K] {A : Type} (x : A → (Sp K ⟶ Y)) (x' : A → (Sp K ⟶ X))
    (hd : Dense (⋃ a, Set.range (x a)))
    (hx : ∀ a, x' a ≫ p = x a ≫ p' ∧ ∃ v, Crd H' s' (x a) v ∧ Crd H s (x' a) v) (i : J) :
    ∃ g : (nonzeroLocus (s' i)).toScheme ⟶ X, ∀ (R : Type) [CommRing R] [IsLocalRing R]
      (y : Sp R ⟶ (nonzeroLocus (s' i)).toScheme),
      (y ≫ g) ≫ p = (y ≫ (nonzeroLocus (s' i)).ι) ≫ p' ∧
        ∀ v, Crd H' s' (y ≫ (nonzeroLocus (s' i)).ι) v → Crd H s (y ≫ g) v := by
  obtain ⟨hA, r, hr, hc⟩ := hI.2 i (Set.mem_univ i)
  choose r' hr' using fun j =>
    (GlobalTheory.SecRatio.existsUnique_isRatio hH' (s' j) (s' i) (nonzeroLocus (s' i)) le_rfl).exists
  let ev := MvPolynomial.eval₂Hom (constHom p (nonzeroLocus (s i))) r
  let ev' := MvPolynomial.eval₂Hom (constHom p' (nonzeroLocus (s' i))) r'
  have hs : Function.Surjective ev := by
    rw [← RingHom.range_eq_top, eq_top_iff, ← hc, Subring.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩
    · exact ⟨MvPolynomial.X j, MvPolynomial.eval₂Hom_X' _ _ _⟩
  have hk : RingHom.ker ev ≤ RingHom.ker ev' := by
    intro f hf
    refine eq_zero_of_dense x hd _ _ fun a h => ?_
    obtain ⟨e, v, hv', hv⟩ := hx a
    have hu : IsUnit (v i) := (crd_isUnit_iff i hv').2 h
    have h' := (crd_isUnit_iff i hv).1 hu
    have : (valHom (x a) _ h).comp ev' = (valHom (x' a) _ h').comp ev := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) fun j => ?_
      · simp only [ev, ev', RingHom.comp_apply, MvPolynomial.eval₂Hom_C, constHom_apply,
          valHom_constFn, e]
      · simp only [ev, ev', RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
        have e := (crd_ratio hv' (hr' j) h).symm.trans (crd_ratio hv (hr j) h')
        rw [valR_eq _ _ h, valR_eq _ _ h'] at e
        exact hu.mul_right_cancel e
    have := congrArg (fun q => q f) this
    simp only [RingHom.comp_apply] at this
    rw [this, (RingHom.mem_ker).1 hf, map_zero]
  let φ := RingHom.liftOfSurjective ev hs ⟨ev', hk⟩
  have hφ : ∀ f, φ (ev f) = ev' f := fun f => RingHom.liftOfSurjective_comp_apply ev hs ⟨ev', hk⟩ f
  have hφc : ∀ a, φ (constFn p _ a) = constFn p' _ a := fun a => by
    have := hφ (MvPolynomial.C a)
    simpa only [ev, ev', MvPolynomial.eval₂Hom_C, constHom_apply] using this
  have hφr : ∀ j, φ (r j) = r' j := fun j => by
    have := hφ (MvPolynomial.X j)
    simpa only [ev, ev', MvPolynomial.eval₂Hom_X'] using this
  obtain ⟨g, hg⟩ := exists_hom_of_ringHom hA _ φ
  refine ⟨g, fun R _ _ y => ?_⟩
  have h : ⊤ ≤ (y ≫ (nonzeroLocus (s' i)).ι) ⁻¹ᵁ nonzeroLocus (s' i) := fun z _ => (y z).2
  obtain ⟨h', hv⟩ := hg R y h
  refine ⟨comp_eq_of_const p p' _ _ h' h fun a => by rw [hv, hφc], fun v hv' => ?_⟩
  obtain ⟨w, hw⟩ := crd_exists hH s (y ≫ g)
  have hu : IsUnit (v i) := (crd_isUnit_iff i hv').2 h
  have hu' : IsUnit (w i) := (crd_isUnit_iff i hw).2 h'
  have := crd_smul (hu.unit * hu'.unit⁻¹) hw
  convert this using 2 with j
  rw [crd_ratio hv' (hr' j) h, crd_ratio hw (hr j) h', valR_eq _ _ h, valR_eq _ _ h', hv, hφr,
    mul_left_comm, Units.val_mul, _root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one, IsUnit.unit_spec]

/- English proof (translation)
Introduce `k _ X Y _ p p' H H' J _ s s' hH hH' hI hc K _ A x x' hd hx`. Use `choose g hg using exists_chart hH hH' hI x x' hd hx`. Set `𝒰` to `Y.openCoverOfIsOpenCover (fun j => nonzeroLocus (s' j)) hc`. Establish `hcomp : ∀ i j : J, pullback.fst (nonzeroLocus (s' i)).ι (nonzeroLocus (s' j)).ι ≫ g i = pullback.snd (nonzeroLocus (s' i)).ι (nonzeroLocus (s' j)).ι ≫ g j`. Introduce `i j`.

Use `ext_local _ _ fun R _ _ y => ?_` and prove the remaining obligations. Establish `e : (y ≫ pullback.fst _ _) ≫ (nonzeroLocus (s' i)).ι = (y ≫ pullback.snd _ _) ≫ (nonzeroLocus (s' j)).ι`. Rewrite using `[Category.assoc, Category.assoc, pullback.condition]`. Take `⟨a₁, b₁⟩` from `hg i R (y ≫ pullback.fst _ _)`. Take `⟨a₂, b₂⟩` from `hg j R (y ≫ pullback.snd _ _)`.

Take `⟨v, hv⟩` from `crd_exists hH' s' ((y ≫ pullback.fst _ _) ≫ (nonzeroLocus (s' i)).ι)`. Rewrite using `[← Category.assoc, ← Category.assoc]`. Conclude with `eq_of_crd_eq k X p H J s _ hH hI R _ _ v (by rw [a₁, a₂, e]) (b₁ v hv) (b₂ v (e ▸ hv))`. Establish `hG : ∀ i, (nonzeroLocus (s' i)).ι ≫ 𝒰.glueMorphisms g hcomp = g i` using `fun i => 𝒰.ι_glueMorphisms g hcomp i`. Establish `key : ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ Y), (y ≫ 𝒰.glueMorphisms g hcomp) ≫ p = y ≫ p' ∧ ∀ v, Crd H' s' y v → Crd H s (y ≫ 𝒰.glueMorphisms g hcomp) v`.

Introduce `R _ _ y`. Establish `: y (IsLocalRing.closedPoint R) ∈ ⨆ j, nonzeroLocus (s' j)` using `by rw [hc]; trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 this`. Establish `h` using `(top_le_iff y _).2 hi`. Establish `hr : Set.range y ⊆ Set.range (nonzeroLocus (s' i)).ι`.

Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `h (Set.mem_univ z)`. Establish `e` using `IsOpenImmersion.lift_fac (nonzeroLocus (s' i)).ι y hr`. Use `hg i R (IsOpenImmersion.lift (nonzeroLocus (s' i)).ι y hr)` as an intermediate fact.

Rewrite `this` using `[← hG i, ← Category.assoc, e]`. Then use the resulting hypothesis. Use `⟨𝒰.glueMorphisms g hcomp, ext_local _ _ fun R _ _ y => ?_, fun a => ?_, fun R _ _ y => (key R y).2⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, (key R y).1]`. Take `⟨e, v, hv', hv⟩` from `hx a`. Conclude with `eq_of_crd_eq k X p H J s _ hH hI K _ _ v (by rw [(key K (x a)).1, e]) ((key K (x a)).2 v hv') hv`.
-/
theorem exists_factor : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsReduced Y] (p : X ⟶ Sp k) (p' : Y ⟶ Sp k) (H : LB X) (H' : LB Y) (J : Type) [Fintype J] (s : J → H.Sec) (s' : J → H'.Sec), H.IsLB → H'.IsLB → ImmBy p H s Set.univ → ⨆ j, nonzeroLocus (s' j) = ⊤ → ∀ (K : Type) [Field K] (A : Type) (x : A → (Sp K ⟶ Y)) (x' : A → (Sp K ⟶ X)), Dense (⋃ a, Set.range (x a)) → (∀ a, x' a ≫ p = x a ≫ p' ∧ ∃ v, Crd H' s' (x a) v ∧ Crd H s (x' a) v) → ∃ g : Y ⟶ X, g ≫ p = p' ∧ (∀ a, x a ≫ g = x' a) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ Y) (v : J → R), Crd H' s' y v → Crd H s (y ≫ g) v := by
  intro k _ X Y _ p p' H H' J _ s s' hH hH' hI hc K _ A x x' hd hx
  choose g hg using exists_chart hH hH' hI x x' hd hx
  let 𝒰 := Y.openCoverOfIsOpenCover (fun j => nonzeroLocus (s' j)) hc
  have hcomp : ∀ i j : J, pullback.fst (nonzeroLocus (s' i)).ι (nonzeroLocus (s' j)).ι ≫ g i =
      pullback.snd (nonzeroLocus (s' i)).ι (nonzeroLocus (s' j)).ι ≫ g j := by
    intro i j
    refine ext_local _ _ fun R _ _ y => ?_
    have e : (y ≫ pullback.fst _ _) ≫ (nonzeroLocus (s' i)).ι =
        (y ≫ pullback.snd _ _) ≫ (nonzeroLocus (s' j)).ι := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    obtain ⟨a₁, b₁⟩ := hg i R (y ≫ pullback.fst _ _)
    obtain ⟨a₂, b₂⟩ := hg j R (y ≫ pullback.snd _ _)
    obtain ⟨v, hv⟩ := crd_exists hH' s' ((y ≫ pullback.fst _ _) ≫ (nonzeroLocus (s' i)).ι)
    rw [← Category.assoc, ← Category.assoc]
    exact eq_of_crd_eq k X p H J s _ hH hI R _ _ v (by rw [a₁, a₂, e]) (b₁ v hv) (b₂ v (e ▸ hv))
  have hG : ∀ i, (nonzeroLocus (s' i)).ι ≫ 𝒰.glueMorphisms g hcomp = g i :=
    fun i => 𝒰.ι_glueMorphisms g hcomp i
  have key : ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ Y),
      (y ≫ 𝒰.glueMorphisms g hcomp) ≫ p = y ≫ p' ∧
        ∀ v, Crd H' s' y v → Crd H s (y ≫ 𝒰.glueMorphisms g hcomp) v := by
    intro R _ _ y
    have : y (IsLocalRing.closedPoint R) ∈ ⨆ j, nonzeroLocus (s' j) := by rw [hc]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    have h := (top_le_iff y _).2 hi
    have hr : Set.range y ⊆ Set.range (nonzeroLocus (s' i)).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      exact h (Set.mem_univ z)
    have e := IsOpenImmersion.lift_fac (nonzeroLocus (s' i)).ι y hr
    have := hg i R (IsOpenImmersion.lift (nonzeroLocus (s' i)).ι y hr)
    rwa [← hG i, ← Category.assoc, e] at this
  refine ⟨𝒰.glueMorphisms g hcomp, ext_local _ _ fun R _ _ y => ?_, fun a => ?_,
    fun R _ _ y => (key R y).2⟩
  · rw [← Category.assoc, (key R y).1]
  · obtain ⟨e, v, hv', hv⟩ := hx a
    exact eq_of_crd_eq k X p H J s _ hH hI K _ _ v (by rw [(key K (x a)).1, e]) ((key K (x a)).2 v hv') hv

end GlobalTheory.ZH.ToImm
end
