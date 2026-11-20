import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomBirationalModelsAmpleFramesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliFiniteSurjectiveOverGenericFamilyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOnTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelChangeActsOnUnitaryFamilyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoprimeLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullObjOfObj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.TopOfFamily

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc pullback.lift_snd_assoc

/- English proof (translation)
Establish `hp` using `isPullback_morphismRestrict u W`. Use `⟨inv (u ∣_ W) ≫ (u ⁻¹ᵁ W).ι, inferInstance, ?_, fun T g b h => ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]`. Establish `h1` using `hp.lift_fst b g h.symm`. Establish `h2` using `hp.lift_snd b g h.symm`.

Rewrite using `[← h1, Category.assoc, IsIso.hom_inv_id_assoc, h2]`.
-/
theorem exists_section {U M : Scheme.{0}} (u : U ⟶ M) (W : M.Opens) [IsIso (u ∣_ W)] :
    ∃ i : W.toScheme ⟶ U, IsOpenImmersion i ∧ i ≫ u = W.ι ∧
      ∀ (T : Scheme.{0}) (g : T ⟶ U) (b : T ⟶ W.toScheme), g ≫ u = b ≫ W.ι → g = b ≫ i := by
  have hp := isPullback_morphismRestrict u W
  refine ⟨inv (u ∣_ W) ≫ (u ⁻¹ᵁ W).ι, inferInstance, ?_, fun T g b h => ?_⟩
  · rw [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  · have h1 := hp.lift_fst b g h.symm
    have h2 := hp.lift_snd b g h.symm
    rw [← h1, Category.assoc, IsIso.hom_inv_id_assoc, h2]

/- English proof (translation)
Take `⟨L, hL⟩` from `GlobalTheory.exists_isAmpleLB_of_isProjOver h`. Use `projProper _ _ _ h` as an intermediate fact. Establish `: IsIso (CommRingCat.ofHom σ.toRingHom)` using `σ.toCommRingCatIso.isIso_hom`. Conclude with `hL.isProjOver _`.
-/
theorem isProjOver_comp_iso {R : Type} [CommRing R] {Z : Scheme.{0}} {s : Z ⟶ Sp R} (h : IsProjOver s) (σ : R ≃+* R) :
    IsProjOver (s ≫ spMap σ.toRingHom) := by
  obtain ⟨L, hL⟩ := GlobalTheory.exists_isAmpleLB_of_isProjOver h
  have := projProper _ _ _ h
  have : IsIso (CommRingCat.ofHom σ.toRingHom) := σ.toCommRingCatIso.isIso_hom
  exact hL.isProjOver _

/- English proof (translation)
Establish `: ∀ x : Z, _root_.IsReduced (Z.presheaf.stalk x)` using `fun x ↦`. Use `(h x).1` as an intermediate fact. Use `inferInstance`. Conclude with `isReduced_of_isReduced_stalk Z`.
-/
theorem isReduced_of_normal {Z : Scheme.{0}} (h : Geo.Tor.IsNormalScheme Z) : IsReduced Z := by
  have : ∀ x : Z, _root_.IsReduced (Z.presheaf.stalk x) := fun x ↦
    have := (h x).1
    inferInstance
  exact isReduced_of_isReduced_stalk Z

/- English proof (translation)
Take `⟨φ, -⟩` from `Spec.map_surjective (S.fromSpecResidueField p ≫ s)`. Conclude with `charZero_of_injective_ringHom (R := k) φ.hom.injective`.
-/
theorem charZero_residueField {k : Type} [Field k] [CharZero k] {S : Scheme.{0}} (s : S ⟶ Sp k) (p : S) :
    CharZero (S.residueField p) := by
  obtain ⟨φ, -⟩ := Spec.map_surjective (S.fromSpecResidueField p ≫ s)
  exact charZero_of_injective_ringHom (R := k) φ.hom.injective

/- English proof (translation)
Rewrite using `[spMap, spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [spMap, spMap, ← Spec.map_comp]; rfl

/- English proof (translation)
Establish `h : x.asIdeal = ⊥` using `@Ideal.eq_bot_of_prime _ _ _ x.isPrime`. Express the relevant statement in the definitionally equal form `Ideal.comap β x.asIdeal = ⊥`. Rewrite using `[h]`. Conclude with `(RingHom.injective_iff_ker_eq_bot _).1 hβ`.
-/
theorem asIdeal_spMap {A k : Type} [CommRing A] [Field k] (β : A →+* k) (hβ : Function.Injective β) (x : Sp k) :
    (spMap β x).asIdeal = ⊥ := by
  have h : x.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ x.isPrime
  change Ideal.comap β x.asIdeal = ⊥
  rw [h]
  exact (RingHom.injective_iff_ker_eq_bot _).1 hβ

/- English proof (translation)
Use `isDominant_pullback_fst_of_isOpenMap j p p.isOpenEmbedding.isOpenMap` as an intermediate fact. Rewrite using `[← pullbackSymmetry_hom_comp_fst]`. Use `infer_instance`.
-/
theorem isDominant_snd {X U Y : Scheme.{0}} (j : U ⟶ X) [IsDominant j] (p : Y ⟶ X) [IsOpenImmersion p] :
    IsDominant (pullback.snd j p) := by
  have := isDominant_pullback_fst_of_isOpenMap j p p.isOpenEmbedding.isOpenMap
  rw [← pullbackSymmetry_hom_comp_fst]
  infer_instance

/- English proof (translation)
Set `d₁` to `pullback.fst (w₀ ≫ ρ.hom) w₀`. Set `d₂` to `pullback.snd (w₀ ≫ ρ.hom) w₀`. Establish `hd : d₁ ≫ w₀ ≫ ρ.hom = d₂ ≫ w₀` using `pullback.condition`. Establish `key : (d₁ ≫ i ≫ v) ≫ τ = d₂ ≫ i ≫ v`. Use `isReduced_of_isOpenImmersion (d₁ ≫ i ≫ v)` as an intermediate fact.

Use `isDominant_snd (e₁ ≫ j ≫ v) (d₁ ≫ i ≫ v)` as an intermediate fact. Establish `hq` using `pullback.condition (f := e₁ ≫ j ≫ v) (g := d₁ ≫ i ≫ v)`. Use `set q₁ := pullback.fst (e₁ ≫ j ≫ v) (d₁ ≫ i ≫ v)`. Use `set q₂ := pullback.snd (e₁ ≫ j ≫ v) (d₁ ≫ i ≫ v)`. Use `ext_of_isDominant q₂ ?_` and prove the remaining obligations.

Establish `h1 : q₁ ≫ e₁ ≫ j = q₂ ≫ d₁ ≫ i`. Rewrite using `[← cancel_mono v]`. Simplify using `using hq`. Establish `h2 : q₁ ≫ e₂ ≫ j = (q₂ ≫ d₂) ≫ i`. Use `hu _ _ _ ?_` and prove the remaining obligations.

Simplify using `only [Category.assoc]`. Rewrite using `[← he, reassoc_of% h1, reassoc_of% hi, hd]`. Rewrite using `[← Category.assoc q₂, ← hq, Category.assoc, hτ, reassoc_of% h2]`. Establish `h1` using `pullback.lift_fst b b' (f := w₀ ≫ ρ.hom) (g := w₀) hb`. Establish `h2` using `pullback.lift_snd b b' (f := w₀ ≫ ρ.hom) (g := w₀) hb`.

Rewrite using `[← h1]`. Use `conv_rhs => rw [← h2]`. Simplify using `only [Category.assoc] at key ⊢`. Rewrite using `[key]`.
-/
theorem comp_eq_of_dense {Z U M W W₀ W' X : Scheme.{0}} [IsReduced Z] [Z.IsSeparated] (v : U ⟶ Z) [IsOpenImmersion v]
    (u : U ⟶ M) (w₀ : W₀ ⟶ M) [IsOpenImmersion w₀] (i : W₀ ⟶ U) [IsOpenImmersion i] (hi : i ≫ u = w₀)
    (hu : ∀ (T : Scheme.{0}) (g : T ⟶ U) (b : T ⟶ W₀), g ≫ u = b ≫ w₀ → g = b ≫ i)
    (j : W ⟶ U) (e₁ e₂ : W' ⟶ W) [IsDominant (e₁ ≫ j ≫ v)] (ρ : M ≅ M) (he : e₁ ≫ j ≫ u ≫ ρ.hom = e₂ ≫ j ≫ u)
    (τ : Z ⟶ Z) (hτ : (e₁ ≫ j ≫ v) ≫ τ = e₂ ≫ j ≫ v) (b b' : X ⟶ W₀) (hb : b ≫ w₀ ≫ ρ.hom = b' ≫ w₀) :
    (b ≫ i ≫ v) ≫ τ = b' ≫ i ≫ v := by
  let d₁ := pullback.fst (w₀ ≫ ρ.hom) w₀
  let d₂ := pullback.snd (w₀ ≫ ρ.hom) w₀
  have hd : d₁ ≫ w₀ ≫ ρ.hom = d₂ ≫ w₀ := pullback.condition
  have key : (d₁ ≫ i ≫ v) ≫ τ = d₂ ≫ i ≫ v := by
    have := isReduced_of_isOpenImmersion (d₁ ≫ i ≫ v)
    have := isDominant_snd (e₁ ≫ j ≫ v) (d₁ ≫ i ≫ v)
    have hq := pullback.condition (f := e₁ ≫ j ≫ v) (g := d₁ ≫ i ≫ v)
    set q₁ := pullback.fst (e₁ ≫ j ≫ v) (d₁ ≫ i ≫ v)
    set q₂ := pullback.snd (e₁ ≫ j ≫ v) (d₁ ≫ i ≫ v)
    refine ext_of_isDominant q₂ ?_
    have h1 : q₁ ≫ e₁ ≫ j = q₂ ≫ d₁ ≫ i := by
      rw [← cancel_mono v]; simpa using hq
    have h2 : q₁ ≫ e₂ ≫ j = (q₂ ≫ d₂) ≫ i := by
      refine hu _ _ _ ?_
      simp only [Category.assoc]
      rw [← he, reassoc_of% h1, reassoc_of% hi, hd]
    rw [← Category.assoc q₂, ← hq, Category.assoc, hτ, reassoc_of% h2]
  have h1 := pullback.lift_fst b b' (f := w₀ ≫ ρ.hom) (g := w₀) hb
  have h2 := pullback.lift_snd b b' (f := w₀ ≫ ρ.hom) (g := w₀) hb
  rw [← h1]
  conv_rhs => rw [← h2]
  simp only [Category.assoc] at key ⊢
  rw [key]

/- English proof (translation)
Establish `hp` using `isPullback_morphismRestrict (pullback.fst s β) U`. Take `⟨p, hp₀⟩ : ∃ p, p ≫ w₀ = pullback.fst sM β` from `⟨_, IsOpenImmersion.lift_fac w₀ _ hr⟩`. Establish `c₁ : (p ≫ i ≫ U.ι) ≫ s = pullback.snd sM β ≫ β`. Simplify using `only [Category.assoc]`. Rewrite using `[← hs, reassoc_of% hi, reassoc_of% hp₀, pullback.condition]`.

Establish `c₂ : (p ≫ i) ≫ U.ι = pullback.lift _ _ c₁ ≫ pullback.fst s β` using `by simp`. Establish `c₃ : (pullback.fst s β ∣_ U ≫ u) ≫ sM = ((pullback.fst s β ⁻¹ᵁ U).ι ≫ pullback.snd s β) ≫ β`. Simplify using `only [Category.assoc]`. Rewrite using `[hs, morphismRestrict_ι_assoc, pullback.condition]`. Establish `g₁` using `hp.lift_fst _ _ c₂`.

Establish `g₂` using `hp.lift_snd _ _ c₂`. Use `set g := hp.lift _ _ c₂`. Establish `hk : pullback.fst s β ∣_ U = (pullback.lift _ _ c₃ ≫ p) ≫ i` using `hu _ _ _ (by simp [hp₀])`. Establish `: IsIso g`. Use `⟨pullback.lift _ _ c₃, ?_, ?_⟩` and prove the remaining obligations.

Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `[reassoc_of% g₁, hi, hp₀]`. Simplify using `[reassoc_of% g₂]`. Apply `hp.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, g₁, Category.id_comp, ← Category.assoc, ← hk]`.

Rewrite using `[Category.assoc, g₂, Category.id_comp]`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc, pullback.lift_fst]`. Rewrite using `[← morphismRestrict_ι]`. Use `conv_rhs => rw [hk]`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Use `⟨pullback.lift _ _ h ≫ g, inferInstance, inferInstance, ?_, ?_⟩` and prove the remaining obligations. Establish `: pullback.lift _ _ h ≫ p = b`. Rewrite using `[← cancel_mono w₀]`.

Simplify using `[hp₀]`. Simplify using `[reassoc_of% g₂, reassoc_of% this]`. Simplify using `[reassoc_of% g₂]`.
-/
theorem exists_finite_lift {Z M W₀ X B B' : Scheme.{0}} (U : Z.Opens) (s : Z ⟶ B) (sM : M ⟶ B) (β : B' ⟶ B)
    (u : U.toScheme ⟶ M) (hs : u ≫ sM = U.ι ≫ s) (w₀ : W₀ ⟶ M) [IsOpenImmersion w₀] (i : W₀ ⟶ U.toScheme)
    (hi : i ≫ u = w₀) (hu : ∀ (T : Scheme.{0}) (g : T ⟶ U) (b : T ⟶ W₀), g ≫ u = b ≫ w₀ → g = b ≫ i)
    (hr : Set.range (pullback.fst sM β) ⊆ Set.range w₀) (b : X ⟶ W₀) (c : X ⟶ B') (h : (b ≫ w₀) ≫ sM = c ≫ β)
    (hf : IsFinite (pullback.lift _ _ h)) (hsu : Surjective (pullback.lift _ _ h)) :
    ∃ f : X ⟶ (pullback.fst s β ⁻¹ᵁ U).toScheme, IsFinite f ∧ Surjective f ∧
      f ≫ (pullback.fst s β ⁻¹ᵁ U).ι ≫ pullback.fst _ _ = b ≫ i ≫ U.ι ∧
      f ≫ (pullback.fst s β ⁻¹ᵁ U).ι ≫ pullback.snd _ _ = c := by
  have hp := isPullback_morphismRestrict (pullback.fst s β) U
  obtain ⟨p, hp₀⟩ : ∃ p, p ≫ w₀ = pullback.fst sM β := ⟨_, IsOpenImmersion.lift_fac w₀ _ hr⟩
  have c₁ : (p ≫ i ≫ U.ι) ≫ s = pullback.snd sM β ≫ β := by
    simp only [Category.assoc]
    rw [← hs, reassoc_of% hi, reassoc_of% hp₀, pullback.condition]
  have c₂ : (p ≫ i) ≫ U.ι = pullback.lift _ _ c₁ ≫ pullback.fst s β := by simp
  have c₃ : (pullback.fst s β ∣_ U ≫ u) ≫ sM = ((pullback.fst s β ⁻¹ᵁ U).ι ≫ pullback.snd s β) ≫ β := by
    simp only [Category.assoc]
    rw [hs, morphismRestrict_ι_assoc, pullback.condition]
  have g₁ := hp.lift_fst _ _ c₂
  have g₂ := hp.lift_snd _ _ c₂
  set g := hp.lift _ _ c₂
  have hk : pullback.fst s β ∣_ U = (pullback.lift _ _ c₃ ≫ p) ≫ i := hu _ _ _ (by simp [hp₀])
  have : IsIso g := by
    refine ⟨pullback.lift _ _ c₃, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp [reassoc_of% g₁, hi, hp₀]
      · simp [reassoc_of% g₂]
    · apply hp.hom_ext
      · rw [Category.assoc, g₁, Category.id_comp, ← Category.assoc, ← hk]
      · rw [Category.assoc, g₂, Category.id_comp]
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst]
          rw [← morphismRestrict_ι]
          conv_rhs => rw [hk]
          simp
        · simp
  refine ⟨pullback.lift _ _ h ≫ g, inferInstance, inferInstance, ?_, ?_⟩
  · have : pullback.lift _ _ h ≫ p = b := by
      rw [← cancel_mono w₀]; simp [hp₀]
    simp [reassoc_of% g₂, reassoc_of% this]
  · simp [reassoc_of% g₂]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `sabComp pullCubComp E H _ _ _ t t' t'' f g m m'`.
-/
theorem comp_of_eq {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (m' : SABMap t'' t' g) (e : g ≫ f = h) :
    ∃ n : SABMap t'' t h, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabComp pullCubComp E H _ _ _ t t' t'' f g m m'

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `sabCancel pullCubCancel E H _ _ _ t t' t'' f g m n`.
-/
theorem cancel_of_eq {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t h) (e : g ≫ f = h) :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabCancel pullCubCancel E H _ _ _ t t' t'' f g m n

section Model

variable {R : Type} [CommRing R] {MM : Scheme.{0}} {sM : MM ⟶ Sp R} {tM : SAB H MM} {m : ℕ} (C : ZOn sM tM m)

/- English proof (translation)
Use `projProper _ _ _ C.proj` as an intermediate fact. Conclude with `LocallyOfFiniteType.isLocallyNoetherian C.s`.
-/
theorem isLocallyNoetherian [IsNoetherianRing R] : IsLocallyNoetherian C.Z := by
  have := projProper _ _ _ C.proj
  exact LocallyOfFiniteType.isLocallyNoetherian C.s

/- English proof (translation)
Use `projProper _ _ _ C.proj` as an intermediate fact. Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[← terminal.comp_from C.s]`. Use `infer_instance`.
-/
theorem isSeparated : C.Z.IsSeparated := by
  have := projProper _ _ _ C.proj
  refine ⟨?_⟩
  rw [← terminal.comp_from C.s]
  infer_instance

/- English proof (translation)
Use `isLocallyNoetherian C` as an intermediate fact. Use `C.j_open` as an intermediate fact. Use `C.j_dom` as an intermediate fact. Use `(genericPoints_subset_range_of_isDominant C.j).trans ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`.

Rewrite using `[abLocus_pullback abLocusOne C.t.semi C.m₂.cart.1, ← abLocus_pullback abLocusOne tM.semi C.m₁.cart.1]`. Introduce `K _ _ t _`. Use `infer_instance`.
-/
theorem genericPoints_subset [IsNoetherianRing R] [IsProper tM.G.hom] : genericPoints C.Z ⊆ abLocus C.t.G := by
  have := isLocallyNoetherian C
  have := C.j_open
  have := C.j_dom
  refine (genericPoints_subset_range_of_isDominant C.j).trans ?_
  rintro _ ⟨x, rfl⟩
  rw [abLocus_pullback abLocusOne C.t.semi C.m₂.cart.1, ← abLocus_pullback abLocusOne tM.semi C.m₁.cart.1]
  intro K _ _ t _
  infer_instance

/- English proof (translation)
Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[abLocus_pullback abLocusOne C.t.semi C.m₂.cart.1, ← abLocus_pullback abLocusOne tM.semi C.m₁.cart.1]`. Introduce `K _ _ t _`. Use `infer_instance`.
-/
theorem range_j_subset [IsProper tM.G.hom] : Set.range C.j ⊆ abLocus C.t.G := by
  rintro _ ⟨x, rfl⟩
  rw [abLocus_pullback abLocusOne C.t.semi C.m₂.cart.1, ← abLocus_pullback abLocusOne tM.semi C.m₁.cart.1]
  intro K _ _ t _
  infer_instance

/- English proof (translation)
Use `isLocallyNoetherian C` as an intermediate fact. Use `isSeparated C` as an intermediate fact. Use `isReduced_of_normal C.normal` as an intermediate fact. Use `C.j_open` as an intermediate fact. Use `C.j_dom` as an intermediate fact.

Establish `: IsDominant C.W.ι` using `⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact C.dense⟩`. Establish `d₁` using `isDominant_pullback_fst_of_isOpenMap C.W.ι (C.W.ι ≫ ρ.hom) (C.W.ι ≫ ρ.hom).isOpenEmbedding.isOpenMap`. Establish `d₂` using `isDominant_snd (C.W.ι ≫ ρ.hom) C.W.ι`. Establish `he` using `pullback.condition (f := C.W.ι ≫ ρ.hom) (g := C.W.ι)`. Establish `o₁ : IsOpenImmersion (pullback.fst (C.W.ι ≫ ρ.hom) C.W.ι)` using `inferInstance`.

Establish `o₂ : IsOpenImmersion (pullback.snd (C.W.ι ≫ ρ.hom) C.W.ι)` using `inferInstance`. Use `set e₁ := pullback.fst (C.W.ι ≫ ρ.hom) C.W.ι`. Use `set e₂ := pullback.snd (C.W.ι ≫ ρ.hom) C.W.ι`. Choose the witnesses or unpack the hypotheses as in `⟨t', ⟨n₁⟩⟩ : ∃ t' : SAB H _, Nonempty (SABMap t' C.tW e₁) := by`. Take `⟨_, _, _, _, _, n, -⟩` from `sabPull Out.CubePf.cubePull e₁ C.tW`.

Conclude with `⟨_, ⟨n⟩⟩`. Take `⟨k₁, -⟩` from `comp_of_eq C.m₁ n₁ rfl`. Take `⟨k₂, -⟩` from `comp_of_eq mu k₁ ((Category.assoc _ _ _).trans he)`. Take `⟨n₂, -⟩` from `cancel_of_eq C.m₁ k₂ rfl`. Take `⟨p₁, -⟩` from `comp_of_eq C.m₂ n₁ rfl`.

Take `⟨p₂, -⟩` from `comp_of_eq C.m₂ n₂ rfl`. Establish `hp : IsProper t'.G.hom` using `MorphismProperty.of_isPullback k₁.cart.1 inferInstance`. Establish `h₂ : (e₂ ≫ C.j) ≫ C.s = (e₁ ≫ C.j) ≫ C.s ≫ spMap σ.toRingHom`. Simplify using `only [Category.assoc]`. Rewrite using `[C.j_over, reassoc_of% C.j_over, ← reassoc_of% he, hρ]`.

Establish `h₁ : (e₁ ≫ C.j) ≫ C.s = (e₂ ≫ C.j) ≫ C.s ≫ spMap σ.symm.toRingHom`. Establish `: spMap σ.toRingHom ≫ spMap σ.symm.toRingHom = 𝟙 _`. Rewrite using `[spMap_comp, RingEquiv.toRingHom_comp_symm_toRingHom]`. Conclude with `Spec.map_id _`. Rewrite using `[← Category.assoc _ C.s, h₂, Category.assoc (e₁ ≫ C.j), Category.assoc C.s, this, Category.comp_id]`.

Take `⟨τ, hτ⟩` from `GlobalTheory.T.exists_hom_birational_models_ampleFrames hH E H R C.Z C.Z _ C.s _ C.t C.t t' _ _ p₁ p₂ _ C.amp C.amp hR inferInstance hft C.normal C.proj (isProjOver_comp_iso C.proj σ.symm) C.flat inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance …`. Take `⟨τ', hτ'⟩` from `GlobalTheory.T.exists_hom_birational_models_ampleFrames hH E H R C.Z C.Z _ C.s _ C.t C.t t' _ _ p₂ p₁ _ C.amp C.amp hR inferInstance hft C.normal C.proj (isProjOver_comp_iso C.proj σ) C.flat inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance infer …`. Use `⟨_, e₁, e₂, ⟨τ, τ', ?_, ?_⟩, inferInstance, he, hτ⟩` and prove the remaining obligations. Use `ext_of_isDominant (e₁ ≫ C.j) ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, hτ, hτ', Category.comp_id]`.

Use `ext_of_isDominant (e₂ ≫ C.j) ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, hτ', hτ, Category.comp_id]`.
-/
theorem exists_iso (hH : GlobalTheory.LN.HomExtSt) (hR : IsDedekindDomain R) [CharZero R] (hft : Algebra.FiniteType ℤ R)
    [IsProper tM.G.hom] (ρ : MM ≅ MM) (mu : SABMap tM tM ρ.hom) (σ : R ≃+* R)
    (hρ : ρ.hom ≫ sM = sM ≫ spMap σ.toRingHom) :
    ∃ (W' : Scheme.{0}) (e₁ e₂ : W' ⟶ C.W.toScheme) (τ : C.Z ≅ C.Z), IsDominant (e₁ ≫ C.j) ∧
      e₁ ≫ C.W.ι ≫ ρ.hom = e₂ ≫ C.W.ι ∧ (e₁ ≫ C.j) ≫ τ.hom = e₂ ≫ C.j := by
  have := isLocallyNoetherian C
  have := isSeparated C
  have := isReduced_of_normal C.normal
  have := C.j_open
  have := C.j_dom
  have : IsDominant C.W.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact C.dense⟩
  have d₁ := isDominant_pullback_fst_of_isOpenMap C.W.ι (C.W.ι ≫ ρ.hom) (C.W.ι ≫ ρ.hom).isOpenEmbedding.isOpenMap
  have d₂ := isDominant_snd (C.W.ι ≫ ρ.hom) C.W.ι
  have he := pullback.condition (f := C.W.ι ≫ ρ.hom) (g := C.W.ι)
  have o₁ : IsOpenImmersion (pullback.fst (C.W.ι ≫ ρ.hom) C.W.ι) := inferInstance
  have o₂ : IsOpenImmersion (pullback.snd (C.W.ι ≫ ρ.hom) C.W.ι) := inferInstance
  set e₁ := pullback.fst (C.W.ι ≫ ρ.hom) C.W.ι
  set e₂ := pullback.snd (C.W.ι ≫ ρ.hom) C.W.ι
  obtain ⟨t', ⟨n₁⟩⟩ : ∃ t' : SAB H _, Nonempty (SABMap t' C.tW e₁) := by
    obtain ⟨_, _, _, _, _, n, -⟩ := sabPull Out.CubePf.cubePull e₁ C.tW
    exact ⟨_, ⟨n⟩⟩
  obtain ⟨k₁, -⟩ := comp_of_eq C.m₁ n₁ rfl
  obtain ⟨k₂, -⟩ := comp_of_eq mu k₁ ((Category.assoc _ _ _).trans he)
  obtain ⟨n₂, -⟩ := cancel_of_eq C.m₁ k₂ rfl
  obtain ⟨p₁, -⟩ := comp_of_eq C.m₂ n₁ rfl
  obtain ⟨p₂, -⟩ := comp_of_eq C.m₂ n₂ rfl
  have hp : IsProper t'.G.hom := MorphismProperty.of_isPullback k₁.cart.1 inferInstance
  have h₂ : (e₂ ≫ C.j) ≫ C.s = (e₁ ≫ C.j) ≫ C.s ≫ spMap σ.toRingHom := by
    simp only [Category.assoc]
    rw [C.j_over, reassoc_of% C.j_over, ← reassoc_of% he, hρ]
  have h₁ : (e₁ ≫ C.j) ≫ C.s = (e₂ ≫ C.j) ≫ C.s ≫ spMap σ.symm.toRingHom := by
    have : spMap σ.toRingHom ≫ spMap σ.symm.toRingHom = 𝟙 _ := by
      rw [spMap_comp, RingEquiv.toRingHom_comp_symm_toRingHom]
      exact Spec.map_id _
    rw [← Category.assoc _ C.s, h₂, Category.assoc (e₁ ≫ C.j), Category.assoc C.s, this, Category.comp_id]
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_hom_birational_models_ampleFrames hH E H R C.Z C.Z _ C.s _ C.t C.t t' _ _ p₁ p₂ _ C.amp C.amp hR inferInstance hft
    C.normal C.proj (isProjOver_comp_iso C.proj σ.symm) C.flat inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance hp h₁ rfl rfl
  obtain ⟨τ', hτ'⟩ := GlobalTheory.T.exists_hom_birational_models_ampleFrames hH E H R C.Z C.Z _ C.s _ C.t C.t t' _ _ p₂ p₁ _ C.amp C.amp hR inferInstance hft
    C.normal C.proj (isProjOver_comp_iso C.proj σ) C.flat inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance hp h₂ rfl rfl
  refine ⟨_, e₁, e₂, ⟨τ, τ', ?_, ?_⟩, inferInstance, he, hτ⟩
  · refine ext_of_isDominant (e₁ ≫ C.j) ?_
    rw [← Category.assoc, hτ, hτ', Category.comp_id]
  · refine ext_of_isDominant (e₂ ≫ C.j) ?_
    rw [← Category.assoc, hτ', hτ, Category.comp_id]

end Model

/- English proof (translation)
Substitute `h` using the available equality. Take `⟨j, -, hj⟩` from `hN`. Take `⟨⟨β, hβ⟩, -, h⟩` from `BaseRing.isDedFrac_RZ E H l n j hn.pos hj.dvd`. Take `⟨⟨_, hd⟩, -, hf⟩` from `h β hβ`. Use `letI := β.toAlgebra`.

Use `⟨hd, β, hβ, IsFractionRing.injective (RZ H n l.A) (KA l), ?_⟩` and prove the remaining obligations. Rewrite using `[Flat.SpecMap_iff]`. Conclude with `IsLocalization.flat (KA l) (nonZeroDivisors (RZ H n l.A))`.
-/
theorem exists_inc {n N : ℕ} (hn : n.Prime) (hN : ∃ j, 1 ≤ j ∧ N = n ^ j) (l : Level H) (h : l.A = N) :
    IsDedekindDomain (RZ H n N) ∧ ∃ β : RZ H n N →+* KA l, IsInc (RZ H n N).subtype (KA l).val.toRingHom β ∧
      Function.Injective β ∧ Flat (spMap β) := by
  subst h
  obtain ⟨j, -, hj⟩ := hN
  obtain ⟨⟨β, hβ⟩, -, h⟩ := BaseRing.isDedFrac_RZ E H l n j hn.pos hj.dvd
  obtain ⟨⟨_, hd⟩, -, hf⟩ := h β hβ
  letI := β.toAlgebra
  refine ⟨hd, β, hβ, IsFractionRing.injective (RZ H n l.A) (KA l), ?_⟩
  rw [Flat.SpecMap_iff]
  exact IsLocalization.flat (KA l) (nonZeroDivisors (RZ H n l.A))

/- English proof (translation)
The claim follows from `RingHom.ext fun x => Subtype.ext ((h x).trans (h' x).symm)`.
-/
theorem eq_of_isInc {R : Type} [CommRing R] {i : R →+* ℂ} {l : Level H} {β β' : R →+* KA l}
    (h : IsInc i (KA l).val.toRingHom β) (h' : IsInc i (KA l).val.toRingHom β') : β = β' :=
  RingHom.ext fun x => Subtype.ext ((h x).trans (h' x).symm)

/- English proof (translation)
Substitute `h` using the available equality. Use `Xo.smooth` as an intermediate fact. Establish `hs : Smooth Xo.s` using `SmoothOfRelativeDimension.smooth D.dim Xo.s`. Take `⟨hr, -, hno⟩` from `isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s hs`. Establish `e : a = a'` using `(F.rep _ _ _ _ hr hno inferInstance (fullObj_of_obj Xo.s Xo.univ β hβ)).unique ⟨ha, ν, hν⟩ ⟨ha', ν', hν'⟩`.

Substitute `e` using the available equality. Conclude with `⟨rfl, GlobalTheory.fullObj_rigid hL E H D n _ _ _ sM tM lev _ a ν ν' Xo.univ.etaA h3 hodd F.obj hr (charZero_residueField Xo.s) hν hν'⟩`.
-/
theorem eq_of_level (hL : Out.Laws) {D : Datum H} {n N : ℕ} (h3 : 3 ≤ N) (hodd : Odd N) {MM : Scheme.{0}}
    {sM : MM ⟶ Sp (RZ H n N)} {tM : SAB H MM} {lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)} (F : FamCore D sM tM lev)
    {l : Level H} (h : l.A = N) (Xo : Moduli D l) {β : RZ H n N →+* KA l}
    (hβ : IsInc (RZ H n N).subtype (KA l).val.toRingHom β) [Flat (spMap β)] {a a' : Xo.X ⟶ MM}
    (ν : SABMap Xo.univ.t tM a) (ν' : SABMap Xo.univ.t tM a') (ha : a ≫ sM = Xo.s ≫ spMap β)
    (ha' : a' ≫ sM = Xo.s ≫ spMap β) (hν : ∀ x, (Xo.univ.etaA x).left ≫ ν.φ = a ≫ (lev x).left)
    (hν' : ∀ x, (Xo.univ.etaA x).left ≫ ν'.φ = a' ≫ (lev x).left) : a = a' ∧ ν.φ = ν'.φ := by
  subst h
  have := Xo.smooth
  have hs : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨hr, -, hno⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s hs
  have e : a = a' := (F.rep _ _ _ _ hr hno inferInstance (fullObj_of_obj Xo.s Xo.univ β hβ)).unique
    ⟨ha, ν, hν⟩ ⟨ha', ν', hν'⟩
  subst e
  exact ⟨rfl, GlobalTheory.fullObj_rigid hL E H D n _ _ _ sM tM lev _ a ν ν' Xo.univ.etaA h3 hodd F.obj hr
    (charZero_residueField Xo.s) hν hν'⟩

/- English proof (translation)
Introduce `hH hL hL2 E _ _ _ H D Xo n N MM sM tM lev m C hD hn hN hm F hS`. Take `⟨U, hU, -⟩` from `C.good.1`. Take `⟨u, tU, mU, mM, hu, ufin, usurj, ⟨W₀, hW₀, hiso⟩, hj⟩` from `GlobalTheory.T.abelian_locus_open_family_over_level hH hL hL2 E H D n N MM sM tM lev m C U hn.1 (hN.imp fun _ h => h.2) hm F hU`. Take `⟨i, hio, hi, hi'⟩` from `exists_section u W₀`. Establish `hab` using `F.obj.proper`.

Establish `hft` using `BaseRing.finiteType_RZ H n N`. Establish `hnoeth : IsNoetherianRing (RZ H n N)` using `Algebra.FiniteType.isNoetherianRing ℤ _`. Establish `hodd : Odd N`. Take `⟨j, -, rfl⟩` from `hN`. Conclude with `hn.2.1.pow`.

Establish `h3 : 3 ≤ N`. Take `⟨j, hj, rfl⟩` from `hN`. Establish `h2` using `hn.1.two_le`. Take `⟨c, hc⟩` from `hn.2.1`. Conclude with `le_trans (by omega) (Nat.le_self_pow (by omega) n)`.

Establish `hgen : ∀ {l : Level H} (β : RZ H n N →+* KA l), Function.Injective β → ∀ {T : Scheme.{0}} (f : T ⟶ MM) (c : T ⟶ Sp (KA l)), f ≫ sM = c ≫ spMap β → Set.range f ⊆ Set.range W₀.ι`. Introduce and unpack `l β hβ T f c h _ ⟨x, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Use `hW₀ _ ?_` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]`.

Conclude with `asIdeal_spMap β hβ _`. Establish `key : ∀ l : Level H, l.A = N → ∃ (β : RZ H n N →+* KA l) (b : (Xo l).X ⟶ W₀.toScheme) (ν : SABMap (Xo l).univ.t tM (b ≫ W₀.ι)) (ν' : SABMap (Xo l).univ.t tU (b ≫ i)) (ν'' : SABMap (Xo l).univ.t C.t (b ≫ i ≫ U.ι)) (h : (b ≫ W₀.ι) ≫ sM = (Xo l).s ≫ spMap β), IsInc (RZ H n N).subtyp …`. Introduce `l h`. Take `⟨-, β, hβ, hinj, hfl⟩` from `exists_inc hn.1 hN l h`. Establish `hc : N.Coprime l.M`.

Take `⟨j, -, rfl⟩` from `hN`. Conclude with `((exists_two_auxiliary_inert_odd_primes_coprime_level E H).2 n hn l).pow_left j`. Take `⟨a, ν, ha, h₁, h₂, h₃⟩` from `GlobalTheory.T.moduli_finite_surjective_over_generic_family hL hL2 E H D n N MM sM tM lev l (Xo l) β h hn.1 hn.2.1 hN hc hβ F`. Take `⟨b, rfl⟩ : ∃ b, b ≫ W₀.ι = a` from `⟨_, IsOpenImmersion.lift_fac W₀.ι a (hgen β hinj a _ ha)⟩`. Take `⟨ν', hν'⟩` from `cancel_of_eq (g := b ≫ i) mM ν (by rw [Category.assoc, hi])`.

Take `⟨ν'', hν''⟩` from `comp_of_eq mU ν' (Category.assoc _ _ _)`. Conclude with `⟨β, b, ν, ν', ν'', ha, hβ, hinj, hfl, hν', hν'', h₁, h₂, h₃⟩`. Use `choose β b ν ν' ν'' hb hβ hinj hfl hν hν' hlev hfin hsurj using key`. Use `⟨{ Z := C.Z, s := C.s, normal := C.normal, proj := C.proj, flat := C.flat, t := C.t, qproj := C.qproj good := C.good, ga := genericPoints_subset C, a := fun l h => b l h ≫ i ≫ U.ι, m := ν'' fin := ?_, compat := ?_, sym := ?_, U := U, U_eq := hU, MM := MM, sM := sM, tM := tM, lev …` and prove the remaining obligations. Introduce `l h β' hβ'`.

Take `rfl` from `eq_of_isInc (hβ l h) hβ'`. Take `⟨f, hf⟩` from `exists_finite_lift U C.s sM (spMap (β l h)) u hu W₀.ι i hi hi' (hgen _ (hinj l h) _ _ pullback.condition) (b l h) (Xo l).s (hb l h) (hfin l h) (hsurj l h)`. Conclude with `⟨_, f, by rw [← hU]; rfl, hf⟩`. Introduce `l l' h h' r κ k hk hr hκ`. Establish `hkβ : k.comp (β l h) = β l' h'` using `eq_of_isInc (i := (RZ H n N).subtype) (fun x => (hk _).trans (hβ l h x)) (hβ l' h')`.

Take `⟨κ', hκ'⟩` from `comp_of_eq (ν l h) κ rfl`. Use `hfl l' h'` as an intermediate fact. Take `⟨e₁, e₂⟩` from `eq_of_level hL h3 hodd F h' (Xo l') (hβ l' h') κ' (ν l' h') (by rw [Category.assoc, hb, reassoc_of% hr, spMap_comp, hkβ]) (hb l' h') (fun x => by rw [hκ', reassoc_of% hκ x, hlev, Category.assoc r]) (hlev l' h')`. Establish `e₃ : r ≫ b l h = b l' h'` using `by rwa [← cancel_mono W₀.ι, Category.assoc]`. Use `⟨by rw [reassoc_of% e₃], ?_⟩` and prove the remaining obligations.

Establish `e₄ : κ.φ ≫ (ν' l h).φ = (ν' l' h').φ`. Apply `mM.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc]`. Conclude with `(congrArg (κ.φ ≫ ·) (hν l h).symm).trans (hκ'.symm.trans (e₂.trans (hν l' h')))`. Rewrite using `[Category.assoc, (ν' l h).cart.1.w, (ν' l' h').cart.1.w, reassoc_of% κ.cart.1.w, reassoc_of% e₃]`.

Rewrite using `[hν', hν', reassoc_of% e₄]`. Introduce `l h r κ g σ hσ hr hκ`. Take `⟨ρ, mu, σ₀, h₁, h₂, -⟩` from `GlobalTheory.T.fullLevelChange_acts_on_unitaryFamily hL hL2 E H D n N MM sM tM lev l (Xo l) (β l h) _ (ν l h) (hb l h) r κ g σ hD h hn.1 hn.2.1 hN (hβ l h) F (hsurj l h) (hlev l h) hσ hr hκ`. Take `⟨W', e₁, e₂, τ, hd, he, hτ⟩` from `exists_iso C hH (exists_inc hn.1 hN l h).1 hft ρ mu σ₀ h₂`. Take `⟨j', hj'⟩ : ∃ j', j' ≫ U.ι = C.j` from `⟨_, IsOpenImmersion.lift_fac U.ι C.j (by rw [Scheme.Opens.range_ι, hU]; exact range_j_subset C)⟩`.

Establish `hju` using `hj j' hj'`. Use `isSeparated C` as an intermediate fact. Use `isReduced_of_normal C.normal` as an intermediate fact. Rewrite `hd`, `hτ` using `[← hj']`. Use `⟨τ, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Category.assoc r.hom]`. Conclude with `comp_eq_of_dense U.ι u W₀.ι i hi hi' j' e₁ e₂ ρ (by rw [reassoc_of% hju, hju, he]) τ.hom hτ _ _ (by simpa only [Category.assoc] using h₁)`. Introduce `l h a' x y ha hy`. Establish `e : a' = b l h ≫ i` using `by rw [← cancel_mono U.ι, ha, Category.assoc]`. Establish `: Mono mU.φ` using `MorphismProperty.of_isPullback (P := .monomorphisms _) mU.cart.1.flip (inferInstanceAs (Mono U.ι))`.

Establish `e' : y = ((Xo l).univ.etaA x).left ≫ (ν' l h).φ`. Rewrite using `[← cancel_mono mU.φ, hy, hν', Category.assoc]`. Rewrite using `[e', Category.assoc, ← hν, hlev, e, Category.assoc, Category.assoc, reassoc_of% hi]`.
-/
theorem exists_top : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (m : ℕ) (C : ZOn sM tM m), 1 ≤ D.p + D.q → AuxiliaryInertOddPrime H n → (∃ j, 1 ≤ j ∧ N = n ^ j) → 0 < m → FamCore D sM tM lev → SiegClause D sM tM lev → ∃ T : Top Xo n N, Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L (m ^ 2)) := by
  intro hH hL hL2 E _ _ _ H D Xo n N MM sM tM lev m C hD hn hN hm F hS
  obtain ⟨U, hU, -⟩ := C.good.1
  obtain ⟨u, tU, mU, mM, hu, ufin, usurj, ⟨W₀, hW₀, hiso⟩, hj⟩ :=
    GlobalTheory.T.abelian_locus_open_family_over_level hH hL hL2 E H D n N MM sM tM lev m C U hn.1 (hN.imp fun _ h => h.2) hm F hU
  obtain ⟨i, hio, hi, hi'⟩ := exists_section u W₀
  have hab := F.obj.proper
  have hft := BaseRing.finiteType_RZ H n N
  have hnoeth : IsNoetherianRing (RZ H n N) := Algebra.FiniteType.isNoetherianRing ℤ _
  have hodd : Odd N := by
    obtain ⟨j, -, rfl⟩ := hN
    exact hn.2.1.pow
  have h3 : 3 ≤ N := by
    obtain ⟨j, hj, rfl⟩ := hN
    have h2 := hn.1.two_le
    obtain ⟨c, hc⟩ := hn.2.1
    exact le_trans (by omega) (Nat.le_self_pow (by omega) n)
  have hgen : ∀ {l : Level H} (β : RZ H n N →+* KA l), Function.Injective β → ∀ {T : Scheme.{0}} (f : T ⟶ MM)
      (c : T ⟶ Sp (KA l)), f ≫ sM = c ≫ spMap β → Set.range f ⊆ Set.range W₀.ι := by
    rintro l β hβ T f c h _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine hW₀ _ ?_
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
    exact asIdeal_spMap β hβ _
  have key : ∀ l : Level H, l.A = N → ∃ (β : RZ H n N →+* KA l) (b : (Xo l).X ⟶ W₀.toScheme)
      (ν : SABMap (Xo l).univ.t tM (b ≫ W₀.ι)) (ν' : SABMap (Xo l).univ.t tU (b ≫ i))
      (ν'' : SABMap (Xo l).univ.t C.t (b ≫ i ≫ U.ι)) (h : (b ≫ W₀.ι) ≫ sM = (Xo l).s ≫ spMap β),
      IsInc (RZ H n N).subtype (KA l).val.toRingHom β ∧ Function.Injective β ∧ Flat (spMap β) ∧
      ν.φ = ν'.φ ≫ mM.φ ∧ ν''.φ = ν'.φ ≫ mU.φ ∧
      (∀ x, ((Xo l).univ.etaA x).left ≫ ν.φ = (b ≫ W₀.ι) ≫ (lev x).left) ∧
      IsFinite (pullback.lift _ _ h) ∧ Surjective (pullback.lift _ _ h) := by
    intro l h
    obtain ⟨-, β, hβ, hinj, hfl⟩ := exists_inc hn.1 hN l h
    have hc : N.Coprime l.M := by
      obtain ⟨j, -, rfl⟩ := hN
      exact ((exists_two_auxiliary_inert_odd_primes_coprime_level E H).2 n hn l).pow_left j
    obtain ⟨a, ν, ha, h₁, h₂, h₃⟩ := GlobalTheory.T.moduli_finite_surjective_over_generic_family hL hL2 E H D n N MM sM tM lev l (Xo l) β h hn.1 hn.2.1 hN hc hβ F
    obtain ⟨b, rfl⟩ : ∃ b, b ≫ W₀.ι = a := ⟨_, IsOpenImmersion.lift_fac W₀.ι a (hgen β hinj a _ ha)⟩
    obtain ⟨ν', hν'⟩ := cancel_of_eq (g := b ≫ i) mM ν (by rw [Category.assoc, hi])
    obtain ⟨ν'', hν''⟩ := comp_of_eq mU ν' (Category.assoc _ _ _)
    exact ⟨β, b, ν, ν', ν'', ha, hβ, hinj, hfl, hν', hν'', h₁, h₂, h₃⟩
  choose β b ν ν' ν'' hb hβ hinj hfl hν hν' hlev hfin hsurj using key
  refine ⟨{
    Z := C.Z, s := C.s, normal := C.normal, proj := C.proj, flat := C.flat, t := C.t, qproj := C.qproj
    good := C.good, ga := genericPoints_subset C, a := fun l h => b l h ≫ i ≫ U.ι, m := ν''
    fin := ?_, compat := ?_, sym := ?_, U := U, U_eq := hU, MM := MM, sM := sM, tM := tM, lev := lev
    MM_red := F.red, MM_flat := F.flat, MM_ab := hab, u := u, u_over := hu, u_fin := ufin, u_surj := usurj
    u_gen := ⟨W₀, hW₀, hiso⟩, tU := tU, mU := mU, mM := mM, lev_eq := ?_, sieg := hS }, ⟨C.amp⟩⟩
  · intro l h β' hβ'
    obtain rfl := eq_of_isInc (hβ l h) hβ'
    obtain ⟨f, hf⟩ := exists_finite_lift U C.s sM (spMap (β l h)) u hu W₀.ι i hi hi'
      (hgen _ (hinj l h) _ _ pullback.condition) (b l h) (Xo l).s (hb l h) (hfin l h) (hsurj l h)
    exact ⟨_, f, by rw [← hU]; rfl, hf⟩
  · intro l l' h h' r κ k hk hr hκ
    have hkβ : k.comp (β l h) = β l' h' :=
      eq_of_isInc (i := (RZ H n N).subtype) (fun x => (hk _).trans (hβ l h x)) (hβ l' h')
    obtain ⟨κ', hκ'⟩ := comp_of_eq (ν l h) κ rfl
    have := hfl l' h'
    obtain ⟨e₁, e₂⟩ := eq_of_level hL h3 hodd F h' (Xo l') (hβ l' h') κ' (ν l' h')
      (by rw [Category.assoc, hb, reassoc_of% hr, spMap_comp, hkβ]) (hb l' h')
      (fun x => by rw [hκ', reassoc_of% hκ x, hlev, Category.assoc r]) (hlev l' h')
    have e₃ : r ≫ b l h = b l' h' := by rwa [← cancel_mono W₀.ι, Category.assoc]
    refine ⟨by rw [reassoc_of% e₃], ?_⟩
    have e₄ : κ.φ ≫ (ν' l h).φ = (ν' l' h').φ := by
      apply mM.cart.1.hom_ext
      · rw [Category.assoc]
        exact (congrArg (κ.φ ≫ ·) (hν l h).symm).trans (hκ'.symm.trans (e₂.trans (hν l' h')))
      · rw [Category.assoc, (ν' l h).cart.1.w, (ν' l' h').cart.1.w, reassoc_of% κ.cart.1.w, reassoc_of% e₃]
    rw [hν', hν', reassoc_of% e₄]
  · intro l h r κ g σ hσ hr hκ
    obtain ⟨ρ, mu, σ₀, h₁, h₂, -⟩ := GlobalTheory.T.fullLevelChange_acts_on_unitaryFamily hL hL2 E H D n N MM sM tM lev l (Xo l) (β l h) _ (ν l h) (hb l h) r κ g σ
      hD h hn.1 hn.2.1 hN (hβ l h) F (hsurj l h) (hlev l h) hσ hr hκ
    obtain ⟨W', e₁, e₂, τ, hd, he, hτ⟩ := exists_iso C hH (exists_inc hn.1 hN l h).1 hft ρ mu σ₀ h₂
    obtain ⟨j', hj'⟩ : ∃ j', j' ≫ U.ι = C.j :=
      ⟨_, IsOpenImmersion.lift_fac U.ι C.j (by rw [Scheme.Opens.range_ι, hU]; exact range_j_subset C)⟩
    have hju := hj j' hj'
    have := isSeparated C
    have := isReduced_of_normal C.normal
    rw [← hj'] at hd hτ
    refine ⟨τ, ?_⟩
    rw [← Category.assoc r.hom]
    exact comp_eq_of_dense U.ι u W₀.ι i hi hi' j' e₁ e₂ ρ (by rw [reassoc_of% hju, hju, he]) τ.hom hτ _ _
      (by simpa only [Category.assoc] using h₁)
  · intro l h a' x y ha hy
    have e : a' = b l h ≫ i := by rw [← cancel_mono U.ι, ha, Category.assoc]
    have : Mono mU.φ := MorphismProperty.of_isPullback (P := .monomorphisms _) mU.cart.1.flip
      (inferInstanceAs (Mono U.ι))
    have e' : y = ((Xo l).univ.etaA x).left ≫ (ν' l h).φ := by
      rw [← cancel_mono mU.φ, hy, hν', Category.assoc]
    rw [e', Category.assoc, ← hν, hlev, e, Category.assoc, Category.assoc, reassoc_of% hi]

end GlobalTheory.TopOfFamily
