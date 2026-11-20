import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleKernelFlatOfFiniteNoetherianLocal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatOfIsFiniteOfFlatLocalizationMaximal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjRestrictSnd
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubeProjectiveAbelianSchemeAffineBase
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionFibreOverPointToBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorsFibreOverPointIffFactorsProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleFamilyAtPointLambdaTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationDifferenceTrivialBaseChangeIffOverAStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoFamilyIffLocallyTrivialTranslatiStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat
open GlobalTheory.StabFlatLocal GlobalTheory.StabFlat GlobalTheory.UU

/- English proof (translation)
Introduce `hG V _ _ _ B _ _ hB hp L hL hΘ O hO hu H j hj hH hf`. Take `⟨g, hg⟩` from `GlobalTheory.AbelianDim.exists_relDim V B hB`. Rewrite using `[← Over.w j]`. Use `GlobalTheory.T.flat_closedSubscheme_finite_over_localRing V B.left H.left B.hom j.left hj (by rw [Over.w j]; exact hf) fun h σ hσ hn => ?_` and prove the remaining obligations. Establish `cl : ∀ (z : H.left) (p : Spec (B.left.presheaf.stalk (j.left h))), (IsLocalRing.maximalIdeal V).map σ ≤ p.asIdeal → j.left z = B.left.fromSpecStalk (j.left h) p → IsClosed ({j.left z} : Set B.left)`.

Introduce `z p hp e`. Establish `hz : H.hom z = IsLocalRing.closedPoint V`. Rewrite using `[← Over.w j, Scheme.Hom.comp_apply, e, ← Scheme.Hom.comp_apply, hσ]`. Use `PrimeSpectrum.ext (Eq.symm ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le (PrimeSpectrum.isPrime _).ne_top ?_))` and prove the remaining obligations. Conclude with `Ideal.map_le_iff_le_comap.1 hp`.

Use `j.left.isClosedEmbedding.isClosedMap _ (isClosed_of_isFinite H.hom z hz)` as an intermediate fact. Rewrite `this` using `[Set.image_singleton]`. Then use the resulting hypothesis. Establish `hm : (IsLocalRing.maximalIdeal V).map σ ≤ IsLocalRing.maximalIdeal _` using `Ideal.map_le_iff_le_comap.2 fun v hv => map_nonunit σ v hv`. Take `⟨h₀, h₁, h₂, h₃⟩` from `GlobalTheory.T.stalk_regular_flat_of_smooth V B.left B.hom g hg (j.left h) (cl h (IsLocalRing.closedPoint _) hm Scheme.fromSpecStalk_closedPoint.symm) σ hσ hn`. Use `@exists_ideal hG V _ _ _ B _ _ hB hp g hg L O hL hO hΘ hu H j hH (B.left.presheaf.stalk (j.left h)) _ h₀ _ (B.left.fromSpecStalk (j.left h)) σ hn h₁ h₂ h₃ (H.left.residueField h) _ (j.left.stalkMap h ≫ H.left.residue h).hom (RingHom.isLocalHom_comp (IsLocalRing.residue (H.left.pr …` and prove the remaining obligations.

Rewrite using `[Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc]`. Both sides reduce to the same expression. Introduce and unpack `K _ φ hφ ⟨y, hy⟩`. Set `p` to `Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint K)`. Establish `hk : p.asIdeal = RingHom.ker φ` using `by show Ideal.comap φ (IsLocalRing.maximalIdeal K) = _`.

Rewrite using `[IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]`. Establish `e : j.left (y (IsLocalRing.closedPoint K)) = B.left.fromSpecStalk (j.left h) p` using `congrArg (fun q => q (IsLocalRing.closedPoint K)) hy`. Establish `hc` using `cl _ p (hφ.trans hk.ge) e`. Establish `hs : B.left.fromSpecStalk (j.left h) p ⤳ j.left h`. Establish `: B.left.fromSpecStalk (j.left h) p ∈ Set.range (B.left.fromSpecStalk (j.left h))` using `⟨p, rfl⟩`.

Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Then use the resulting hypothesis. Establish `e' : j.left h = B.left.fromSpecStalk (j.left h) p` using `(hs.mem_closed hc e.symm).trans e`. Establish `hp' : p = IsLocalRing.closedPoint _` using `(B.left.fromSpecStalk (j.left h)).isEmbedding.injective (e'.symm.trans Scheme.fromSpecStalk_closedPoint.symm)`. Rewrite using `[← hk, hp']`. Both sides reduce to the same expression.
-/
theorem flat_of_isFinite_twist : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V]
    (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ L : LB B.left, L.IsLB →
    (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ O : LB B.left, O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) →
    ∀ (H : Over (Sp V)) (j : H ⟶ B), IsClosedImmersion j.left →
    (∀ (T : Over (Sp V)) (x : T ⟶ B), (∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) ↔
        ∃ y : T ⟶ H, y ≫ j = x) → IsFinite H.hom → Flat H.hom := by
  intro hG V _ _ _ B _ _ hB hp L hL hΘ O hO hu H j hj hH hf
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim V B hB
  rw [← Over.w j]
  refine GlobalTheory.T.flat_closedSubscheme_finite_over_localRing V B.left H.left B.hom j.left hj (by rw [Over.w j]; exact hf) fun h σ hσ hn => ?_
  have cl : ∀ (z : H.left) (p : Spec (B.left.presheaf.stalk (j.left h))),
      (IsLocalRing.maximalIdeal V).map σ ≤ p.asIdeal →
      j.left z = B.left.fromSpecStalk (j.left h) p → IsClosed ({j.left z} : Set B.left) := by
    intro z p hp e
    have hz : H.hom z = IsLocalRing.closedPoint V := by
      rw [← Over.w j, Scheme.Hom.comp_apply, e, ← Scheme.Hom.comp_apply, hσ]
      refine PrimeSpectrum.ext (Eq.symm ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le
        (PrimeSpectrum.isPrime _).ne_top ?_))
      exact Ideal.map_le_iff_le_comap.1 hp
    have := j.left.isClosedEmbedding.isClosedMap _ (isClosed_of_isFinite H.hom z hz)
    rwa [Set.image_singleton] at this
  have hm : (IsLocalRing.maximalIdeal V).map σ ≤ IsLocalRing.maximalIdeal _ :=
    Ideal.map_le_iff_le_comap.2 fun v hv => map_nonunit σ v hv
  obtain ⟨h₀, h₁, h₂, h₃⟩ := GlobalTheory.T.stalk_regular_flat_of_smooth V B.left B.hom g hg (j.left h)
    (cl h (IsLocalRing.closedPoint _) hm Scheme.fromSpecStalk_closedPoint.symm) σ hσ hn
  refine @exists_ideal hG V _ _ _ B _ _ hB hp g hg L O hL hO hΘ hu H j hH
    (B.left.presheaf.stalk (j.left h)) _ h₀ _
    (B.left.fromSpecStalk (j.left h)) σ hn h₁ h₂ h₃ (H.left.residueField h) _
    (j.left.stalkMap h ≫ H.left.residue h).hom
    (RingHom.isLocalHom_comp (IsLocalRing.residue (H.left.presheaf.stalk h)) (j.left.stalkMap h).hom) ⟨H.left.fromSpecResidueField h, ?_⟩ ?_
  · rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc]
    rfl
  · rintro K _ φ hφ ⟨y, hy⟩
    let p := Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint K)
    have hk : p.asIdeal = RingHom.ker φ := by
      show Ideal.comap φ (IsLocalRing.maximalIdeal K) = _
      rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]
    have e : j.left (y (IsLocalRing.closedPoint K)) = B.left.fromSpecStalk (j.left h) p :=
      congrArg (fun q => q (IsLocalRing.closedPoint K)) hy
    have hc := cl _ p (hφ.trans hk.ge) e
    have hs : B.left.fromSpecStalk (j.left h) p ⤳ j.left h := by
      have : B.left.fromSpecStalk (j.left h) p ∈ Set.range (B.left.fromSpecStalk (j.left h)) := ⟨p, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have e' : j.left h = B.left.fromSpecStalk (j.left h) p := (hs.mem_closed hc e.symm).trans e
    have hp' : p = IsLocalRing.closedPoint _ := (B.left.fromSpecStalk (j.left h)).isEmbedding.injective
      (e'.symm.trans Scheme.fromSpecStalk_closedPoint.symm)
    rw [← hk, hp']
    rfl

end GlobalTheory.TwistFlat

namespace GlobalTheory.TwistFlat

/- English proof (translation)
Introduce `R _ A _ hA L hL ha T N hN H h hh hH V _ _ _ φ hfin`. Establish `hB : IsAbelianScheme (bc A φ)` using `GlobalTheory.isAbelianScheme_pullback_obj _ A hA`. Establish `: IsCommMonObj (bc A φ)` using `hB.comm`. Establish `hP : IsProjBy (bc A φ).hom` using `(GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ A L hA hL ha V (φ ≫ T.hom) _ (pullback.fst A.hom (φ ≫ T.hom)) (pullback.snd A.hom (φ ≫ T.hom)) (IsPullback.of_hasPullback _ _)).1`. Establish `hL' : (L.pull (pullback.fst A.hom (φ ≫ T.hom))).IsLB` using `LB.isLB_pull hL _`.

Establish `hO : (twist A φ N).IsLB` using `pull_isLB hN.isLB _`. Use `flat_of_isFinite_twist GlobalTheory.T.abelianScheme_laws_unconditional.1.globalFns V (bc A φ) hB hP _ hL' (GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy GlobalTheory.T.abelianScheme_laws_unconditional.1 _ _ hB hP _ hL') (twist A φ N) hO (GlobalTheory.T.lineBundleFamilyAtPo …` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.factors_fibreOverPoint_iff_factors_product A φ h Y x, ← hH, GlobalTheory.T.mumfordBundle_iso_family_iff_locally_trivial_translationDiff A T hA L hL N hN]`. Conclude with `forall_congr' fun p => exists_congr fun U => and_congr_right' (GlobalTheory.T.translationDifference_trivial_baseChange_iff_over_A A φ L hL N hN.isLB Y x U)`.
-/
theorem flat_local : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left,
    L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left), Fam A N →
    ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left →
    (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) →
    ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (φ : Sp V ⟶ T.left),
    IsFinite (pullback.snd (h ≫ snd A T).left φ) → Flat (pullback.snd (h ≫ snd A T).left φ) := by
  intro R _ A _ hA L hL ha T N hN H h hh hH V _ _ _ φ hfin
  have hB : IsAbelianScheme (bc A φ) := GlobalTheory.isAbelianScheme_pullback_obj _ A hA
  have : IsCommMonObj (bc A φ) := hB.comm
  have hP : IsProjBy (bc A φ).hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ A L hA hL ha V (φ ≫ T.hom)
      _ (pullback.fst A.hom (φ ≫ T.hom)) (pullback.snd A.hom (φ ≫ T.hom)) (IsPullback.of_hasPullback _ _)).1
  have hL' : (L.pull (pullback.fst A.hom (φ ≫ T.hom))).IsLB := LB.isLB_pull hL _
  have hO : (twist A φ N).IsLB := pull_isLB hN.isLB _
  refine flat_of_isFinite_twist GlobalTheory.T.abelianScheme_laws_unconditional.1.globalFns V (bc A φ) hB hP _ hL'
    (GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy GlobalTheory.T.abelianScheme_laws_unconditional.1 _ _ hB hP _ hL') (twist A φ N) hO
    (GlobalTheory.T.lineBundleFamilyAtPoint_lambda_trivial A φ N hN) (ker A φ h) (kerι A φ h) (GlobalTheory.T.isClosedImmersion_fibreOverPointToBaseChange A φ h hh) (fun Y x => ?_) hfin
  rw [GlobalTheory.T.factors_fibreOverPoint_iff_factors_product A φ h Y x, ← hH, GlobalTheory.T.mumfordBundle_iso_family_iff_locally_trivial_translationDiff A T hA L hL N hN]
  exact forall_congr' fun p => exists_congr fun U => and_congr_right' (GlobalTheory.T.translationDifference_trivial_baseChange_iff_over_A A φ L hL N hN.isLB Y x U)

end GlobalTheory.TwistFlat

namespace GlobalTheory.TwistFlat

/- English proof (translation)
Establish `h1 : (f.appTop).hom.FiniteType` using `(HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).1 hf`. Establish `: IsNoetherianRing Γ(Sp R, ⊤)` using `isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv`. Use `letI := (f.appTop).hom.toAlgebra`. Establish `: Algebra.FiniteType Γ(Sp R, ⊤) Γ(X, ⊤)` using `h1`. Conclude with `Algebra.FiniteType.isNoetherianRing Γ(Sp R, ⊤) Γ(X, ⊤)`.
-/
theorem isNoetherianRing_top (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) [IsAffine X]
    (f : X ⟶ Sp R) (hf : LocallyOfFiniteType f) : IsNoetherianRing Γ(X, ⊤) := by
  have h1 : (f.appTop).hom.FiniteType := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).1 hf
  have : IsNoetherianRing Γ(Sp R, ⊤) :=
    isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  letI := (f.appTop).hom.toAlgebra
  have : Algebra.FiniteType Γ(Sp R, ⊤) Γ(X, ⊤) := h1
  exact Algebra.FiniteType.isNoetherianRing Γ(Sp R, ⊤) Γ(X, ⊤)

/- English proof (translation)
Introduce `R _ _ A _ hA L hL ha T _ hT N hN H h hh hH hfin`. Establish `: IsNoetherianRing Γ(T.left, ⊤)` using `isNoetherianRing_top R T.left T.hom hT`. Set `e` to `T.left.isoSpec`. Set `f` to `(h ≫ snd A T).left`. Use `haveI : IsFinite f := hfin`.

Set `H' : Over (Sp Γ(T.left, ⊤))` to `Over.mk (f ≫ e.hom)`. Establish `hfin' : IsFinite H'.hom` using `by show IsFinite (f ≫ e.hom) infer_instance`. Establish `hflat : Flat (f ≫ e.hom)`. Use `GlobalTheory.flat_of_isFinite_of_flat_localization_maximal Γ(T.left, ⊤) H' hfin' fun m _ => ?_` and prove the remaining obligations. Set `φ : Sp (Localization.AtPrime m) ⟶ T.left` to `spMap (algebraMap Γ(T.left, ⊤) (Localization.AtPrime m)) ≫ e.inv`.

Establish `hf : IsFinite (pullback.snd f φ)` using `MorphismProperty.of_isPullback (P := @IsFinite) (IsPullback.of_hasPullback f φ) hfin`. Use `haveI := flat_local R A hA L hL ha T N hN H h hh hH (Localization.AtPrime m) φ hf`. Establish `sq : IsPullback (pullback.fst f φ) (pullback.snd f φ) (f ≫ e.hom) (spMap (algebraMap Γ(T.left, ⊤) (Localization.AtPrime m)))` using `(IsPullback.of_hasPullback f φ).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp) (by simp) (by simp [φ])`. Use `show Flat (pullback.snd (f ≫ e.hom) _)`. Rewrite using `[← sq.isoPullback_inv_snd]`.

Use `infer_instance`. Establish `hfe : f = (f ≫ e.hom) ≫ e.inv` using `by simp`. Use `show Flat f`. Rewrite using `[hfe]`. Use `infer_instance`.
-/
theorem flat_twisted_kernel : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → IsFinite (h ≫ snd A T).left → Flat (h ≫ snd A T).left := by
  intro R _ _ A _ hA L hL ha T _ hT N hN H h hh hH hfin
  have : IsNoetherianRing Γ(T.left, ⊤) := isNoetherianRing_top R T.left T.hom hT
  let e := T.left.isoSpec
  let f := (h ≫ snd A T).left
  haveI : IsFinite f := hfin
  let H' : Over (Sp Γ(T.left, ⊤)) := Over.mk (f ≫ e.hom)
  have hfin' : IsFinite H'.hom := by
    show IsFinite (f ≫ e.hom)
    infer_instance
  have hflat : Flat (f ≫ e.hom) := by
    refine GlobalTheory.flat_of_isFinite_of_flat_localization_maximal Γ(T.left, ⊤) H' hfin' fun m _ => ?_
    let φ : Sp (Localization.AtPrime m) ⟶ T.left := spMap (algebraMap Γ(T.left, ⊤) (Localization.AtPrime m)) ≫ e.inv
    have hf : IsFinite (pullback.snd f φ) := MorphismProperty.of_isPullback (P := @IsFinite) (IsPullback.of_hasPullback f φ) hfin
    haveI := flat_local R A hA L hL ha T N hN H h hh hH (Localization.AtPrime m) φ hf
    have sq : IsPullback (pullback.fst f φ) (pullback.snd f φ) (f ≫ e.hom)
        (spMap (algebraMap Γ(T.left, ⊤) (Localization.AtPrime m))) :=
      (IsPullback.of_hasPullback f φ).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp)
        (by simp) (by simp [φ])
    show Flat (pullback.snd (f ≫ e.hom) _)
    rw [← sq.isoPullback_inv_snd]
    infer_instance
  have hfe : f = (f ≫ e.hom) ≫ e.inv := by simp
  show Flat f
  rw [hfe]
  infer_instance

end GlobalTheory.TwistFlat
