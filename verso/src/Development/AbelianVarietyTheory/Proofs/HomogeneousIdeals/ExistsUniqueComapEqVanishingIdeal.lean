import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineHomOfIsPullbackSpecMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.MvPolynomialIsHomogeneousComapWeighted

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace GlobalTheory.QCoh.Qcqs

universe u

namespace GlobalTheory.GaloisDescent

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Introduce `x hx`. Establish `h1 : (I.subschemeι ≫ f).app U x = 0` using `(I.subschemeι ≫ f).ideal_ker_le U (Scheme.IdealSheafData.le_map_iff_comap_le.2 h U hx)`. Rewrite using `[Ideal.mem_comap, ← I.ker_subschemeι_app V, RingHom.mem_ker, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE, CommRingCat.comp_apply, h1, map_zero]`.
-/
theorem ideal_le_comap_appLE {X Y : Scheme.{u}} (f : Y ⟶ X) {J : X.IdealSheafData}
    {I : Y.IdealSheafData} (h : J.comap f ≤ I) (U : X.affineOpens) (V : Y.affineOpens)
    (e : V.1 ≤ f ⁻¹ᵁ U.1) : J.ideal U ≤ (I.ideal V).comap (f.appLE U V e).hom := by
  intro x hx
  have h1 : (I.subschemeι ≫ f).app U x = 0 :=
    (I.subschemeι ≫ f).ideal_ker_le U (Scheme.IdealSheafData.le_map_iff_comap_le.2 h U hx)
  rw [Ideal.mem_comap, ← I.ker_subschemeι_app V, RingHom.mem_ker, Scheme.Hom.app_eq_appLE,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE,
    CommRingCat.comp_apply, h1, map_zero]

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {X Y : Scheme.{u}}
  {p : X ⟶ Spec (.of K)} {q : Y ⟶ Spec (.of L)} {π : Y ⟶ X}
  (H : IsPullback π q p (Spec.map (CommRingCat.ofHom (algebraMap K L)))) {G : Type*}

include H

/- English proof (translation)
Establish `po` using `(isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := π ⁻¹ᵁ U) le_top le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hU)`. Use `po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _) ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using `[baseRingHom]`. Rewrite using `[← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression.

Simplify using `[Scheme.Hom.app_eq_appLE]`. Simplify using `[baseRingHom]`.
-/
theorem isPushout_app {U : X.Opens} (hU : IsAffineOpen U) :
    IsPushout (baseRingHom p U) (CommRingCat.ofHom (algebraMap K L)) (π.app U)
      (baseRingHom q (π ⁻¹ᵁ U)) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := π ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [baseRingHom]
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · simp [baseRingHom]

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Establish `: IsAffineHom π` using `MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance`. Use `le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_` and prove the remaining obligations. Use `Scheme.IdealSheafData.le_of_iSup_eq_top (fun U : X.affineOpens => ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) ?_ fun U => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `⨆ U : X.affineOpens, π ⁻¹ᵁ U.1 = ⊤`. Rewrite using `[← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]`.

Set `` to `(π.app U).hom.toAlgebra`. Set `` to `(baseRingHom p U).hom.toAlgebra`. Set `` to `(baseRingHom q (π ⁻¹ᵁ U)).hom.toAlgebra`. Set `` to `(baseRingHom (π ≫ p) (π ⁻¹ᵁ U)).hom.toAlgebra`. Establish `: IsScalarTower K Γ(X, U) Γ(Y, π ⁻¹ᵁ U)` using `.of_algebraMap_eq fun r ↦ (app_baseRingHom π p U r).symm`.

Establish `: IsScalarTower K L Γ(Y, π ⁻¹ᵁ U)` using `.of_algebraMap_eq fun r ↦ (baseRingHom_algebraMap (R := .of K) (L := .of L) H _ r).symm`. Establish `hpo : Algebra.IsPushout K Γ(X, U) L Γ(Y, π ⁻¹ᵁ U)` using `CommRingCat.isPushout_iff_isPushout.mp (isPushout_app H U.2)`. Establish `e : ∀ g, π ⁻¹ᵁ U.1 ≤ a g ⁻¹ᵁ (π ⁻¹ᵁ U.1)` using `fun g => by`. Rewrite using `[← Scheme.Hom.comp_preimage, haπ]`. Establish `h1 : ∀ g, π.app U ≫ (a g).appLE _ _ (e g) = π.app U` using `fun g => by`.

Simplify using `only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, haπ]`. Establish `h2 : ∀ g, baseRingHom q (π ⁻¹ᵁ U) ≫ (a g).appLE _ _ (e g) = CommRingCat.ofHom (s g) ≫ baseRingHom q (π ⁻¹ᵁ U)` using `fun g => by`. Rewrite using `[← baseRingHom_comp_SpecMap, ← haq]`. Simplify using `only [baseRingHom, Category.assoc, Scheme.Hom.appLE_comp_appLE]`. Establish `key` using `ideal_map_comap_of_stable hpo.symm.out s hs (fun g => ((a g).appLE _ _ (e g)).hom.toAddMonoidHom) (fun g l x => by`.

Establish `h3` using `congr($(h1 g) x)`. Establish `h4` using `congr($(h2 g) l)`. Express the relevant statement in the definitionally equal form `(a g).appLE _ _ (e g) (baseRingHom q (π ⁻¹ᵁ U) l * π.app U x) = baseRingHom q (π ⁻¹ᵁ U) (s g l) * π.app U x`. Rewrite using `[map_mul]`. Conclude with `congrArg₂ (· * ·) h4 h3)`.

Use the proof step `(I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩)`. Use the proof step `(fun g x hx => ideal_le_comap_appLE (a g) (hI g) ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩ ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩ (e g) hx)`. Rewrite using `[← key, Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Establish `h5` using `ideal_le_comap_appLE π (le_refl ((I.map π).comap π)) U ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩ le_rfl (x := x) (by rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom]; exact hx)`.

Rewrite `h5` using `[← Scheme.Hom.app_eq_appLE]`. Conclude with `h5`.
-/
theorem idealSheaf_comap_map_of_stable (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (a : G → (Y ⟶ Y)) (haπ : ∀ g, a g ≫ π = π)
    (haq : ∀ g, a g ≫ q = q ≫ Spec.map (CommRingCat.ofHom (s g)))
    (I : Y.IdealSheafData) (hI : ∀ g, I.comap (a g) ≤ I) : (I.map π).comap π = I := by
  have : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun U : X.affineOpens => ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) ?_ fun U => ?_
  · change ⨆ U : X.affineOpens, π ⁻¹ᵁ U.1 = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  · let := (π.app U).hom.toAlgebra
    let := (baseRingHom p U).hom.toAlgebra
    let := (baseRingHom q (π ⁻¹ᵁ U)).hom.toAlgebra
    let := (baseRingHom (π ≫ p) (π ⁻¹ᵁ U)).hom.toAlgebra
    have : IsScalarTower K Γ(X, U) Γ(Y, π ⁻¹ᵁ U) :=
      .of_algebraMap_eq fun r ↦ (app_baseRingHom π p U r).symm
    have : IsScalarTower K L Γ(Y, π ⁻¹ᵁ U) :=
      .of_algebraMap_eq fun r ↦ (baseRingHom_algebraMap (R := .of K) (L := .of L) H _ r).symm
    have hpo : Algebra.IsPushout K Γ(X, U) L Γ(Y, π ⁻¹ᵁ U) :=
      CommRingCat.isPushout_iff_isPushout.mp (isPushout_app H U.2)
    have e : ∀ g, π ⁻¹ᵁ U.1 ≤ a g ⁻¹ᵁ (π ⁻¹ᵁ U.1) := fun g => by
      rw [← Scheme.Hom.comp_preimage, haπ]
    have h1 : ∀ g, π.app U ≫ (a g).appLE _ _ (e g) = π.app U := fun g => by
      simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, haπ]
    have h2 : ∀ g, baseRingHom q (π ⁻¹ᵁ U) ≫ (a g).appLE _ _ (e g) =
        CommRingCat.ofHom (s g) ≫ baseRingHom q (π ⁻¹ᵁ U) := fun g => by
      rw [← baseRingHom_comp_SpecMap, ← haq]
      simp only [baseRingHom, Category.assoc, Scheme.Hom.appLE_comp_appLE]
    have key := ideal_map_comap_of_stable hpo.symm.out s hs
      (fun g => ((a g).appLE _ _ (e g)).hom.toAddMonoidHom) (fun g l x => by
        have h3 := congr($(h1 g) x)
        have h4 := congr($(h2 g) l)
        change (a g).appLE _ _ (e g) (baseRingHom q (π ⁻¹ᵁ U) l * π.app U x) =
          baseRingHom q (π ⁻¹ᵁ U) (s g l) * π.app U x
        rw [map_mul]
        exact congrArg₂ (· * ·) h4 h3)
      (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩)
      (fun g x hx => ideal_le_comap_appLE (a g) (hI g) ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩
        ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩ (e g) hx)
    rw [← key, Ideal.map_le_iff_le_comap]
    intro x hx
    have h5 := ideal_le_comap_appLE π (le_refl ((I.map π).comap π)) U
      ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩ le_rfl (x := x)
      (by rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom]; exact hx)
    rw [← Scheme.Hom.app_eq_appLE] at h5
    exact h5

/- English proof (translation)
Establish `: IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap K L)))` using `.of_isDominant _`. Establish `h : IsSchemeTheoreticallyDominant (pullback.snd π J.subschemeι)` using `.of_isPullback ((IsPullback.of_hasPullback π J.subschemeι).flip.paste_vert H).flip`. Rewrite using `[Scheme.IdealSheafData.comap, Scheme.IdealSheafData.map_ker, pullback.condition, Scheme.Hom.ker_comp, h.ker_eq_bot, Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]`.
-/
theorem idealSheaf_map_comap (J : X.IdealSheafData) : (J.comap π).map π = J := by
  have : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    .of_isDominant _
  have h : IsSchemeTheoreticallyDominant (pullback.snd π J.subschemeι) :=
    .of_isPullback ((IsPullback.of_hasPullback π J.subschemeι).flip.paste_vert H).flip
  rw [Scheme.IdealSheafData.comap, Scheme.IdealSheafData.map_ker, pullback.condition,
    Scheme.Hom.ker_comp, h.ker_eq_bot, Scheme.IdealSheafData.map_bot,
    Scheme.IdealSheafData.ker_subschemeι]

/- English proof (translation)
Introduce `J J' h` and use `by rw [← idealSheaf_map_comap H J, ← idealSheaf_map_comap H J'] exact congrArg (·.map π) h`.
-/
theorem idealSheaf_comap_injective :
    Function.Injective fun J : X.IdealSheafData => J.comap π := fun J J' h => by
  rw [← idealSheaf_map_comap H J, ← idealSheaf_map_comap H J']
  exact congrArg (·.map π) h

noncomputable def twist (σ : L →ₐ[K] L) : Y ⟶ Y :=
  H.lift π (q ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
    rw [H.w, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact σ.comp_algebraMap.symm)

@[reassoc (attr := simp)]
/- English proof (translation)
The claim follows from `H.lift_fst _ _ _ @[reassoc (attr := simp)]`.
-/
theorem twist_fst (σ : L →ₐ[K] L) : twist H σ ≫ π = π := H.lift_fst _ _ _

@[reassoc (attr := simp)]
/- English proof (translation)
The claim follows from `H.lift_snd _ _ _ @[simp]`.
-/
theorem twist_snd (σ : L →ₐ[K] L) :
    twist H σ ≫ q = q ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := H.lift_snd _ _ _

@[simp]
/- English proof (translation)
Apply `H.hom_ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Rewrite using `[twist_snd, Category.id_comp]`. Conclude with `(congrArg (q ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)`.
-/
theorem twist_id : twist H (AlgHom.id K L) = 𝟙 Y := by
  apply H.hom_ext
  · simp
  · rw [twist_snd, Category.id_comp]
    exact (congrArg (q ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)

/- English proof (translation)
Apply `H.hom_ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Rewrite using `[twist_snd, Category.assoc, twist_snd, twist_snd_assoc, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem twist_comp (σ τ : L →ₐ[K] L) : twist H (σ.comp τ) = twist H σ ≫ twist H τ := by
  apply H.hom_ext
  · simp
  · rw [twist_snd, Category.assoc, twist_snd, twist_snd_assoc, ← Spec.map_comp]
    rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hI`. Establish `h1` using `idealSheaf_comap_map_of_stable H (fun g => (s g).toRingHom) hs (fun g => twist H (s g)) (fun g => twist_fst H _) (fun g => twist_snd H _) I hI`. Conclude with `⟨_, h1, fun J hJ => idealSheaf_comap_injective H (hJ.trans h1.symm)⟩`. Introduce and unpack `⟨J, rfl, -⟩ g`.

Rewrite using `[← Scheme.IdealSheafData.comap_comp, twist_fst]`.
-/
theorem idealSheaf_stable_iff_exists_comap (s : G → L →ₐ[K] L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L)) (I : Y.IdealSheafData) :
    (∀ g, I.comap (twist H (s g)) ≤ I) ↔ ∃! J : X.IdealSheafData, J.comap π = I := by
  constructor
  · intro hI
    have h1 := idealSheaf_comap_map_of_stable H (fun g => (s g).toRingHom) hs
      (fun g => twist H (s g)) (fun g => twist_fst H _) (fun g => twist_snd H _) I hI
    exact ⟨_, h1, fun J hJ => idealSheaf_comap_injective H (hJ.trans h1.symm)⟩
  · rintro ⟨J, rfl, -⟩ g
    rw [← Scheme.IdealSheafData.comap_comp, twist_fst]

/- English proof (translation)
Use `(idealSheaf_stable_iff_exists_comap H s hs _).1 fun g => ?_` and prove the remaining obligations. Rewrite using `[← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal, Scheme.IdealSheafData.support_comap]`. Introduce `y hy`. Express the relevant statement in the definitionally equal form `twist H (s g) y ∈ ((Scheme.IdealSheafData.vanishingIdeal Z).support : Set Y)`. Rewrite using `[Scheme.IdealSheafData.coe_support_vanishingIdeal]`.

Conclude with `hZ g y hy`.
-/
theorem existsUnique_comap_eq_vanishingIdeal (s : G → L →ₐ[K] L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L)) (Z : Closeds Y)
    (hZ : ∀ g, ∀ y ∈ Z, twist H (s g) y ∈ Z) :
    ∃! J : X.IdealSheafData, J.comap π = Scheme.IdealSheafData.vanishingIdeal Z := by
  refine (idealSheaf_stable_iff_exists_comap H s hs _).1 fun g => ?_
  rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
    Scheme.IdealSheafData.support_comap]
  intro y hy
  change twist H (s g) y ∈ ((Scheme.IdealSheafData.vanishingIdeal Z).support : Set Y)
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact hZ g y hy

end GlobalTheory.GaloisDescent
