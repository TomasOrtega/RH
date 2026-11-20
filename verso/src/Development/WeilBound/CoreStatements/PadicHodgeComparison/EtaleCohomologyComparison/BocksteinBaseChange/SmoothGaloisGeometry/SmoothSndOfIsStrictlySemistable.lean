import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableModel

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace CrystallineSemistableComparison

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `: IsZariskiLocalAtSource @Smooth.{0}` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Use `set j := Spec.map (CommRingCat.ofHom (algebraMap O K))`. Establish `hgen` using `IsPullback.of_hasPullback p j`. Use `choose W hW hxW m r h1 h2 ψ hψe hψ using hss`. Use `IsZariskiLocalAtSource.of_iSup_eq_top (fun x : X ↦ (pullback.fst p j) ⁻¹ᵁ W x) ?_ ?_` and prove the remaining obligations.

Rewrite using `[eq_top_iff]`. Introduce `z _`. Rewrite using `[TopologicalSpace.Opens.mem_iSup]`. Conclude with `⟨pullback.fst p j z, hxW _⟩`. Introduce `x`.

Use `set B := GlobalTheory.Et.ssModel O ϖ (m x) (r x)`. Use `set s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom (algebraMap O B))`. Use `set φ : (W x).toScheme ⟶ Spec (CommRingCat.of B) := (hW x).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (ψ x))`. Establish `hφ : (W x).ι ≫ p = φ ≫ s`. Establish `e1 : (W x).ι = (hW x).isoSpec.hom ≫ (hW x).fromSpec`.

Rewrite using `[← (hW x).isoSpec_inv_ι, Iso.hom_inv_id_assoc]`. Establish `e2` using `IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top (Spec (CommRingCat.of O))) (hW x) le_top`. Rewrite using `[e1, Category.assoc, ← e2]`. Simplify using `only [φ, s, Category.assoc, ← Spec.map_comp]`. Use `congr 2`.

Rewrite using `[IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]`. Use `congr 1`. Apply `CommRingCat.hom_ext` to reduce the goal to its premises. Conclude with `(hψ x).symm`. Use `set Bϖ := Localization.Away (algebraMap O B ϖ)`.

Use `set σ : K →+* Bϖ := IsLocalization.Away.map K Bϖ (algebraMap O B) ϖ`. Establish `hH : σ.comp (algebraMap O K) = (algebraMap B Bϖ).comp (algebraMap O B)`. Simplify using `only [σ, IsLocalization.Away.map]`. Conclude with `IsLocalization.map_comp _`. Establish `: IsLocalization ((Submonoid.powers ϖ).map (algebraMap O B)) Bϖ`.

Rewrite using `[Submonoid.map_powers]`. Use `infer_instance`. Establish `hpush` using `CommRingCat.isPushout_of_isLocalization (algebraMap O B) σ hH (Submonoid.powers ϖ)`. Establish `hbot` using `isPullback_SpecMap_of_isPushout _ _ _ _ hpush`. Establish `hout` using `(isPullback_morphismRestrict (pullback.fst p j) (W x)).paste_vert hgen`.

Rewrite `hout` using `[hφ]`. Establish `hw : ((pullback.fst p j ∣_ W x) ≫ φ) ≫ s = (((pullback.fst p j) ⁻¹ᵁ W x).ι ≫ pullback.snd p j) ≫ j`. Rewrite using `[Category.assoc]`. Conclude with `hout.w`. Use `set t := hbot.lift _ _ hw`.

Establish `ht1 : t ≫ Spec.map (CommRingCat.ofHom (algebraMap B Bϖ)) = (pullback.fst p j ∣_ W x) ≫ φ` using `hbot.lift_fst _ _ hw`. Establish `ht2 : t ≫ Spec.map (CommRingCat.ofHom σ) = ((pullback.fst p j) ⁻¹ᵁ W x).ι ≫ pullback.snd p j` using `hbot.lift_snd _ _ hw`. Rewrite `hout` using `[← ht2]`. Establish `hleft` using `IsPullback.of_bot hout ht1.symm hbot`. Establish `: Etale (Spec.map (CommRingCat.ofHom (ψ x)))` using `HasRingHomProperty.Spec_iff.mpr (hψe x)`.

Establish `: Etale φ` using `inferInstance`. Establish `: Etale t` using `MorphismProperty.of_isPullback hleft ‹Etale φ›`. Establish `: Smooth (Spec.map (CommRingCat.ofHom σ))` using `HasRingHomProperty.Spec_iff.mpr (hsm _ _ (h1 x) (h2 x))`. Rewrite using `[← ht2]`. Use `infer_instance`.
-/
theorem smooth_snd_of_isStrictlySemistable {O K : Type} [CommRing O] [CommRing K] [Algebra O K] (ϖ : O)
    [IsLocalization.Away ϖ K] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O))
    (hss : GlobalTheory.Et.IsStrictlySemistable ϖ p)
    (hsm : ∀ m r : ℕ, 1 ≤ r → r ≤ m →
      (IsLocalization.Away.map K (Localization.Away (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r) ϖ))
        (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r)) ϖ).Smooth) :
    Smooth (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap O K)))) := by
  have : IsZariskiLocalAtSource @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  set j := Spec.map (CommRingCat.ofHom (algebraMap O K))
  have hgen := IsPullback.of_hasPullback p j
  choose W hW hxW m r h1 h2 ψ hψe hψ using hss
  refine IsZariskiLocalAtSource.of_iSup_eq_top (fun x : X ↦ (pullback.fst p j) ⁻¹ᵁ W x) ?_ ?_
  · rw [eq_top_iff]
    intro z _
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨pullback.fst p j z, hxW _⟩
  intro x
  set B := GlobalTheory.Et.ssModel O ϖ (m x) (r x)
  set s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom (algebraMap O B))
  set φ : (W x).toScheme ⟶ Spec (CommRingCat.of B) := (hW x).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (ψ x))
  have hφ : (W x).ι ≫ p = φ ≫ s := by
    have e1 : (W x).ι = (hW x).isoSpec.hom ≫ (hW x).fromSpec := by
      rw [← (hW x).isoSpec_inv_ι, Iso.hom_inv_id_assoc]
    have e2 := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top (Spec (CommRingCat.of O))) (hW x) le_top
    rw [e1, Category.assoc, ← e2]
    simp only [φ, s, Category.assoc, ← Spec.map_comp]
    congr 2
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (hψ x).symm
  set Bϖ := Localization.Away (algebraMap O B ϖ)
  set σ : K →+* Bϖ := IsLocalization.Away.map K Bϖ (algebraMap O B) ϖ
  have hH : σ.comp (algebraMap O K) = (algebraMap B Bϖ).comp (algebraMap O B) := by
    simp only [σ, IsLocalization.Away.map]
    exact IsLocalization.map_comp _
  have : IsLocalization ((Submonoid.powers ϖ).map (algebraMap O B)) Bϖ := by
    rw [Submonoid.map_powers]; infer_instance
  have hpush := CommRingCat.isPushout_of_isLocalization (algebraMap O B) σ hH (Submonoid.powers ϖ)
  have hbot := isPullback_SpecMap_of_isPushout _ _ _ _ hpush
  have hout := (isPullback_morphismRestrict (pullback.fst p j) (W x)).paste_vert hgen
  rw [hφ] at hout
  have hw : ((pullback.fst p j ∣_ W x) ≫ φ) ≫ s =
      (((pullback.fst p j) ⁻¹ᵁ W x).ι ≫ pullback.snd p j) ≫ j := by
    rw [Category.assoc]; exact hout.w
  set t := hbot.lift _ _ hw
  have ht1 : t ≫ Spec.map (CommRingCat.ofHom (algebraMap B Bϖ)) = (pullback.fst p j ∣_ W x) ≫ φ :=
    hbot.lift_fst _ _ hw
  have ht2 : t ≫ Spec.map (CommRingCat.ofHom σ) = ((pullback.fst p j) ⁻¹ᵁ W x).ι ≫ pullback.snd p j :=
    hbot.lift_snd _ _ hw
  rw [← ht2] at hout
  have hleft := IsPullback.of_bot hout ht1.symm hbot
  have : Etale (Spec.map (CommRingCat.ofHom (ψ x))) := HasRingHomProperty.Spec_iff.mpr (hψe x)
  have : Etale φ := inferInstance
  have : Etale t := MorphismProperty.of_isPullback hleft ‹Etale φ›
  have : Smooth (Spec.map (CommRingCat.ofHom σ)) := HasRingHomProperty.Spec_iff.mpr (hsm _ _ (h1 x) (h2 x))
  rw [← ht2]
  infer_instance

end CrystallineSemistableComparison
