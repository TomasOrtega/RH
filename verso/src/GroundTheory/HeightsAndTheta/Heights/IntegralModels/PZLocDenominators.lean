import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsZLocDenominators
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace ZLocDenominators

/- English proof (translation)
Introduce `X f p U hU`. Establish `: IsAffineHom (baseChangeMap f (ZLoc p))` using `by set_option backward.isDefEq.respectTransparency.types false in`. Conclude with `MorphismProperty.pullback_fst _ _ inferInstance`. Use `set g := baseChangeMap f (ZLoc p) with hg`. Establish `hV : IsAffineOpen (g ⁻¹ᵁ U)` using `hU.preimage g`.

Introduce `b`. Set `φ : Γ(X, U) ⟶ Γ(baseChange f (ZLoc p), g ⁻¹ᵁ U)` to `g.appLE U (g ⁻¹ᵁ U) le_rfl`. Establish `hφ : g.app U = φ` using `Scheme.Hom.app_eq_appLE _`. Set `ιA : CommRingCat.of ℤ ⟶ Γ(X, U)` to `CommRingCat.ofHom (Int.castRingHom Γ(X, U))`. Set `h : CommRingCat.of ℤ ⟶ CommRingCat.of (ZLoc p)` to `CommRingCat.ofHom (Int.castRingHom (ZLoc p))`.

Establish `hUf : hU.fromSpec ≫ f = Spec.map ιA` using `specZIsTerminal.hom_ext _ _`. Establish `key` using `IsAffineOpen.SpecMap_appLE_fromSpec g hU hV le_rfl`. Establish `Pgeo : IsPullback (Spec.map φ) (hV.fromSpec ≫ pullback.snd f (Spec.map h)) (Spec.map ιA) (Spec.map h)`. Establish `P` using `(isPullback_morphismRestrict g U).paste_vert (IsPullback.of_hasPullback f (Spec.map h))`. Rewrite using `[← hUf]`.

Use `P.of_iso hV.isoSpec hU.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← cancel_mono hU.fromSpec, Category.assoc, Category.assoc, key, ← hU.isoSpec_inv_ι, ← hV.isoSpec_inv_ι]`. Simplify using `[morphismRestrict_ι]`. Rewrite using `[← hV.isoSpec_inv_ι]`. Simplify using the standard rewrite rules.

Rewrite using `[← hU.isoSpec_inv_ι]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Set `S : Submonoid ℤ` to `(Ideal.span {((p : ℕ) : ℤ)}).primeCompl`. Set `M : Submonoid Γ(X, U)` to `S.map (Int.castRingHom Γ(X, U))`.

Set `L` to `Localization M`. Set `fZ : ZLoc p →+* L` to `IsLocalization.map (M := S) (S := ZLoc p) L (Int.castRingHom Γ(X, U)) (T := M) (Submonoid.le_comap_map _)`. Establish `H : fZ.comp (algebraMap ℤ (ZLoc p)) = (algebraMap Γ(X, U) L).comp (Int.castRingHom Γ(X, U))` using `IsLocalization.map_comp _`. Establish `Palg` using `isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isLocalization (Int.castRingHom Γ(X, U)) fZ H S)`. Establish `hh : algebraMap ℤ (ZLoc p) = Int.castRingHom (ZLoc p)` using `Subsingleton.elim _ _`.

Rewrite `Palg` using `[hh]`. Set `e` to `Pgeo.isoIsPullback _ _ Palg`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective e.hom`. Take `⟨χ, hχ⟩` from `Spec.map_surjective e.inv`. Establish `hcomp : CommRingCat.ofHom (algebraMap Γ(X, U) L) ≫ ψ = φ`.

Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hψ]`. Conclude with `IsPullback.isoIsPullback_hom_fst _ _ Pgeo Palg`. Establish `hχψ : χ ≫ ψ = 𝟙 _`. Apply `Spec.map_injective` to reduce the goal to its premises.

Rewrite using `[Spec.map_comp, hψ, hχ, Iso.hom_inv_id, Spec.map_id]`. Establish `hφa : ∀ a, φ a = ψ (algebraMap Γ(X, U) L a)` using `fun a => by rw [← hcomp]; rfl`. Establish `hψa : ∀ b, ψ (χ b) = b` using `fun b => by`. Rewrite using `[← CommRingCat.comp_apply, hχψ]`. Both sides reduce to the same expression.

Take `⟨⟨a, m⟩, ham⟩` from `IsLocalization.surj M (χ b)`. Take `⟨n, hn, hnm⟩` from `Submonoid.mem_map.mp m.2`. Establish `hpn : ¬ ((p : ℕ) : ℤ) ∣ n` using `fun hd => hn (Ideal.mem_span_singleton.mpr hd)`. Establish `hn0 : n ≠ 0` using `by rintro rfl; exact hpn (dvd_zero _)`. Establish `hb : b * (n : Γ(baseChange f (ZLoc p), g ⁻¹ᵁ U)) = φ a`.

Use `congrArg ψ ham` as an intermediate fact. Rewrite `this` using `[map_mul, hψa, ← hφa, ← hφa, ← hnm]`. Simplify using `using this`. Use `⟨n.natAbs, Int.natAbs_pos.mpr hn0, fun hd => hpn (Int.natCast_dvd.mpr hd), ?_⟩` and prove the remaining obligations. Rewrite using `[hφ, nsmul_eq_mul]`.

Break down `Int.natAbs_eq n with hn' | hn'` into its components or cases. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← hb, mul_comm, hn']`. Simplify using the standard rewrite rules. Use `⟨-a, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_neg, ← hb, mul_comm, hn']`. Simplify using the standard rewrite rules.
-/
theorem proof : ZLocDenominators.Statement := by
  intro X f p U hU
  have : IsAffineHom (baseChangeMap f (ZLoc p)) := by
    set_option backward.isDefEq.respectTransparency.types false in
    exact MorphismProperty.pullback_fst _ _ inferInstance
  set g := baseChangeMap f (ZLoc p) with hg
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  intro b
  let φ : Γ(X, U) ⟶ Γ(baseChange f (ZLoc p), g ⁻¹ᵁ U) := g.appLE U (g ⁻¹ᵁ U) le_rfl
  have hφ : g.app U = φ := Scheme.Hom.app_eq_appLE _
  let ιA : CommRingCat.of ℤ ⟶ Γ(X, U) := CommRingCat.ofHom (Int.castRingHom Γ(X, U))
  let h : CommRingCat.of ℤ ⟶ CommRingCat.of (ZLoc p) :=
    CommRingCat.ofHom (Int.castRingHom (ZLoc p))
  have hUf : hU.fromSpec ≫ f = Spec.map ιA := specZIsTerminal.hom_ext _ _

  have key := IsAffineOpen.SpecMap_appLE_fromSpec g hU hV le_rfl
  have Pgeo : IsPullback (Spec.map φ) (hV.fromSpec ≫ pullback.snd f (Spec.map h))
      (Spec.map ιA) (Spec.map h) := by
    have P := (isPullback_morphismRestrict g U).paste_vert (IsPullback.of_hasPullback f (Spec.map h))
    rw [← hUf]
    refine P.of_iso hV.isoSpec hU.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [← cancel_mono hU.fromSpec, Category.assoc, Category.assoc, key, ← hU.isoSpec_inv_ι,
        ← hV.isoSpec_inv_ι]
      simp [morphismRestrict_ι]
    · rw [← hV.isoSpec_inv_ι]
      simp
    · rw [← hU.isoSpec_inv_ι]
      simp
    · simp

  let S : Submonoid ℤ := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl
  let M : Submonoid Γ(X, U) := S.map (Int.castRingHom Γ(X, U))
  let L := Localization M
  let fZ : ZLoc p →+* L := IsLocalization.map (M := S) (S := ZLoc p) L
    (Int.castRingHom Γ(X, U)) (T := M) (Submonoid.le_comap_map _)
  have H : fZ.comp (algebraMap ℤ (ZLoc p)) = (algebraMap Γ(X, U) L).comp (Int.castRingHom Γ(X, U)) :=
    IsLocalization.map_comp _
  have Palg := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (Int.castRingHom Γ(X, U)) fZ H S)
  have hh : algebraMap ℤ (ZLoc p) = Int.castRingHom (ZLoc p) := Subsingleton.elim _ _
  rw [hh] at Palg
  let e := Pgeo.isoIsPullback _ _ Palg
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective e.hom
  obtain ⟨χ, hχ⟩ := Spec.map_surjective e.inv
  have hcomp : CommRingCat.ofHom (algebraMap Γ(X, U) L) ≫ ψ = φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ]
    exact IsPullback.isoIsPullback_hom_fst _ _ Pgeo Palg
  have hχψ : χ ≫ ψ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hχ, Iso.hom_inv_id, Spec.map_id]
  have hφa : ∀ a, φ a = ψ (algebraMap Γ(X, U) L a) := fun a => by rw [← hcomp]; rfl
  have hψa : ∀ b, ψ (χ b) = b := fun b => by
    rw [← CommRingCat.comp_apply, hχψ]; rfl

  obtain ⟨⟨a, m⟩, ham⟩ := IsLocalization.surj M (χ b)
  obtain ⟨n, hn, hnm⟩ := Submonoid.mem_map.mp m.2
  have hpn : ¬ ((p : ℕ) : ℤ) ∣ n := fun hd => hn (Ideal.mem_span_singleton.mpr hd)
  have hn0 : n ≠ 0 := by rintro rfl; exact hpn (dvd_zero _)
  have hb : b * (n : Γ(baseChange f (ZLoc p), g ⁻¹ᵁ U)) = φ a := by
    have := congrArg ψ ham
    rw [map_mul, hψa, ← hφa, ← hφa, ← hnm] at this
    simpa using this
  refine ⟨n.natAbs, Int.natAbs_pos.mpr hn0, fun hd => hpn (Int.natCast_dvd.mpr hd), ?_⟩
  rw [hφ, nsmul_eq_mul]
  rcases Int.natAbs_eq n with hn' | hn'
  · refine ⟨a, ?_⟩
    rw [← hb, mul_comm, hn']
    simp
  · refine ⟨-a, ?_⟩
    rw [map_neg, ← hb, mul_comm, hn']
    simp

end ZLocDenominators

end

end GroundTheory.Heights₂.Heights.Model
