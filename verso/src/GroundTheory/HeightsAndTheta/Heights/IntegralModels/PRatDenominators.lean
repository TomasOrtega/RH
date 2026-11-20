import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsRatDenominators
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace RatDenominators

/- English proof (translation)
Introduce `X f U hU`. Establish `: IsAffineHom (baseChangeMap f ℚ)` using `by set_option backward.isDefEq.respectTransparency.types false in`. Conclude with `MorphismProperty.pullback_fst _ _ inferInstance`. Use `set g := baseChangeMap f ℚ with hg`. Establish `hV : IsAffineOpen (g ⁻¹ᵁ U)` using `hU.preimage g`.

Introduce `b`. Set `φ : Γ(X, U) ⟶ Γ(baseChange f ℚ, g ⁻¹ᵁ U)` to `g.appLE U (g ⁻¹ᵁ U) le_rfl`. Establish `hφ : g.app U = φ` using `Scheme.Hom.app_eq_appLE _`. Set `ιA : CommRingCat.of ℤ ⟶ Γ(X, U)` to `CommRingCat.ofHom (Int.castRingHom Γ(X, U))`. Set `h : CommRingCat.of ℤ ⟶ CommRingCat.of ℚ` to `CommRingCat.ofHom (Int.castRingHom ℚ)`.

Establish `hUf : hU.fromSpec ≫ f = Spec.map ιA` using `specZIsTerminal.hom_ext _ _`. Establish `key` using `IsAffineOpen.SpecMap_appLE_fromSpec g hU hV le_rfl`. Establish `Pgeo : IsPullback (Spec.map φ) (hV.fromSpec ≫ pullback.snd f (Spec.map h)) (Spec.map ιA) (Spec.map h)`. Establish `P` using `(isPullback_morphismRestrict g U).paste_vert (IsPullback.of_hasPullback f (Spec.map h))`. Rewrite using `[← hUf]`.

Use `P.of_iso hV.isoSpec hU.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← cancel_mono hU.fromSpec, Category.assoc, Category.assoc, key, ← hU.isoSpec_inv_ι, ← hV.isoSpec_inv_ι]`. Simplify using `[morphismRestrict_ι]`. Rewrite using `[← hV.isoSpec_inv_ι]`. Simplify using the standard rewrite rules.

Rewrite using `[← hU.isoSpec_inv_ι]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Set `M : Submonoid Γ(X, U)` to `(nonZeroDivisors ℤ).map (Int.castRingHom Γ(X, U))`. Set `L` to `Localization M`.

Set `fQ : ℚ →+* L` to `IsLocalization.map (M := nonZeroDivisors ℤ) (S := ℚ) L (Int.castRingHom Γ(X, U)) (T := M) (Submonoid.le_comap_map _)`. Establish `H : fQ.comp (algebraMap ℤ ℚ) = (algebraMap Γ(X, U) L).comp (Int.castRingHom Γ(X, U))` using `IsLocalization.map_comp _`. Establish `Palg` using `isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isLocalization (Int.castRingHom Γ(X, U)) fQ H (nonZeroDivisors ℤ))`. Set `e` to `Pgeo.isoIsPullback _ _ Palg`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective e.hom`.

Take `⟨χ, hχ⟩` from `Spec.map_surjective e.inv`. Establish `hcomp : CommRingCat.ofHom (algebraMap Γ(X, U) L) ≫ ψ = φ`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hψ]`. Conclude with `IsPullback.isoIsPullback_hom_fst _ _ Pgeo Palg`.

Establish `hχψ : χ ≫ ψ = 𝟙 _`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hψ, hχ, Iso.hom_inv_id, Spec.map_id]`. Establish `hφa : ∀ a, φ a = ψ (algebraMap Γ(X, U) L a)` using `fun a => by rw [← hcomp]; rfl`. Establish `hψa : ∀ b, ψ (χ b) = b` using `fun b => by`.

Rewrite using `[← CommRingCat.comp_apply, hχψ]`. Both sides reduce to the same expression. Take `⟨⟨a, m⟩, ham⟩` from `IsLocalization.surj M (χ b)`. Take `⟨n, hn, hnm⟩` from `Submonoid.mem_map.mp m.2`. Establish `hn0 : n ≠ 0` using `nonZeroDivisors.ne_zero hn`.

Establish `hb : b * (n : Γ(baseChange f ℚ, g ⁻¹ᵁ U)) = φ a`. Use `congrArg ψ ham` as an intermediate fact. Rewrite `this` using `[map_mul, hψa, ← hφa, ← hφa, ← hnm]`. Simplify using `using this`. Use `⟨n.natAbs, Int.natAbs_pos.mpr hn0, ?_⟩` and prove the remaining obligations.

Rewrite using `[hφ, nsmul_eq_mul]`. Break down `Int.natAbs_eq n with hn' | hn'` into its components or cases. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← hb, mul_comm, hn']`. Simplify using the standard rewrite rules.

Use `⟨-a, ?_⟩` and prove the remaining obligations. Rewrite using `[map_neg, ← hb, mul_comm, hn']`. Simplify using the standard rewrite rules.
-/
theorem proof : RatDenominators.Statement := by
  intro X f U hU
  have : IsAffineHom (baseChangeMap f ℚ) := by
    set_option backward.isDefEq.respectTransparency.types false in
    exact MorphismProperty.pullback_fst _ _ inferInstance
  set g := baseChangeMap f ℚ with hg
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  intro b
  let φ : Γ(X, U) ⟶ Γ(baseChange f ℚ, g ⁻¹ᵁ U) := g.appLE U (g ⁻¹ᵁ U) le_rfl
  have hφ : g.app U = φ := Scheme.Hom.app_eq_appLE _
  let ιA : CommRingCat.of ℤ ⟶ Γ(X, U) := CommRingCat.ofHom (Int.castRingHom Γ(X, U))
  let h : CommRingCat.of ℤ ⟶ CommRingCat.of ℚ := CommRingCat.ofHom (Int.castRingHom ℚ)
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

  let M : Submonoid Γ(X, U) := (nonZeroDivisors ℤ).map (Int.castRingHom Γ(X, U))
  let L := Localization M
  let fQ : ℚ →+* L := IsLocalization.map (M := nonZeroDivisors ℤ) (S := ℚ) L
    (Int.castRingHom Γ(X, U)) (T := M) (Submonoid.le_comap_map _)
  have H : fQ.comp (algebraMap ℤ ℚ) = (algebraMap Γ(X, U) L).comp (Int.castRingHom Γ(X, U)) :=
    IsLocalization.map_comp _
  have Palg := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (Int.castRingHom Γ(X, U)) fQ H (nonZeroDivisors ℤ))
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
  have hn0 : n ≠ 0 := nonZeroDivisors.ne_zero hn
  have hb : b * (n : Γ(baseChange f ℚ, g ⁻¹ᵁ U)) = φ a := by
    have := congrArg ψ ham
    rw [map_mul, hψa, ← hφa, ← hφa, ← hnm] at this
    simpa using this
  refine ⟨n.natAbs, Int.natAbs_pos.mpr hn0, ?_⟩
  rw [hφ, nsmul_eq_mul]
  rcases Int.natAbs_eq n with hn' | hn'
  · refine ⟨a, ?_⟩
    rw [← hb, mul_comm, hn']
    simp
  · refine ⟨-a, ?_⟩
    rw [map_neg, ← hb, mul_comm, hn']
    simp

end RatDenominators

end

end GroundTheory.Heights₂.Heights.Model
