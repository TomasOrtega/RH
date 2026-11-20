import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EvenNormsOfUnitNonsquare
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissibleSupersetFinitePlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsQuadraticSqrtExtensionOfNotSquare
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsQuadraticSqrtExtensionBasicFacts
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ValuationUnramifiedOfUnit
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTwoPlacesOverOfIsSquareLocal
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Use `choose! n hnN hnv hnw using h`. Use `set T := (finite_valuation_ne_one F t).toFinset \ S with hT`. Establish `hP : ∏ v ∈ T, n v ∈ N` using `N.prod_mem (fun v hv => hnN v (Finset.mem_sdiff.1 hv).2)`. Establish `hU : t * (∏ v ∈ T, n v)⁻¹ ∈ sUnits F S`. Rewrite using `[mem_sUnits]`.

Introduce `w hw`. Establish `key : w.valuation F ((∏ v ∈ T, n v : Fˣ) : F) = w.valuation F (t : F)`. Rewrite using `[Units.coe_prod, map_prod]`. Distinguish the cases in `hwT : w ∈ T`. Rewrite using `[Finset.prod_eq_single w]`.

Conclude with `hnv w hw`. Introduce `v hv hne`. Conclude with `hnw v (Finset.mem_sdiff.1 hv).2 w hw hne.symm`. Introduce `h'`. Conclude with `absurd hwT h'`.

Establish `h1 : w.valuation F (t : F) = 1`. Assume the negation of the conclusion as `hc`. Conclude with `hwT (Finset.mem_sdiff.2 ⟨by simpa using hc, hw⟩)`. Rewrite using `[h1]`. Use `Finset.prod_eq_one (fun v hv => ?_)` and prove the remaining obligations.

Conclude with `hnw v (Finset.mem_sdiff.1 hv).2 w hw (fun e => hwT (e ▸ hv))`. Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, key]`. Conclude with `mul_inv_cancel₀ (by simp)`. Establish `: t = t * (∏ v ∈ T, n v)⁻¹ * ∏ v ∈ T, n v` using `by group`. Rewrite using `[this]`.

Conclude with `Subgroup.mul_mem_sup hU hP`.
-/
theorem mem_sUnits_sup_of_local_orders {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (N : Subgroup Fˣ) (t : Fˣ)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∃ n ∈ N,
      v.valuation F (n : F) = v.valuation F (t : F) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → w ≠ v → w.valuation F (n : F) = 1) :
    t ∈ sUnits F S ⊔ N := by
  classical
  choose! n hnN hnv hnw using h
  set T := (finite_valuation_ne_one F t).toFinset \ S with hT
  have hP : ∏ v ∈ T, n v ∈ N :=
    N.prod_mem (fun v hv => hnN v (Finset.mem_sdiff.1 hv).2)
  have hU : t * (∏ v ∈ T, n v)⁻¹ ∈ sUnits F S := by
    rw [mem_sUnits]
    intro w hw
    have key : w.valuation F ((∏ v ∈ T, n v : Fˣ) : F) = w.valuation F (t : F) := by
      rw [Units.coe_prod, map_prod]
      by_cases hwT : w ∈ T
      · rw [Finset.prod_eq_single w]
        · exact hnv w hw
        · intro v hv hne
          exact hnw v (Finset.mem_sdiff.1 hv).2 w hw hne.symm
        · intro h'; exact absurd hwT h'
      · have h1 : w.valuation F (t : F) = 1 := by
          by_contra hc
          exact hwT (Finset.mem_sdiff.2 ⟨by simpa using hc, hw⟩)
        rw [h1]
        refine Finset.prod_eq_one (fun v hv => ?_)
        exact hnw v (Finset.mem_sdiff.1 hv).2 w hw (fun e => hwT (e ▸ hv))
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, key]
    exact mul_inv_cancel₀ (by simp)
  have : t = t * (∏ v ∈ T, n v)⁻¹ * ∏ v ∈ T, n v := by group
  rw [this]
  exact Subgroup.mul_mem_sup hU hP

/- English proof (translation)
Take `⟨w, w', hne, hw, hw'⟩` from `two_places_of_isSquare F E δ θ σ hq v hsq`. Take `⟨hc1, hc2⟩` from `conj_places_transitive F E δ θ σ hq`. Establish `hwS : w ∉ SE` using `by rw [hover, hw]; exact hv`. Establish `hw'S : w' ∉ SE` using `by rw [hover, hw']; exact hv`. Take `⟨-, π, hπ, hπ'⟩` from `hSE w hwS`.

Take `⟨a, b, hab⟩` from `(isQuad_basic F E δ θ σ hq).2.2.2.1 π`. Establish `hun : ∀ x : HeightOneSpectrum (𝓞 E), x.under (𝓞 F) ∉ S → (x.under (𝓞 F)).valuation F (a ^ 2 - δ * b ^ 2) = x.valuation E π * x.valuation E (σ π)`. Introduce `x hx`. Rewrite using `[← map_mul, hab, valuation_unramified_of_unit F E δ θ σ hq x (hS _ hx).1 (hδ _ hx)]`. Use `⟨a, b, ?_, ?_⟩` and prove the remaining obligations.

Use `hun w (hw ▸ hv)` as an intermediate fact. Rewrite `this` using `[hw]`. Rewrite using `[this, hπ]`. Break down `hc2 w w' (hw'.trans hw.symm) with h | h` into its components or cases. Conclude with `absurd h.symm hne`.

Rewrite using `[← h, hπ' w' hw'S hne.symm, mul_one]`. Introduce `u hu huv`. Take `⟨x, hx⟩` from `(places_over F E).2.1 u`. Take `⟨x', hx', hxx⟩` from `hc1 x`. Use `hun x (hx ▸ hu)` as an intermediate fact.

Rewrite `this` using `[hx]`. Rewrite using `[this, ← hxx, hπ' x (by rw [hover, hx]; exact hu) (by rintro rfl; exact huv (hx.symm.trans hw)), hπ' x' (by rw [hover, hx', hx]; exact hu) (by rintro rfl; exact huv ((hx'.trans hx).symm.trans hw)), mul_one]`.
-/
theorem exists_norm_uniformizer_of_split {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E} (hq : IsQuad δ θ σ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : admitted F S) (hSE : admitted E SE) (hover : ∀ w, w ∈ SE ↔ w.under (𝓞 F) ∈ S)
    (hδ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v.valuation F δ = 1)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S)
    (hsq : IsSquare (algebraMap F (v.adicCompletion F) δ)) :
    ∃ a b : F, v.valuation F (a ^ 2 - δ * b ^ 2) = WithZero.exp (-1) ∧
      ∀ u : HeightOneSpectrum (𝓞 F), u ∉ S → u ≠ v → u.valuation F (a ^ 2 - δ * b ^ 2) = 1 := by
  obtain ⟨w, w', hne, hw, hw'⟩ := two_places_of_isSquare F E δ θ σ hq v hsq
  obtain ⟨hc1, hc2⟩ := conj_places_transitive F E δ θ σ hq
  have hwS : w ∉ SE := by rw [hover, hw]; exact hv
  have hw'S : w' ∉ SE := by rw [hover, hw']; exact hv
  obtain ⟨-, π, hπ, hπ'⟩ := hSE w hwS
  obtain ⟨a, b, hab⟩ := (isQuad_basic F E δ θ σ hq).2.2.2.1 π
  have hun : ∀ x : HeightOneSpectrum (𝓞 E), x.under (𝓞 F) ∉ S →
      (x.under (𝓞 F)).valuation F (a ^ 2 - δ * b ^ 2) =
        x.valuation E π * x.valuation E (σ π) := by
    intro x hx
    rw [← map_mul, hab,
      valuation_unramified_of_unit F E δ θ σ hq x (hS _ hx).1 (hδ _ hx)]
  refine ⟨a, b, ?_, ?_⟩
  · have := hun w (hw ▸ hv)
    rw [hw] at this
    rw [this, hπ]
    rcases hc2 w w' (hw'.trans hw.symm) with h | h
    · exact absurd h.symm hne
    · rw [← h, hπ' w' hw'S hne.symm, mul_one]
  · intro u hu huv
    obtain ⟨x, hx⟩ := (places_over F E).2.1 u
    obtain ⟨x', hx', hxx⟩ := hc1 x
    have := hun x (hx ▸ hu)
    rw [hx] at this
    rw [this, ← hxx, hπ' x (by rw [hover, hx]; exact hu) (by rintro rfl; exact huv (hx.symm.trans hw)),
      hπ' x' (by rw [hover, hx', hx]; exact hu)
        (by rintro rfl; exact huv ((hx'.trans hx).symm.trans hw)), mul_one]

/- English proof (translation)
Introduce `F _ _ δ hδ`. Take `⟨E, _, _, _, θ, σ, hq⟩` from `exists_isQuad F δ hδ`. Take `⟨T, -, hT⟩` from `exists_admissible_superset_finite_places E ∅`. Take `⟨S₁, hS₁, hS₁'⟩` from `exists_superset_mem_sUnits F {δ} (T.image (fun w => w.under (𝓞 F)))`. Take `⟨S, hS, hadm⟩` from `exists_admissible_superset_finite_places F S₁`.

Establish `hδS : δ ∈ sUnits F S` using `hS₁' S hS δ (by simp)`. Take `⟨SE, hSE⟩` from `(places_over F E).1 S`. Establish `hadmE : admitted E SE` using `hT.mono (fun w hw => (hSE w).2 (hS (hS₁ (Finset.mem_image_of_mem _ hw))))`. Use `⟨S, hadm, hδS, fun t ht => ?_⟩` and prove the remaining obligations. Use `mem_sUnits_sup_of_local_orders S _ t (fun v hv => ?_)` and prove the remaining obligations.

Establish `ht0 : v.valuation F (t : F) ≠ 0` using `by simp`. Distinguish the cases in `hsq : IsSquare (algebraMap F (v.adicCompletion F) δ)`. Take `⟨a, b, h1, h2⟩` from `exists_norm_uniformizer_of_split hq S SE hadm hadmE hSE ((mem_sUnits F S δ).1 hδS) v hv hsq`. Establish `h0 : a ^ 2 - δ * b ^ 2 ≠ 0`. Introduce `h`.

Rewrite `h1` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero h1.symm`. Use `⟨(Units.mk0 _ h0) ^ (-(WithZero.log (v.valuation F (t : F)))), Subgroup.zpow_mem _ ((mem_normSub _ _ _).2 ⟨a, b, rfl⟩) _, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_zpow_eq_zpow_val, Units.val_mk0, map_zpow₀, h1, ← WithZero.exp_zsmul]`. Simplify using `[WithZero.exp_log ht0]`.

Introduce `u hu huv`. Rewrite using `[Units.val_zpow_eq_zpow_val, Units.val_mk0, map_zpow₀, h2 u hu huv, one_zpow]`. Take `⟨h2, π, hπ, hπ'⟩` from `hadm v hv`. Establish `hval : ∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x` using `fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x`. Establish `hev` using `evenNorms_of_odd_place F v (by have := hval 2; rwa [map_ofNat, h2] at this) _ ((hval _).trans ((mem_sUnits F S δ).1 hδS v hv)) hsq`.

Take `⟨a, b, hab⟩` from `ht v hv`. Take `⟨m, hm⟩` from `hev a b (by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Rewrite `hab` using `[hc.1, hc.2]`.

Simplify using `at hab)`. Rewrite `hm` using `[← hab, hval]`. Establish `hπ0 : π ≠ 0`. Introduce `h`. Rewrite `hπ` using `[h, map_zero]`.

Conclude with `WithZero.exp_ne_zero hπ.symm`. Use `⟨((Units.mk0 _ hπ0) ^ (-m)) ^ 2, ⟨π ^ (-m), 0, by simp⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_pow, map_zpow₀, hπ, hm, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul]`. Simplify using the standard rewrite rules. Introduce `u hu huv`.

Rewrite using `[Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_pow, map_zpow₀, hπ' u hu huv, one_zpow, one_pow]`.
-/
theorem exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub :
    ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ), ¬ IsSquare (δ : F) →
      ∃ S : Finset (HeightOneSpectrum (𝓞 F)), admitted F S ∧ δ ∈ sUnits F S ∧ ∀ t : Fˣ,
        (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
          t ∈ normSub (algebraMap F (v.adicCompletion F)) (δ : F)) →
        t ∈ sUnits F S ⊔ normSub (RingHom.id F) (δ : F) := by
  classical
  intro F _ _ δ hδ
  obtain ⟨E, _, _, _, θ, σ, hq⟩ := exists_isQuad F δ hδ
  obtain ⟨T, -, hT⟩ := exists_admissible_superset_finite_places E ∅
  obtain ⟨S₁, hS₁, hS₁'⟩ := exists_superset_mem_sUnits F {δ} (T.image (fun w => w.under (𝓞 F)))
  obtain ⟨S, hS, hadm⟩ := exists_admissible_superset_finite_places F S₁
  have hδS : δ ∈ sUnits F S := hS₁' S hS δ (by simp)
  obtain ⟨SE, hSE⟩ := (places_over F E).1 S
  have hadmE : admitted E SE := hT.mono (fun w hw =>
    (hSE w).2 (hS (hS₁ (Finset.mem_image_of_mem _ hw))))
  refine ⟨S, hadm, hδS, fun t ht => ?_⟩
  refine mem_sUnits_sup_of_local_orders S _ t (fun v hv => ?_)
  have ht0 : v.valuation F (t : F) ≠ 0 := by simp
  by_cases hsq : IsSquare (algebraMap F (v.adicCompletion F) δ)
  · obtain ⟨a, b, h1, h2⟩ := exists_norm_uniformizer_of_split hq S SE hadm hadmE hSE
      ((mem_sUnits F S δ).1 hδS) v hv hsq
    have h0 : a ^ 2 - δ * b ^ 2 ≠ 0 := by
      intro h
      rw [h, map_zero] at h1
      exact WithZero.exp_ne_zero h1.symm
    refine ⟨(Units.mk0 _ h0) ^ (-(WithZero.log (v.valuation F (t : F)))),
      Subgroup.zpow_mem _ ((mem_normSub _ _ _).2 ⟨a, b, rfl⟩) _, ?_, ?_⟩
    · rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, map_zpow₀, h1, ← WithZero.exp_zsmul]
      simp [WithZero.exp_log ht0]
    · intro u hu huv
      rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, map_zpow₀, h2 u hu huv, one_zpow]
  · obtain ⟨h2, π, hπ, hπ'⟩ := hadm v hv
    have hval : ∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
      fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
    have hev := evenNorms_of_odd_place F v
      (by have := hval 2; rwa [map_ofNat, h2] at this) _
      ((hval _).trans ((mem_sUnits F S δ).1 hδS v hv)) hsq
    obtain ⟨a, b, hab⟩ := ht v hv
    obtain ⟨m, hm⟩ := hev a b (by
      by_contra hc
      push Not at hc
      rw [hc.1, hc.2] at hab
      simp at hab)
    rw [← hab, hval] at hm
    have hπ0 : π ≠ 0 := by
      intro h
      rw [h, map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    refine ⟨((Units.mk0 _ hπ0) ^ (-m)) ^ 2, ⟨π ^ (-m), 0, by simp⟩, ?_, ?_⟩
    · rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_pow,
        map_zpow₀, hπ, hm, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul]
      simp
    · intro u hu huv
      rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_pow,
        map_zpow₀, hπ' u hu huv, one_zpow, one_pow]

end GlobalTheory.QNorm
