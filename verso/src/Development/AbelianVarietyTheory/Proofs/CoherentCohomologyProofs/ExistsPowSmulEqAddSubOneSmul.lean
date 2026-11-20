import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsXPowSmulEqZeroOfEqXSubOneSmul

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open scoped Pointwise

namespace GlobalTheory

/- English proof (translation)
Use `⟨(∑ j ∈ Finset.range k, x ^ j) • y, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, mul_geom_sum, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_pow_smul_eq_add_sub_one_smul {S M : Type} [CommRing S] [AddCommGroup M]
    [Module S M] (x : S) (k : ℕ) (y : M) : ∃ w : M, x ^ k • y = y + (x - 1) • w := by
  refine ⟨(∑ j ∈ Finset.range k, x ^ j) • y, ?_⟩
  rw [smul_smul, mul_geom_sum, sub_smul, one_smul]
  abel

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, hx⟩`. Take `⟨v, -, hv⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx`.

Establish `hvK : v ∈ LinearMap.ker φ`. Rewrite using `[LinearMap.mem_ker]`. Apply `hreg` to reduce the goal to its premises. Rewrite using `[← map_smul, hv]`. Conclude with `LinearMap.mem_ker.mp x.2`.

Establish `hx' : x = u • (⟨v, hvK⟩ : LinearMap.ker φ)` using `Subtype.ext hv.symm`. Rewrite using `[hx']`. Conclude with `Submodule.smul_mem_pointwise_smul _ u ⊤ Submodule.mem_top`. Introduce `hx`. Take `⟨b, -, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx`.

Use `⟨(u • b).2, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul]`. Conclude with `Submodule.smul_mem_pointwise_smul (b : F) u ⊤ Submodule.mem_top`.
-/
private lemma comap_ker_inf_smul_whole_eq_smul_whole_of_regular {S F G : Type} [CommRing S] [AddCommGroup F]
    [Module S F] [AddCommGroup G] [Module S G] (u : S) (φ : F →ₗ[S] G)
    (hreg : ∀ z : G, u • z = 0 → z = 0) :
    Submodule.comap (LinearMap.ker φ).subtype (LinearMap.ker φ ⊓ u • (⊤ : Submodule S F)) =
      u • (⊤ : Submodule S (LinearMap.ker φ)) := by
  ext x
  rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]
  constructor
  · rintro ⟨-, hx⟩
    obtain ⟨v, -, hv⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    have hvK : v ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker]
      apply hreg
      rw [← map_smul, hv]
      exact LinearMap.mem_ker.mp x.2
    have hx' : x = u • (⟨v, hvK⟩ : LinearMap.ker φ) := Subtype.ext hv.symm
    rw [hx']
    exact Submodule.smul_mem_pointwise_smul _ u ⊤ Submodule.mem_top
  · intro hx
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    refine ⟨(u • b).2, ?_⟩
    rw [Submodule.coe_smul]
    exact Submodule.smul_mem_pointwise_smul (b : F) u ⊤ Submodule.mem_top

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le ?_ ?_` and prove the remaining obligations. Introduce `y hy`. Rewrite `hy`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[LinearMap.comp_apply, hy, map_zero]`.

Introduce `y hy`. Take `⟨v, -, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy`. Rewrite using `[LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, map_smul]`. Conclude with `Submodule.smul_mem_pointwise_smul _ u ⊤ Submodule.mem_top`. Introduce `y hy`.

Rewrite `hy` using `[LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Take `⟨w, -, hw⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy`. Take `⟨k, v, hk, rfl⟩` from `hker y w hw.symm`. Conclude with `Submodule.add_mem_sup (LinearMap.mem_ker.mpr hk) (Submodule.smul_mem_pointwise_smul v u ⊤ Submodule.mem_top)`.
-/
private lemma ker_sup_smul_whole_eq_ker_mkQ_comp {S F G : Type} [CommRing S] [AddCommGroup F]
    [Module S F] [AddCommGroup G] [Module S G] (u : S) (φ : F →ₗ[S] G)
    (hker : ∀ (y : F) (w : G), φ y = u • w → ∃ (k v : F), φ k = 0 ∧ y = k + u • v) :
    LinearMap.ker φ ⊔ u • (⊤ : Submodule S F) =
      LinearMap.ker ((u • (⊤ : Submodule S G)).mkQ ∘ₗ φ) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro y hy
      rw [LinearMap.mem_ker] at hy ⊢
      rw [LinearMap.comp_apply, hy, map_zero]
    · intro y hy
      obtain ⟨v, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, map_smul]
      exact Submodule.smul_mem_pointwise_smul _ u ⊤ Submodule.mem_top
  · intro y hy
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    obtain ⟨k, v, hk, rfl⟩ := hker y w hw.symm
    exact Submodule.add_mem_sup (LinearMap.mem_ker.mpr hk)
      (Submodule.smul_mem_pointwise_smul v u ⊤ Submodule.mem_top)

/- English proof (translation)
Set `ψ : F →ₗ[S] QuotSMulTop u G` to `(u • (⊤ : Submodule S G)).mkQ ∘ₗ φ`. Establish `hψ : Function.Surjective ψ`. Introduce `z`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective (u • (⊤ : Submodule S G)) z`. Take `⟨y, w, hy⟩` from `hsurj z`.

Use `⟨y, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hy, add_sub_cancel_left]`. Conclude with `Submodule.smul_mem_pointwise_smul w u ⊤ Submodule.mem_top`. Establish `hfg : (LinearMap.ker ψ).FG` using `Module.FinitePresentation.fg_ker ψ hψ`. Establish `hfin : Module.Finite S ↥(LinearMap.ker φ ⊔ u • (⊤ : Submodule S F))`.

Rewrite using `[ker_sup_smul_whole_eq_ker_mkQ_comp u φ hker]`. Conclude with `Module.Finite.iff_fg.mpr hfg`. Establish `h2 : Module.Finite S (LinearMap.ker φ ⧸ Submodule.comap (LinearMap.ker φ).subtype (LinearMap.ker φ ⊓ u • (⊤ : Submodule S F)))` using `Module.Finite.equiv (LinearMap.quotientInfEquivSupQuotient (LinearMap.ker φ) (u • (⊤ : Submodule S F))).symm`. Conclude with `Module.Finite.equiv (Submodule.quotEquivOfEq _ (u • (⊤ : Submodule S (LinearMap.ker φ))) (comap_ker_inf_smul_whole_eq_smul_whole_of_regular u φ hreg))`.
-/
theorem finite_quotSMulTop_ker_of_regular {S F G : Type} [CommRing S] [AddCommGroup F]
    [Module S F] [AddCommGroup G] [Module S G] (u : S) (φ : F →ₗ[S] G)
    (hreg : ∀ z : G, u • z = 0 → z = 0) [Module.Finite S F]
    [Module.FinitePresentation S (QuotSMulTop u G)]
    (hsurj : ∀ z : G, ∃ (y : F) (w : G), φ y = z + u • w)
    (hker : ∀ (y : F) (w : G), φ y = u • w → ∃ (k v : F), φ k = 0 ∧ y = k + u • v) :
    Module.Finite S (QuotSMulTop u (LinearMap.ker φ)) := by
  let ψ : F →ₗ[S] QuotSMulTop u G := (u • (⊤ : Submodule S G)).mkQ ∘ₗ φ
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (u • (⊤ : Submodule S G)) z
    obtain ⟨y, w, hy⟩ := hsurj z
    refine ⟨y, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hy, add_sub_cancel_left]
    exact Submodule.smul_mem_pointwise_smul w u ⊤ Submodule.mem_top
  have hfg : (LinearMap.ker ψ).FG := Module.FinitePresentation.fg_ker ψ hψ
  have hfin : Module.Finite S ↥(LinearMap.ker φ ⊔ u • (⊤ : Submodule S F)) := by
    rw [ker_sup_smul_whole_eq_ker_mkQ_comp u φ hker]
    exact Module.Finite.iff_fg.mpr hfg
  have h2 : Module.Finite S (LinearMap.ker φ ⧸ Submodule.comap (LinearMap.ker φ).subtype
      (LinearMap.ker φ ⊓ u • (⊤ : Submodule S F))) :=
    Module.Finite.equiv (LinearMap.quotientInfEquivSupQuotient (LinearMap.ker φ)
      (u • (⊤ : Submodule S F))).symm
  exact Module.Finite.equiv (Submodule.quotEquivOfEq _ (u • (⊤ : Submodule S (LinearMap.ker φ)))
    (comap_ker_inf_smul_whole_eq_smul_whole_of_regular u φ hreg))

/- English proof (translation)
Introduce `ι _ _ R _ F _ _ _ _ ℱ _ _ G _ _ _ _ 𝒢 _ _ φ i hφ hF hpow hfp`. Take `⟨hregG, hkillG, -⟩` from `X_sub_one_smul_graded ι R G 𝒢 i`. Take `⟨-, -, hhomF⟩` from `X_sub_one_smul_graded ι R F ℱ i`. Use `finite_quotSMulTop_ker_of_regular (X i - 1 : MvPolynomial ι R) φ hregG ?_ ?_` and prove the remaining obligations. Introduce `z`.

Take `⟨k, hk⟩` from `hpow z`. Take `⟨y, hy⟩` from `LinearMap.mem_range.mp hk`. Take `⟨w, hw⟩` from `exists_pow_smul_eq_add_sub_one_smul (X i : MvPolynomial ι R) k z`. Conclude with `⟨y, w, hy.trans hw⟩`. Introduce `y w hyw`.

Take `⟨n₀, hn⟩` from `hhomF y`. Take `⟨y', hy', v₀, hyv⟩` from `hn n₀ le_rfl`. Establish `hφy' : φ y' ∈ 𝒢 n₀` using `hφ hy'`. Establish `h1 : φ y = φ y' + (X i - 1 : MvPolynomial ι R) • φ v₀`. Rewrite using `[hyv, map_add, map_smul]`.

Establish `h2 : φ y' = (X i - 1 : MvPolynomial ι R) • (w - φ v₀)`. Rewrite using `[smul_sub, ← hyw, h1]`. Normalize the expressions using the abelian group laws. Take `⟨k, hk⟩` from `hkillG n₀ (φ y') (w - φ v₀) hφy' h2`. Take `⟨w₁, hw₁⟩` from `exists_pow_smul_eq_add_sub_one_smul (X i : MvPolynomial ι R) k y'`.

Use `⟨(X i : MvPolynomial ι R) ^ k • y', v₀ - w₁, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, hk]`. Rewrite using `[hyv, hw₁, smul_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem finite_quotSMulTop_ker_of_graded :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (F : Type) [AddCommGroup F] [Module R F] [Module (MvPolynomial ι R) F] [IsScalarTower R (MvPolynomial ι R) F] (ℱ : ℤ → Submodule R F) [PolyGradedSMul ι ℱ] [Decomposition ℱ] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G] [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢] [Decomposition 𝒢] (φ : F →ₗ[MvPolynomial ι R] G) (i : ι), IsGradedMap ℱ 𝒢 φ → Module.Finite (MvPolynomial ι R) F → (∀ z : G, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range φ) → Module.FinitePresentation (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) G) → Module.Finite (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) (LinearMap.ker φ)) := by
  intro ι _ _ R _ F _ _ _ _ ℱ _ _ G _ _ _ _ 𝒢 _ _ φ i hφ hF hpow hfp
  obtain ⟨hregG, hkillG, -⟩ := X_sub_one_smul_graded ι R G 𝒢 i
  obtain ⟨-, -, hhomF⟩ := X_sub_one_smul_graded ι R F ℱ i
  refine finite_quotSMulTop_ker_of_regular (X i - 1 : MvPolynomial ι R) φ hregG ?_ ?_
  · intro z
    obtain ⟨k, hk⟩ := hpow z
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hk
    obtain ⟨w, hw⟩ := exists_pow_smul_eq_add_sub_one_smul (X i : MvPolynomial ι R) k z
    exact ⟨y, w, hy.trans hw⟩
  · intro y w hyw
    obtain ⟨n₀, hn⟩ := hhomF y
    obtain ⟨y', hy', v₀, hyv⟩ := hn n₀ le_rfl
    have hφy' : φ y' ∈ 𝒢 n₀ := hφ hy'
    have h1 : φ y = φ y' + (X i - 1 : MvPolynomial ι R) • φ v₀ := by
      rw [hyv, map_add, map_smul]
    have h2 : φ y' = (X i - 1 : MvPolynomial ι R) • (w - φ v₀) := by
      rw [smul_sub, ← hyw, h1]
      abel
    obtain ⟨k, hk⟩ := hkillG n₀ (φ y') (w - φ v₀) hφy' h2
    obtain ⟨w₁, hw₁⟩ := exists_pow_smul_eq_add_sub_one_smul (X i : MvPolynomial ι R) k y'
    refine ⟨(X i : MvPolynomial ι R) ^ k • y', v₀ - w₁, ?_, ?_⟩
    · rw [map_smul, hk]
    · rw [hyv, hw₁, smul_sub]
      abel

end GlobalTheory
