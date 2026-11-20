import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.QuotientRegularAtOfQuotientFreeOverPowerSeries
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ExistsUltraLimitPairOfEventualQuotientMaps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ExistsPowMaximalIdealSmulFiniteEqZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.YCplMemOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.FibEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Patched
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QRegScal

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

/- English proof (translation)
Establish `hf : f ∈ Submonoid.powers f` using `Submonoid.mem_powers f`. Use `⟨fun c => IsLocalizedModule.map_units h c, fun y => ?_, fun {z₁ z₂} hz => ?_⟩` and prove the remaining obligations. Take `⟨⟨x, m⟩, hm⟩` from `IsLocalizedModule.surj (Submonoid.powers f) h y`. Use `⟨⟨Φ x, ⟨f, hf⟩ * m⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, h2, LinearMap.map_smul]`.

Rewrite using `[← hm, mul_smul]`. Both sides reduce to the same expression. Take `⟨c, hc⟩` from `IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) (f := h) hz`. Use `⟨c * ⟨f, hf⟩, ?_⟩` and prove the remaining obligations. Establish `hc'` using `congrArg Φ hc`.

Simplify using `only [Submonoid.smul_def, LinearMap.map_smul, h1] at hc'`. Simplify using `only [Submonoid.smul_def, Submonoid.coe_mul, mul_smul]`. Conclude with `hc'`.
-/
private theorem loc_of_pair {R X Y Z : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] [AddCommGroup Z] [Module R Z] (f : R) (h : X →ₗ[R] Y) [IsLocalizedModule (Submonoid.powers f) h]
    (Φ : X →ₗ[R] Z) (Ψ : Z →ₗ[R] X) (h1 : ∀ z, Φ (Ψ z) = f • z) (h2 : ∀ z, Ψ (Φ z) = f • z) :
    IsLocalizedModule (Submonoid.powers f) (h ∘ₗ Ψ) := by
  have hf : f ∈ Submonoid.powers f := Submonoid.mem_powers f
  refine ⟨fun c => IsLocalizedModule.map_units h c, fun y => ?_, fun {z₁ z₂} hz => ?_⟩
  · obtain ⟨⟨x, m⟩, hm⟩ := IsLocalizedModule.surj (Submonoid.powers f) h y
    refine ⟨⟨Φ x, ⟨f, hf⟩ * m⟩, ?_⟩
    simp only [LinearMap.comp_apply, h2, LinearMap.map_smul]
    rw [← hm, mul_smul]
    rfl
  · obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) (f := h) hz
    refine ⟨c * ⟨f, hf⟩, ?_⟩
    have hc' := congrArg Φ hc
    simp only [Submonoid.smul_def, LinearMap.map_smul, h1] at hc'
    simp only [Submonoid.smul_def, Submonoid.coe_mul, mul_smul]
    exact hc'

/- English proof (translation)
Introduce `Λ R σ _ _ _ _ s _ _ _ _ _ U f ii M _ _ X _ _ _ _ hU hΛ hX hk hpair hnil`. Set `y : σ → R` to `fun a => s (MvPowerSeries.X a)`. Set `m : Ideal R` to `Ideal.map (s.comp MvPowerSeries.C) (maximalIdeal Λ)`. Establish `hq : ∀ a j, ∀ᶠ N in (U : Filter ℕ), QRegAt (M N) y (m ^ j) a`. Introduce `a j`.

Use `filter_upwards [hk (a + 1) j] with N hN`. Take `⟨r, e, he⟩` from `hN`. Conclude with `quotientRegularAt_of_quotient_free_over_powerSeries Λ R σ s (M N) a j r e he`. Establish `hXR : Module.Finite R X`. Take `⟨T, hT⟩` from `(Module.Finite.fg_top : (⊤ : Submodule Λ X).FG)`.

Use `⟨⟨T, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce and unpack `x -`. Establish `hx : x ∈ Submodule.span Λ (T : Set X)` using `hT ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem z hz => exact Submodule.subset_span hz`. Consider the case `zero => exact zero_mem _`. Consider the case `add _ _ _ _ ha hb => exact add_mem ha hb`. Consider the case `smul a z _ hz => rw [hΛ]`. Conclude with `Submodule.smul_mem _ _ hz`.

Take `⟨Φ, Ψ, h1, h2⟩` from `exists_ultraLimit_pair_of_eventual_quotient_maps Λ R σ s U f M X hU hΛ hX hpair`. Set `S` to `Localization.Away f`. Set `g` to `(TensorProduct.mk R S X 1) ∘ₗ Ψ`. Use `haveI : IsLocalizedModule (Submonoid.powers f) g := loc_of_pair f (TensorProduct.mk R S X 1) Φ Ψ h1 h2`. Take `⟨MM, i1, i2, i3, i4, q, hfin, hsurj, hker, hqr, hann⟩` from `exists_patched_module R σ (U : Filter ℕ) hU y m f M S _ rfl hq (S ⊗[R] X) g inferInstance`.

Set `BB` to `AdicCompletion (Ideal.map (algebraMap R S) (Ideal.span (Set.range y))) S`. Establish `hy : ∀ a (x : X), y a • x = 0` using `hX`. Take `⟨fibE⟩` from `fibEquiv R σ y f S BB X MM q (yCpl R σ y f) hy hsurj hker`. Establish `hqr' : GlobalTheory.IsQuasiRegularSeq MM fun a => algebraMap R BB (y a)`. Rewrite `hqr`, the goal using `[isQuasiRegularSeq_iff_qRegAt]`.

Introduce `a`. Use `((qRegAt_map S BB σ (fun b => algebraMap R S (y b)) ⊥ a).1 MM).1 (hqr a)` as an intermediate fact. Simplify `this` using `[Ideal.map_bot, ← IsScalarTower.algebraMap_apply]`. Establish `hnil' : ii ≤ Ideal.comap (algebraMap R BB) (Module.annihilator BB MM).radical`. Take `⟨e, Gs, hGs, hG⟩` from `hnil`.

Rewrite using `[← hGs, Ideal.span_le]`. Introduce `r hr`. Establish `key : ∀ x : MM, algebraMap R S ((f * r) ^ e) • x = 0`. Apply `hann` to reduce the goal to its premises. Introduce `k`.

Use `⟨k, fun j => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `finite_quotient_of_ultrafilter_limit_module Λ R σ s U f M X hΛ hX hpair k j`. Use `filter_upwards [hc, hG r hr c] with N hN hN'`. Take `⟨a, ha, ha0⟩` from `hN'`. Introduce `x`.

Establish `hmem` using `hN _ ha x`. Establish `heq : (f ^ k * (f * r) ^ e) • x = (f ^ k * ((f * r) ^ e - a)) • x`. Rewrite using `[mul_sub, sub_smul, mul_smul (f ^ k) a, ha0, smul_zero, sub_zero]`. Rewrite using `[heq]`. Conclude with `hmem`.

Rewrite using `[SetLike.mem_coe, Ideal.mem_comap]`. Use `⟨e, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.mem_annihilator]`. Introduce `x`. Establish `hu : IsUnit ((algebraMap R S f) ^ e)` using `(IsLocalization.Away.algebraMap_isUnit f).pow e`.

Establish `hx : (algebraMap R BB r) ^ e • x = ((algebraMap R S r) ^ e) • x`. Rewrite using `[IsScalarTower.algebraMap_apply R S BB, ← map_pow, algebraMap_smul]`. Rewrite using `[hx, ← hu.smul_eq_zero, smul_smul, ← mul_pow, ← map_mul, ← map_pow]`. Conclude with `key x`. Conclude with `⟨⟨BB, yCpl R σ y f, MM, hfin, hqr', fibE, hnil'⟩⟩`.
-/
theorem UpperTheory.V.Pa.Core.pmodEx :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] [IsLocalRing R] [IsNoetherianRing R] (U : Ultrafilter ℕ) (f : R) (ii : Ideal R) (M : ℕ → Type) [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] (X : Type) [AddCommGroup X] [Module R X] [Module Λ X] [Module.Finite Λ X], (U : Filter ℕ) ≤ atTop → (∀ (a : Λ) (x : X), a • x = s (MvPowerSeries.C a) • x) → (∀ a (x : X), s (MvPowerSeries.X a) • x = 0) → (∀ k j, ∀ᶠ N in (U : Filter ℕ), ∃ (r : ℕ) (e : (M N ⧸ ((kjIdeal Λ σ k j).map s • ⊤ : Submodule R (M N))) ≃+ (Fin r → MvPowerSeries σ Λ ⧸ kjIdeal Λ σ k j)), ∀ a m, e (s a • m) = a • e m) → (∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ (φ : (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z) → (∃ (e : ℕ) (Gs : Set R), Ideal.span Gs = ii ∧ ∀ r ∈ Gs, ∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ a : R, (f * r) ^ e - a ∈ maximalIdeal R ^ j ∧ ∀ m : M N, a • m = 0) → Nonempty (PMod (fun a => s (MvPowerSeries.X a)) f ii X) := by
  intro Λ R σ _ _ _ _ s _ _ _ _ _ U f ii M _ _ X _ _ _ _ hU hΛ hX hk hpair hnil
  classical
  let y : σ → R := fun a => s (MvPowerSeries.X a)
  let m : Ideal R := Ideal.map (s.comp MvPowerSeries.C) (maximalIdeal Λ)
  have hq : ∀ a j, ∀ᶠ N in (U : Filter ℕ), QRegAt (M N) y (m ^ j) a := by
    intro a j
    filter_upwards [hk (a + 1) j] with N hN
    obtain ⟨r, e, he⟩ := hN
    exact quotientRegularAt_of_quotient_free_over_powerSeries Λ R σ s (M N) a j r e he
  have hXR : Module.Finite R X := by
    obtain ⟨T, hT⟩ := (Module.Finite.fg_top : (⊤ : Submodule Λ X).FG)
    refine ⟨⟨T, ?_⟩⟩
    rw [eq_top_iff]
    rintro x -
    have hx : x ∈ Submodule.span Λ (T : Set X) := hT ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span hz
    | zero => exact zero_mem _
    | add _ _ _ _ ha hb => exact add_mem ha hb
    | smul a z _ hz => rw [hΛ]; exact Submodule.smul_mem _ _ hz
  obtain ⟨Φ, Ψ, h1, h2⟩ := exists_ultraLimit_pair_of_eventual_quotient_maps Λ R σ s U f M X hU hΛ hX hpair
  let S := Localization.Away f
  let g := (TensorProduct.mk R S X 1) ∘ₗ Ψ
  haveI : IsLocalizedModule (Submonoid.powers f) g :=
    loc_of_pair f (TensorProduct.mk R S X 1) Φ Ψ h1 h2
  obtain ⟨MM, i1, i2, i3, i4, q, hfin, hsurj, hker, hqr, hann⟩ :=
    exists_patched_module R σ (U : Filter ℕ) hU y m f M S _ rfl hq (S ⊗[R] X) g inferInstance
  let BB := AdicCompletion (Ideal.map (algebraMap R S) (Ideal.span (Set.range y))) S
  have hy : ∀ a (x : X), y a • x = 0 := hX
  obtain ⟨fibE⟩ := fibEquiv R σ y f S BB X MM q (yCpl R σ y f) hy hsurj hker
  have hqr' : GlobalTheory.IsQuasiRegularSeq MM fun a => algebraMap R BB (y a) := by
    rw [isQuasiRegularSeq_iff_qRegAt] at hqr ⊢
    intro a
    have := ((qRegAt_map S BB σ (fun b => algebraMap R S (y b)) ⊥ a).1 MM).1 (hqr a)
    simpa [Ideal.map_bot, ← IsScalarTower.algebraMap_apply] using this
  have hnil' : ii ≤ Ideal.comap (algebraMap R BB) (Module.annihilator BB MM).radical := by
    obtain ⟨e, Gs, hGs, hG⟩ := hnil
    rw [← hGs, Ideal.span_le]
    intro r hr
    have key : ∀ x : MM, algebraMap R S ((f * r) ^ e) • x = 0 := by
      apply hann
      intro k
      refine ⟨k, fun j => ?_⟩
      obtain ⟨c, hc⟩ := finite_quotient_of_ultrafilter_limit_module Λ R σ s U f M X hΛ hX hpair k j
      filter_upwards [hc, hG r hr c] with N hN hN'
      obtain ⟨a, ha, ha0⟩ := hN'
      intro x
      have hmem := hN _ ha x
      have heq : (f ^ k * (f * r) ^ e) • x = (f ^ k * ((f * r) ^ e - a)) • x := by
        rw [mul_sub, sub_smul, mul_smul (f ^ k) a, ha0, smul_zero, sub_zero]
      rw [heq]
      exact hmem
    rw [SetLike.mem_coe, Ideal.mem_comap]
    refine ⟨e, ?_⟩
    rw [Module.mem_annihilator]
    intro x
    have hu : IsUnit ((algebraMap R S f) ^ e) := (IsLocalization.Away.algebraMap_isUnit f).pow e
    have hx : (algebraMap R BB r) ^ e • x = ((algebraMap R S r) ^ e) • x := by
      rw [IsScalarTower.algebraMap_apply R S BB, ← map_pow, algebraMap_smul]
    rw [hx, ← hu.smul_eq_zero, smul_smul, ← mul_pow, ← map_mul, ← map_pow]
    exact key x
  exact ⟨⟨BB, yCpl R σ y f, MM, hfin, hqr', fibE, hnil'⟩⟩
