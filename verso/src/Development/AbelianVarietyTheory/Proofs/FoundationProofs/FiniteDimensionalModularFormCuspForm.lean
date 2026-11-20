import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EtaSixProductDifferentiable
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.FinDim

open Asymptotics Filter Topology Function

/- English proof (translation)
Establish `ha` using `ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ`. Establish `h1 : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction h f) 0`. Rewrite using `[natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha]`. Introduce `i hi`. Use `hc i hi` as an intermediate fact.

Rewrite `this` using `[qExpansion_coeff]`. Conclude with `(mul_eq_zero.mp this).resolve_left (inv_ne_zero (by exact_mod_cast i.factorial_ne_zero))`. Take `⟨g, hg, hfg⟩` from `(natCast_le_analyticOrderAt ha).mp h1`. Establish `ht` using `qParam_tendsto_atImInfty hh`. Establish `h2 : (fun τ : ℍ => g (Periodic.qParam h τ)) =O[atImInfty] (fun _ => (1 : ℂ))` using `(hg.continuousAt.tendsto.comp ht).isBigO_one ℂ`.

Establish `h3` using `(isBigO_refl (fun τ : ℍ => Periodic.qParam h τ ^ m) atImInfty).mul h2`. Simplify using `only [mul_one] at h3`. Use `h3.congr' ?_ EventuallyEq.rfl` and prove the remaining obligations. Use `filter_upwards [ht.eventually hfg] with τ hτ`. Rewrite `hτ` using `[SlashInvariantFormClass.eq_cuspFunction f τ hΓ hh.ne']`.

Rewrite using `[hτ]`. Simplify using the standard rewrite rules.
-/
theorem bigO_qParam_pow {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [ModularFormClass F Γ k] {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (f : F) (m : ℕ)
    (hc : ∀ n < m, (qExpansion h f).coeff n = 0) :
    (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam h τ ^ m := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ
  have h1 : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction h f) 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha]
    intro i hi
    have := hc i hi
    rw [qExpansion_coeff] at this
    exact (mul_eq_zero.mp this).resolve_left (inv_ne_zero (by exact_mod_cast i.factorial_ne_zero))
  obtain ⟨g, hg, hfg⟩ := (natCast_le_analyticOrderAt ha).mp h1
  have ht := qParam_tendsto_atImInfty hh
  have h2 : (fun τ : ℍ => g (Periodic.qParam h τ)) =O[atImInfty] (fun _ => (1 : ℂ)) :=
    (hg.continuousAt.tendsto.comp ht).isBigO_one ℂ
  have h3 := (isBigO_refl (fun τ : ℍ => Periodic.qParam h τ ^ m) atImInfty).mul h2
  simp only [mul_one] at h3
  refine h3.congr' ?_ EventuallyEq.rfl
  filter_upwards [ht.eventually hfg] with τ hτ
  rw [SlashInvariantFormClass.eq_cuspFunction f τ hΓ hh.ne'] at hτ
  rw [hτ]; simp

/- English proof (translation)
Establish `ha` using `ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ`. Establish `h1 : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 f) 0`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Take `⟨j, hj⟩` from `ENat.ne_top_iff_exists.mp hlt.ne_top`.

Rewrite `hlt` using `[← hj]`. Establish `hjm : j < m` using `by exact_mod_cast hlt`. Take `⟨g, hg, hg0, hfg⟩` from `ha.analyticOrderAt_eq_natCast.mp hj.symm`. Establish `ht` using `qParam_tendsto_atImInfty (h := 1) one_pos`. Establish `h2 : (fun τ : ℍ => g (Periodic.qParam 1 τ)) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ (m - j)`.

Establish `h3` using `(isBigO_refl (fun τ : ℍ => (Periodic.qParam 1 τ ^ j)⁻¹) atImInfty).mul h`. Use `h3.congr' ?_ ?_` and prove the remaining obligations. Use `filter_upwards [ht.eventually hfg] with τ hτ`. Rewrite `hτ` using `[SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero]`. Establish `hq : Periodic.qParam 1 τ ≠ 0` using `Periodic.qParam_ne_zero _`.

Rewrite using `[hτ, sub_zero, smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero _ hq)]`. Use `Eventually.of_forall fun τ => ?_` and prove the remaining obligations. Establish `hq : Periodic.qParam 1 τ ≠ 0` using `Periodic.qParam_ne_zero _`. Simplify using `only`. Rewrite using `[pow_sub₀ _ hq hjm.le, mul_comm]`.

Establish `h4 : Tendsto (fun τ : ℍ => Periodic.qParam 1 τ ^ (m - j)) atImInfty (𝓝 0)`. Use `ht.pow (m - j)` as an intermediate fact. Rewrite `this` using `[zero_pow (by omega)]`. Then use the resulting hypothesis. Conclude with `hg0 (tendsto_nhds_unique (hg.continuousAt.tendsto.comp ht) (h2.trans_tendsto h4))`. Rewrite `h1` using `[natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha]`.

Introduce `n hn`. Rewrite using `[qExpansion_coeff, h1 n hn, mul_zero]`.
-/
theorem coeff_eq_zero_of_bigO {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [ModularFormClass F Γ k] (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (m : ℕ)
    (h : (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ m) :
    ∀ n < m, (qExpansion 1 f).coeff n = 0 := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  have h1 : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 f) 0 := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hlt.ne_top
    rw [← hj] at hlt
    have hjm : j < m := by exact_mod_cast hlt
    obtain ⟨g, hg, hg0, hfg⟩ := ha.analyticOrderAt_eq_natCast.mp hj.symm
    have ht := qParam_tendsto_atImInfty (h := 1) one_pos
    have h2 : (fun τ : ℍ => g (Periodic.qParam 1 τ)) =O[atImInfty]
        fun τ : ℍ => Periodic.qParam 1 τ ^ (m - j) := by
      have h3 := (isBigO_refl (fun τ : ℍ => (Periodic.qParam 1 τ ^ j)⁻¹) atImInfty).mul h
      refine h3.congr' ?_ ?_
      · filter_upwards [ht.eventually hfg] with τ hτ
        rw [SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero] at hτ
        have hq : Periodic.qParam 1 τ ≠ 0 := Periodic.qParam_ne_zero _
        rw [hτ, sub_zero, smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero _ hq)]
      · refine Eventually.of_forall fun τ => ?_
        have hq : Periodic.qParam 1 τ ≠ 0 := Periodic.qParam_ne_zero _
        simp only
        rw [pow_sub₀ _ hq hjm.le, mul_comm]
    have h4 : Tendsto (fun τ : ℍ => Periodic.qParam 1 τ ^ (m - j)) atImInfty (𝓝 0) := by
      have := ht.pow (m - j)
      rwa [zero_pow (by omega)] at this
    exact hg0 (tendsto_nhds_unique (hg.continuousAt.tendsto.comp ht) (h2.trans_tendsto h4))
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha] at h1
  intro n hn
  rw [qExpansion_coeff, h1 n hn, mul_zero]

/- English proof (translation)
Use `IsBigO.of_bound 1 (Eventually.of_forall fun τ => ?_)` and prove the remaining obligations. Rewrite using `[one_mul, norm_pow, norm_pow, Periodic.norm_qParam, Periodic.norm_qParam, ← Real.exp_nat_mul, ← Real.exp_nat_mul, Real.exp_le_exp]`. Establish `hy : 0 < (τ : ℂ).im` using `τ.im_pos`. Establish `key : (M : ℝ) * (τ : ℂ).im ≤ m * (τ : ℂ).im / h`. Rewrite using `[le_div_iff₀ hh]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `e1 : (m : ℝ) * (-2 * Real.pi * (τ : ℂ).im / h) = -2 * Real.pi * (m * (τ : ℂ).im / h)` using `by ring`. Establish `e2 : (M : ℝ) * (-2 * Real.pi * (τ : ℂ).im / 1) = -2 * Real.pi * (M * (τ : ℂ).im)` using `by ring`. Rewrite using `[e1, e2]`. Use polynomial arithmetic with `[Real.pi_pos]`.
-/
theorem qParam_pow_bigO {h : ℝ} (hh : 0 < h) {m M : ℕ} (hm : (M : ℝ) * h ≤ m) :
    (fun τ : ℍ => Periodic.qParam h τ ^ m) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ M := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun τ => ?_)
  rw [one_mul, norm_pow, norm_pow, Periodic.norm_qParam, Periodic.norm_qParam, ← Real.exp_nat_mul,
    ← Real.exp_nat_mul, Real.exp_le_exp]
  have hy : 0 < (τ : ℂ).im := τ.im_pos
  have key : (M : ℝ) * (τ : ℂ).im ≤ m * (τ : ℂ).im / h := by
    rw [le_div_iff₀ hh]; nlinarith
  have e1 : (m : ℝ) * (-2 * Real.pi * (τ : ℂ).im / h) = -2 * Real.pi * (m * (τ : ℂ).im / h) := by ring
  have e2 : (M : ℝ) * (-2 * Real.pi * (τ : ℂ).im / 1) = -2 * Real.pi * (M * (τ : ℂ).im) := by ring
  rw [e1, e2]
  nlinarith [Real.pi_pos]

/- English proof (translation)
Set `` to `Fintype.ofFinite (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))`. Establish `hb : ∀ q : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ), SlashInvariantForm.quotientFunc (k` using `k) f q =O[atImInfty] fun _ => (1 : ℂ) := by`. Use `Quotient.forall.mpr fun ⟨r, hr⟩ => ?_` and prove the remaining obligations. Establish `hc : IsCusp OnePoint.infty 𝒮ℒ` using `Fact.out`. Use `(ModularForm.translate f r⁻¹).bdd_at_cusps' (c := OnePoint.infty) (by simpa using hc.of_isFiniteRelIndex_conj hr)` as an intermediate fact.

Rewrite `this` using `[OnePoint.isBoundedAt_infty_iff]`. Establish `h2 : (ModularForm.translate f r⁻¹ : ℍ → ℂ) =O[atImInfty] (1 : ℍ → ℝ)` using `this`. Use `IsBigO.trans h2 ?_` and prove the remaining obligations. Conclude with `IsBigO.of_bound 1 (by simp)`. Establish `h1 : (∏ q ∈ Finset.univ.erase (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)), SlashInvariantForm.quotientFunc (k` using `k) f q) =O[atImInfty] fun _ => (1 : ℂ) := by`.

Use `IsBigO.finsetProd (s := Finset.univ.erase (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))) (fun q _ => hb q)` as an intermediate fact. Simplify `this` using `[Finset.prod_fn]`. Establish `h2` using `(isBigO_refl (f : ℍ → ℂ) atImInfty).mul h1`. Simplify using `only [mul_one] at h2`. Use `h2.congr_left fun τ => ?_` and prove the remaining obligations.

Establish `h3` using `congr_fun (Finset.mul_prod_erase Finset.univ (fun q => SlashInvariantForm.quotientFunc (k := k) f q) (Finset.mem_univ (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)))) τ`. Rewrite using `[ModularForm.coe_norm]`. Establish `h4 : SlashInvariantForm.quotientFunc (k` using `k) f (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)) = f := by simp`. Rewrite `h3` using `[h4, Pi.mul_apply]`. Use `h3` and compare the differences between its conclusion and the goal.
-/
theorem norm_bigO {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    [Γ.IsArithmetic] (f : F) : (ModularForm.norm 𝒮ℒ f : ℍ → ℂ) =O[atImInfty] (f : ℍ → ℂ) := by
  classical
  let := Fintype.ofFinite (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))
  have hb : ∀ q : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ),
      SlashInvariantForm.quotientFunc (k := k) f q =O[atImInfty] fun _ => (1 : ℂ) := by
    refine Quotient.forall.mpr fun ⟨r, hr⟩ => ?_
    have hc : IsCusp OnePoint.infty 𝒮ℒ := Fact.out
    have := (ModularForm.translate f r⁻¹).bdd_at_cusps' (c := OnePoint.infty)
      (by simpa using hc.of_isFiniteRelIndex_conj hr)
    rw [OnePoint.isBoundedAt_infty_iff] at this
    have h2 : (ModularForm.translate f r⁻¹ : ℍ → ℂ) =O[atImInfty] (1 : ℍ → ℝ) := this
    refine IsBigO.trans h2 ?_
    exact IsBigO.of_bound 1 (by simp)
  have h1 : (∏ q ∈ Finset.univ.erase (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)),
      SlashInvariantForm.quotientFunc (k := k) f q) =O[atImInfty] fun _ => (1 : ℂ) := by
    have := IsBigO.finsetProd (s := Finset.univ.erase (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))) (fun q _ => hb q)
    simpa [Finset.prod_fn] using this
  have h2 := (isBigO_refl (f : ℍ → ℂ) atImInfty).mul h1
  simp only [mul_one] at h2
  refine h2.congr_left fun τ => ?_
  have h3 := congr_fun (Finset.mul_prod_erase Finset.univ (fun q => SlashInvariantForm.quotientFunc (k := k) f q)
    (Finset.mem_univ (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)))) τ
  rw [ModularForm.coe_norm]
  have h4 : SlashInvariantForm.quotientFunc (k := k) f (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)) = f := by simp
  rw [h4, Pi.mul_apply] at h3
  convert h3

/- English proof (translation)
Use `set M := (k * Nat.card (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))).toNat / 12 + 1`. Use `⟨⌈(M : ℝ) * h⌉₊, fun f hf => ?_⟩` and prove the remaining obligations. Establish `h1` using `coeff_eq_zero_of_bigO one_mem_strictPeriods_SL (ModularForm.norm 𝒮ℒ f) M ((norm_bigO f).trans ((bigO_qParam_pow hh hΓ f _ hf).trans (qParam_pow_bigO hh (Nat.le_ceil _))))`. Establish `h2 : ModularForm.norm 𝒮ℒ f = 0`. Apply `ModularForm.sturm_bound_levelOne` to reduce the goal to its premises.

Use `lt_of_lt_of_le ?_ (PowerSeries.nat_le_order _ _ h1)` and prove the remaining obligations. Conclude with `Nat.lt_succ_self _` after adjusting the coercions. Rewrite `h2` using `[ModularForm.norm_eq_zero_iff]`. Use extensionality with `τ`. Simplify using `using congr_fun h2 τ`.
-/
theorem sturm {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (k : ℤ) :
    ∃ m : ℕ, ∀ f : ModularForm Γ k, (∀ n < m, (qExpansion h f).coeff n = 0) → f = 0 := by
  set M := (k * Nat.card (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))).toNat / 12 + 1
  refine ⟨⌈(M : ℝ) * h⌉₊, fun f hf => ?_⟩
  have h1 := coeff_eq_zero_of_bigO one_mem_strictPeriods_SL (ModularForm.norm 𝒮ℒ f) M
    ((norm_bigO f).trans ((bigO_qParam_pow hh hΓ f _ hf).trans (qParam_pow_bigO hh (Nat.le_ceil _))))
  have h2 : ModularForm.norm 𝒮ℒ f = 0 := by
    apply ModularForm.sturm_bound_levelOne
    refine lt_of_lt_of_le ?_ (PowerSeries.nat_le_order _ _ h1)
    exact_mod_cast Nat.lt_succ_self _
  rw [ModularForm.norm_eq_zero_iff] at h2
  ext τ
  simpa using congr_fun h2 τ

def coeffMap {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (k : ℤ)
    (m : ℕ) : ModularForm Γ k →ₗ[ℂ] (Fin m → ℂ) where
  toFun f n := (qExpansion h f).coeff n
  map_add' f g := by
    funext n
    simp only [Pi.add_apply]
    rw [ModularForm.coe_add, ModularForm.qExpansion_add hh hΓ f g, map_add]
  map_smul' c f := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [ModularForm.coe_smul, ModularForm.qExpansion_smul hh hΓ c f, PowerSeries.coeff_smul, smul_eq_mul]

/- English proof (translation)
Take `⟨m, hm⟩` from `sturm Γ.strictWidthInfty_pos Γ.strictWidthInfty_mem_strictPeriods k`. Use `Module.Finite.of_injective (coeffMap Γ.strictWidthInfty_pos Γ.strictWidthInfty_mem_strictPeriods k m) ?_` and prove the remaining obligations. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `f hf`. Conclude with `hm f fun n hn => congr_fun hf ⟨n, hn⟩`.
-/
theorem finiteDimensional_of_isArithmetic (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] [Γ.HasDetOne]
    (k : ℤ) :
    FiniteDimensional ℂ (ModularForm Γ k) := by
  obtain ⟨m, hm⟩ := sturm Γ.strictWidthInfty_pos Γ.strictWidthInfty_mem_strictPeriods k
  refine Module.Finite.of_injective (coeffMap Γ.strictWidthInfty_pos Γ.strictWidthInfty_mem_strictPeriods k m) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  exact hm f fun n hn => congr_fun hf ⟨n, hn⟩

end GlobalTheory.HeckeFamilyMatrices.FinDim

open GlobalTheory.HeckeFamilyMatrices.FinDim in

/- English proof (translation)
Introduce `Γ k hΓ`. Establish `h1` using `finiteDimensional_of_isArithmetic (Γ : Subgroup (GL (Fin 2) ℝ)) k`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Use `haveI := h1`. Conclude with `Module.Finite.equiv (CuspForm.equivCuspFormSubmodule (Γ : Subgroup (GL (Fin 2) ℝ)) k).symm`.
-/
theorem GlobalTheory.HeckeFamilyMatrices.finiteDimensional_modularForm_cuspForm :
    ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℤ), Γ.FiniteIndex →
      FiniteDimensional ℂ (ModularForm Γ k) ∧ FiniteDimensional ℂ (CuspForm Γ k) := by
  intro Γ k hΓ
  have h1 := finiteDimensional_of_isArithmetic (Γ : Subgroup (GL (Fin 2) ℝ)) k
  refine ⟨h1, ?_⟩
  haveI := h1
  exact Module.Finite.equiv (CuspForm.equivCuspFormSubmodule (Γ : Subgroup (GL (Fin 2) ℝ)) k).symm
