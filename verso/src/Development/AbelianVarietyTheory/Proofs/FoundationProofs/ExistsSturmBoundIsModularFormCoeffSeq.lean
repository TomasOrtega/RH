import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormGammaOneOfCoeffSeqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefQExpansionFunctionUpperHalfPlaneStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

open Asymptotics Function

/- English proof (translation)
Establish `ha` using `ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ`. Establish `h1 : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 f) 0`. Rewrite using `[natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha]`. Introduce `i hi`. Use `h i hi` as an intermediate fact.

Rewrite `this` using `[qExpansion_coeff]`. Conclude with `(mul_eq_zero.mp this).resolve_left (inv_ne_zero (by exact_mod_cast i.factorial_ne_zero))`. Take `⟨g, hg, hfg⟩` from `(natCast_le_analyticOrderAt ha).mp h1`. Establish `ht` using `qParam_tendsto_atImInfty (h := 1) one_pos`. Establish `h2 : (fun τ : ℍ => g (Periodic.qParam 1 τ)) =O[atImInfty] (fun _ => (1 : ℂ))` using `(hg.continuousAt.tendsto.comp ht).isBigO_one ℂ`.

Establish `h3` using `(isBigO_refl (fun τ : ℍ => Periodic.qParam 1 τ ^ m) atImInfty).mul h2`. Simplify using `only [mul_one] at h3`. Use `h3.congr' ?_ EventuallyEq.rfl` and prove the remaining obligations. Use `filter_upwards [ht.eventually hfg] with τ hτ`. Rewrite `hτ` using `[SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero]`.

Rewrite using `[hτ]`. Simplify using the standard rewrite rules.
-/
theorem isBigO_qParam_pow_of_qExpansion_coeff_zero {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (m : ℕ) (h : ∀ n < m, (qExpansion 1 f).coeff n = 0) :
    (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ m := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  have h1 : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 f) 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha]
    intro i hi
    have := h i hi
    rw [qExpansion_coeff] at this
    exact (mul_eq_zero.mp this).resolve_left (inv_ne_zero (by exact_mod_cast i.factorial_ne_zero))
  obtain ⟨g, hg, hfg⟩ := (natCast_le_analyticOrderAt ha).mp h1
  have ht := qParam_tendsto_atImInfty (h := 1) one_pos
  have h2 : (fun τ : ℍ => g (Periodic.qParam 1 τ)) =O[atImInfty] (fun _ => (1 : ℂ)) :=
    (hg.continuousAt.tendsto.comp ht).isBigO_one ℂ
  have h3 := (isBigO_refl (fun τ : ℍ => Periodic.qParam 1 τ ^ m) atImInfty).mul h2
  simp only [mul_one] at h3
  refine h3.congr' ?_ EventuallyEq.rfl
  filter_upwards [ht.eventually hfg] with τ hτ
  rw [SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero] at hτ
  rw [hτ]; simp

/- English proof (translation)
Establish `ha` using `ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ`. Establish `h1 : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 f) 0`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Take `⟨j, hj⟩` from `ENat.ne_top_iff_exists.mp hlt.ne_top`.

Rewrite `hlt` using `[← hj]`. Establish `hjm : j < m` using `by exact_mod_cast hlt`. Take `⟨g, hg, hg0, hfg⟩` from `ha.analyticOrderAt_eq_natCast.mp hj.symm`. Establish `ht` using `qParam_tendsto_atImInfty (h := 1) one_pos`. Establish `h2 : (fun τ : ℍ => g (Periodic.qParam 1 τ)) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ (m - j)`.

Establish `h3` using `(isBigO_refl (fun τ : ℍ => (Periodic.qParam 1 τ ^ j)⁻¹) atImInfty).mul h`. Use `h3.congr' ?_ ?_` and prove the remaining obligations. Use `filter_upwards [ht.eventually hfg] with τ hτ`. Rewrite `hτ` using `[SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero]`. Establish `hq : Periodic.qParam 1 τ ≠ 0` using `Periodic.qParam_ne_zero _`.

Rewrite using `[hτ, sub_zero, smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero _ hq)]`. Use `Eventually.of_forall fun τ => ?_` and prove the remaining obligations. Establish `hq : Periodic.qParam 1 τ ≠ 0` using `Periodic.qParam_ne_zero _`. Simplify using `only`. Rewrite using `[pow_sub₀ _ hq hjm.le, mul_comm]`.

Establish `h4 : Tendsto (fun τ : ℍ => Periodic.qParam 1 τ ^ (m - j)) atImInfty (𝓝 0)`. Use `ht.pow (m - j)` as an intermediate fact. Rewrite `this` using `[zero_pow (by omega)]`. Then use the resulting hypothesis. Conclude with `hg0 (tendsto_nhds_unique (hg.continuousAt.tendsto.comp ht) (h2.trans_tendsto h4))`. Rewrite `h1` using `[natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha]`.

Introduce `n hn`. Rewrite using `[qExpansion_coeff, h1 n hn, mul_zero]`.
-/
theorem qExpansion_coeff_zero_of_isBigO_qParam_pow {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (m : ℕ)
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
Set `` to `Fintype.ofFinite (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))`. Establish `hb : ∀ q : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ), SlashInvariantForm.quotientFunc (k` using `k) f q =O[atImInfty] fun _ => (1 : ℂ) := by`. Use `Quotient.forall.mpr fun ⟨r, hr⟩ => ?_` and prove the remaining obligations. Establish `hc : IsCusp OnePoint.infty 𝒮ℒ` using `Fact.out`. Use `(ModularForm.translate f r⁻¹).bdd_at_cusps' (c := OnePoint.infty) (by simpa using hc.of_isFiniteRelIndex_conj hr)` as an intermediate fact.

Rewrite `this` using `[OnePoint.isBoundedAt_infty_iff]`. Establish `h2 : (ModularForm.translate f r⁻¹ : ℍ → ℂ) =O[atImInfty] (1 : ℍ → ℝ)` using `this`. Use `IsBigO.trans h2 ?_` and prove the remaining obligations. Conclude with `IsBigO.of_bound 1 (by simp)`. Establish `h1 : (∏ q ∈ Finset.univ.erase (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)), SlashInvariantForm.quotientFunc (k` using `k) f q) =O[atImInfty] fun _ => (1 : ℂ) := by`.

Use `IsBigO.finsetProd (s := Finset.univ.erase (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))) (fun q _ => hb q)` as an intermediate fact. Simplify `this` using `[Finset.prod_fn]`. Establish `h2` using `(isBigO_refl (f : ℍ → ℂ) atImInfty).mul h1`. Simplify using `only [mul_one] at h2`. Use `h2.congr_left fun τ => ?_` and prove the remaining obligations.

Establish `h3` using `congr_fun (Finset.mul_prod_erase Finset.univ (fun q => SlashInvariantForm.quotientFunc (k := k) f q) (Finset.mem_univ (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)))) τ`. Rewrite using `[ModularForm.coe_norm]`. Establish `h4 : SlashInvariantForm.quotientFunc (k` using `k) f (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)) = f := by simp`. Rewrite `h3` using `[h4, Pi.mul_apply]`. Use `h3` and compare the differences between its conclusion and the goal.
-/
theorem modularFormNorm_isBigO_self_atImInfty {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
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
Use `⟨(k * Nat.card (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))).toNat / 12 + 1, fun f hf => ?_⟩` and prove the remaining obligations. Establish `h1` using `qExpansion_coeff_zero_of_isBigO_qParam_pow one_mem_strictPeriods_SL (ModularForm.norm 𝒮ℒ f) _ ((modularFormNorm_isBigO_self_atImInfty f).trans (isBigO_qParam_pow_of_qExpansion_coeff_zero hΓ f _ hf))`. Establish `h2 : ModularForm.norm 𝒮ℒ f = 0`. Apply `ModularForm.sturm_bound_levelOne` to reduce the goal to its premises. Use `lt_of_lt_of_le ?_ (PowerSeries.nat_le_order _ _ h1)` and prove the remaining obligations.

Conclude with `Nat.lt_succ_self _` after adjusting the coercions. Rewrite `h2` using `[ModularForm.norm_eq_zero_iff]`. Use extensionality with `τ`. Simplify using `using congr_fun h2 τ`.
-/
theorem exists_sturmBound_modularForm_arithmetic {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (k : ℤ) :
    ∃ m : ℕ, ∀ f : ModularForm Γ k, (∀ n < m, (qExpansion 1 f).coeff n = 0) → f = 0 := by
  refine ⟨(k * Nat.card (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))).toNat / 12 + 1, fun f hf => ?_⟩
  have h1 := qExpansion_coeff_zero_of_isBigO_qParam_pow one_mem_strictPeriods_SL (ModularForm.norm 𝒮ℒ f) _
    ((modularFormNorm_isBigO_self_atImInfty f).trans (isBigO_qParam_pow_of_qExpansion_coeff_zero hΓ f _ hf))
  have h2 : ModularForm.norm 𝒮ℒ f = 0 := by
    apply ModularForm.sturm_bound_levelOne
    refine lt_of_lt_of_le ?_ (PowerSeries.nat_le_order _ _ h1)
    exact_mod_cast Nat.lt_succ_self _
  rw [ModularForm.norm_eq_zero_iff] at h2
  ext τ
  simpa using congr_fun h2 τ

/- English proof (translation)
Introduce `k L N ε hL hN`. Establish `hΓ : (1 : ℝ) ∈ (Gamma1 L : Subgroup (GL (Fin 2) ℝ)).strictPeriods`. Simplify using `[strictPeriods_Gamma1]`. Use `haveI : NeZero L := ⟨hL.ne'⟩`. Take `⟨m, hm⟩` from `exists_sturmBound_modularForm_arithmetic hΓ (k : ℤ)`.

Use `⟨m, fun a ha hz => ?_⟩` and prove the remaining obligations. Take `⟨f, hf⟩` from `GlobalTheory.T.modularForm_gammaOne_of_coeffSeq k L N ε a hL hN ha`. Establish `hc : ∀ n, (qExpansion 1 f).coeff n = a n`. Introduce `n`. Use `GlobalTheory.T.coef_qExpansionFunctionUpperHalfPlane a ha.1 n` as an intermediate fact.

Unfold `coef at this`. Rewrite using `[← this, hf]`. Establish `h0 : f = 0` using `hm f fun n hn => by rw [hc n]; exact hz n hn`. Use function extensionality and compare the values at `n`. Rewrite using `[← hc n, h0]`.

Simplify using `[qExpansion_zero]`.
-/
theorem sturm_coef_zero : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N), 0 < L → N ∣ L →
    ∃ B : ℕ, ∀ a, MF k L (ch ε) a → (∀ n < B, a n = 0) → a = 0 := by
  intro k L N ε hL hN
  have hΓ : (1 : ℝ) ∈ (Gamma1 L : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [strictPeriods_Gamma1]
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨m, hm⟩ := exists_sturmBound_modularForm_arithmetic hΓ (k : ℤ)
  refine ⟨m, fun a ha hz => ?_⟩
  obtain ⟨f, hf⟩ := GlobalTheory.T.modularForm_gammaOne_of_coeffSeq k L N ε a hL hN ha
  have hc : ∀ n, (qExpansion 1 f).coeff n = a n := by
    intro n
    have := GlobalTheory.T.coef_qExpansionFunctionUpperHalfPlane a ha.1 n
    unfold coef at this
    rw [← this, hf]
  have h0 : f = 0 := hm f fun n hn => by rw [hc n]; exact hz n hn
  funext n
  rw [← hc n, h0]
  simp [qExpansion_zero]

end GlobalTheory.EisM
