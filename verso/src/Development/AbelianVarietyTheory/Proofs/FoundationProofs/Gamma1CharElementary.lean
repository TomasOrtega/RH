import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Establish `h` using `ModularForm.hasSum_qExpansion f one_pos (by simp) τ`. Rewrite using `[qs, ← h.tsum_eq]`. Use `congr 1`. Use function extensionality and compare the values at `n`.

Rewrite using `[coef, Function.Periodic.qParam, ← Complex.exp_nat_mul]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qs_coef_of_mfc {k M : ℕ} [NeZero M] {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F (Gamma1 M) (k : ℤ)] (f : F) : qs (coef f) = ⇑f := by
  funext τ
  have h := ModularForm.hasSum_qExpansion f one_pos (by simp) τ
  rw [qs, ← h.tsum_eq]
  congr 1
  funext n
  rw [coef, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/- English proof (translation)
Take `⟨c, hc⟩` from `h.bound`. Rewrite `hc` using `[eventually_atTop]`. Take `⟨N, hN⟩` from `hc`. Establish `hS : 0 ≤ ∑ n ∈ Finset.range N, ‖a n‖` using `Finset.sum_nonneg fun _ _ => norm_nonneg _`. Use `⟨|c| + ∑ n ∈ Finset.range N, ‖a n‖, k, fun n => ?_⟩` and prove the remaining obligations.

Establish `hn0 : (0 : ℝ) ≤ n` using `n.cast_nonneg`. Establish `h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ k` using `one_le_pow₀ (by linarith)`. Distinguish the cases in `hn : N ≤ n`. Establish `h2` using `hN n hn`. Rewrite `h2` using `[Real.norm_of_nonneg (by positivity)]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ‖a n‖ ≤ ∑ n ∈ Finset.range N, ‖a n‖` using `Finset.single_le_sum (f := fun n => ‖a n‖) (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem polyB_of_isBigO {a : ℕ → ℂ} {k : ℕ}
    (h : (fun n => a n) =O[atTop] fun n : ℕ => (n : ℝ) ^ k) : PolyB a := by
  obtain ⟨c, hc⟩ := h.bound
  rw [eventually_atTop] at hc
  obtain ⟨N, hN⟩ := hc
  have hS : 0 ≤ ∑ n ∈ Finset.range N, ‖a n‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨|c| + ∑ n ∈ Finset.range N, ‖a n‖, k, fun n => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ k := one_le_pow₀ (by linarith)
  by_cases hn : N ≤ n
  · have h2 := hN n hn
    rw [Real.norm_of_nonneg (by positivity)] at h2
    calc ‖a n‖ ≤ c * (n : ℝ) ^ k := h2
      _ ≤ |c| * ((n : ℝ) + 1) ^ k :=
          mul_le_mul (le_abs_self c) (pow_le_pow_left₀ hn0 (by linarith) k) (by positivity) (abs_nonneg c)
      _ ≤ (|c| + ∑ n ∈ Finset.range N, ‖a n‖) * ((n : ℝ) + 1) ^ k :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have h2 : ‖a n‖ ≤ ∑ n ∈ Finset.range N, ‖a n‖ :=
      Finset.single_le_sum (f := fun n => ‖a n‖) (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
    calc ‖a n‖ ≤ |c| + ∑ n ∈ Finset.range N, ‖a n‖ := by linarith [abs_nonneg c]
      _ ≤ (|c| + ∑ n ∈ Finset.range N, ‖a n‖) * ((n : ℝ) + 1) ^ k :=
          le_mul_of_one_le_right (by positivity) h1

/- English proof (translation)
Introduce `γ hγ τ`. Establish `hmem : γ ∈ Gamma0 M`. Rewrite using `[Gamma0_mem]`. Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hγ`. Establish `h` using `congrFun (hf γ hmem) τ`.

Rewrite `h` using `[ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul]`. Establish `hd : denom (γ : GL (Fin 2) ℝ) τ = ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)`. Simplify using `[denom]`. Establish `hne : denom (γ : GL (Fin 2) ℝ) τ ≠ 0` using `denom_ne_zero _ τ`. Rewrite using `[← hd, ch]`.

Rewrite `h` using `[zpow_neg, zpow_natCast]`. Establish `hk : denom (γ : GL (Fin 2) ℝ) τ ^ k ≠ 0` using `pow_ne_zero _ hne`. Clear denominators, using `at h` for the nonvanishing conditions. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inv_of_hasChar {k M : ℕ} (χ : DirichletCharacter ℂ M) (f : ℍ → ℂ) (hf : HasChar k χ f) :
    Inv k M (ch χ) f := by
  intro γ hγ τ
  have hmem : γ ∈ Gamma0 M := by
    rw [Gamma0_mem]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hγ
  have h := congrFun (hf γ hmem) τ
  rw [ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul] at h
  have hd : denom (γ : GL (Fin 2) ℝ) τ = ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
    simp [denom]
  have hne : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
  rw [← hd, ch]
  rw [zpow_neg, zpow_natCast] at h
  have hk : denom (γ : GL (Fin 2) ℝ) τ ^ k ≠ 0 := pow_ne_zero _ hne
  field_simp at h
  rw [h]
  ring

/- English proof (translation)
Establish `hq` using `qs_coef_of_mfc (k := k) f`. Use `⟨hq, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `ModularFormClass.qExpansion_isBigO (Int.natCast_nonneg k) f`. Simplify using `only [strictWidthInfty_Gamma1, zpow_natCast] at h`. Conclude with `polyB_of_isBigO h`.

Rewrite using `[hq]`. Conclude with `inv_of_hasChar χ f hf`.
-/
theorem mf_of_mfc {k M : ℕ} [NeZero M] {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F (Gamma1 M) (k : ℤ)] (χ : DirichletCharacter ℂ M) (f : F) (hf : HasChar k χ f) :
    qs (coef f) = ⇑f ∧ MF k M (ch χ) (coef f) := by
  have hq := qs_coef_of_mfc (k := k) f
  refine ⟨hq, ?_, ?_⟩
  · have h := ModularFormClass.qExpansion_isBigO (Int.natCast_nonneg k) f
    simp only [strictWidthInfty_Gamma1, zpow_natCast] at h
    exact polyB_of_isBigO h
  · rw [hq]; exact inv_of_hasChar χ f hf

/- English proof (translation)
Introduce `k M χ hM`. Use `haveI : NeZero M := ⟨hM.ne'⟩`. Use `⟨fun f hf => mf_of_mfc χ f hf, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨hq, hmf⟩` from `mf_of_mfc χ f hf`. Use `⟨hq, hmf, ?_⟩` and prove the remaining obligations.

Take `⟨C, hC⟩` from `CuspFormClass.petersson_bounded_left (k : ℤ) (Gamma1 M) f f`. Use `⟨C, fun τ => ?_⟩` and prove the remaining obligations. Establish `h` using `hC τ`. Rewrite using `[hq]`. Simplify using `only [petersson, norm_mul, Complex.norm_conj, norm_zpow, Complex.norm_real, zpow_natCast, norm_pow, Real.norm_of_nonneg τ.im_pos.le] at h`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem gamma1_char_elementary : ∀ (k M : ℕ) (χ : DirichletCharacter ℂ M), 0 < M →
    (∀ f : ModularForm (Gamma1 M) (k : ℤ), HasChar k χ f → qs (coef f) = ⇑f ∧ MF k M (ch χ) (coef f)) ∧
    ∀ f : CuspForm (Gamma1 M) (k : ℤ), HasChar k χ f → qs (coef f) = ⇑f ∧ CF k M (ch χ) (coef f) := by
  intro k M χ hM
  haveI : NeZero M := ⟨hM.ne'⟩
  refine ⟨fun f hf => mf_of_mfc χ f hf, fun f hf => ?_⟩
  obtain ⟨hq, hmf⟩ := mf_of_mfc χ f hf
  refine ⟨hq, hmf, ?_⟩
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left (k : ℤ) (Gamma1 M) f f
  refine ⟨C, fun τ => ?_⟩
  have h := hC τ
  rw [hq]
  simp only [petersson, norm_mul, Complex.norm_conj, norm_zpow, Complex.norm_real,
    zpow_natCast, norm_pow, Real.norm_of_nonneg τ.im_pos.le] at h
  calc ‖f τ‖ ^ 2 * τ.im ^ k = ‖f τ‖ * ‖f τ‖ * τ.im ^ k := by ring
    _ ≤ C := h

end GlobalTheory.EisM
