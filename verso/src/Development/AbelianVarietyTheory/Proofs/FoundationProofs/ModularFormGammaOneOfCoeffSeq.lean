import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableQExpansionOfCoeffPolynomialGrowthStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthQExpansionOfCoeffPolynomialGrowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsBoundedAtImInftyOfPeriodicPolynomialBoundStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.OnGammaOne

/- English proof (translation)
Take `⟨-, h11, h10⟩` from `(Gamma1_mem L γ).1 hγ`. Establish `hc : (L : ℤ) ∣ γ 1 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h10`. Establish `hd1 : (L : ℤ) ∣ γ 1 1 - 1`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`.

Rewrite using `[h11, sub_self]`. Establish `hd : ch ε (γ 1 1) = 1`. Establish `h2 : (N : ℤ) ∣ γ 1 1 - 1` using `(Int.natCast_dvd_natCast.2 hNL).trans hd1`. Rewrite `h2` using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Move the coercions through the operations in `at h2`.

Establish `h3 : ((γ 1 1 : ℤ) : ZMod N) = 1` using `sub_eq_zero.1 h2`. Simplify using `[ch, h3]`. Use function extensionality and compare the values at `τ`. Rewrite using `[ModularForm.slash_action_eq'_iff, hf γ hc τ, hd, one_mul, zpow_natCast]`.
-/
theorem slash_inv {k L N : ℕ} {ε : DirichletCharacter ℂ N} (hNL : N ∣ L) {f : ℍ → ℂ}
    (hf : Inv k L (ch ε) f) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 L) : f ∣[(k : ℤ)] γ = f := by
  obtain ⟨-, h11, h10⟩ := (Gamma1_mem L γ).1 hγ
  have hc : (L : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h10
  have hd1 : (L : ℤ) ∣ γ 1 1 - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h11, sub_self]
  have hd : ch ε (γ 1 1) = 1 := by
    have h2 : (N : ℤ) ∣ γ 1 1 - 1 := (Int.natCast_dvd_natCast.2 hNL).trans hd1
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
    push_cast at h2
    have h3 : ((γ 1 1 : ℤ) : ZMod N) = 1 := sub_eq_zero.1 h2
    simp [ch, h3]
  funext τ
  rw [ModularForm.slash_action_eq'_iff, hf γ hc τ, hd, one_mul, zpow_natCast]

/- English proof (translation)
Establish `hT : (ModularGroup.T ^ (L : ℤ)) • τ = (L : ℝ) +ᵥ τ`. Rewrite using `[modular_T_zpow_smul]`. Simplify using the standard rewrite rules. Establish `hδ : γ * ModularGroup.T ^ (L : ℤ) * γ⁻¹ ∈ Gamma1 L`. Establish `h1 : ModularGroup.T ^ (L : ℤ) ∈ CongruenceSubgroup.Gamma L`.

Simplify using `using ModularGroup_T_pow_mem_Gamma (L : ℤ) (L : ℤ) dvd_rfl`. Establish `h2` using `(Gamma_normal L).conj_mem _ h1 γ`. Rewrite `h2` using `[Gamma_mem]`. Rewrite using `[Gamma1_mem]`. Conclude with `⟨h2.1, h2.2.2.2, h2.2.2.1⟩`.

Establish `e : (f ∣[(k : ℤ)] γ) ∣[(k : ℤ)] (ModularGroup.T ^ (L : ℤ)) = f ∣[(k : ℤ)] γ`. Rewrite using `[← SlashAction.slash_mul, (inv_mul_cancel_right (γ * ModularGroup.T ^ (L : ℤ)) γ).symm, SlashAction.slash_mul, hinv _ hδ]`. Establish `h` using `congrFun e τ`. Establish `hden : denom (ModularGroup.T ^ (L : ℤ) : SL(2, ℤ)) τ = 1`. Rewrite using `[ModularGroup.denom_apply, ModularGroup.coe_T_zpow]`.

Simplify using the standard rewrite rules. Rewrite `h` using `[ModularForm.SL_slash_apply (f := f ∣[(k : ℤ)] γ), hT, hden, one_zpow, mul_one]`. Conclude with `h`.
-/
theorem periodic {k L : ℕ} {f : ℍ → ℂ} (hinv : ∀ γ ∈ Gamma1 L, f ∣[(k : ℤ)] γ = f)
    (γ : SL(2, ℤ)) (τ : ℍ) : (f ∣[(k : ℤ)] γ) ((L : ℝ) +ᵥ τ) = (f ∣[(k : ℤ)] γ) τ := by
  have hT : (ModularGroup.T ^ (L : ℤ)) • τ = (L : ℝ) +ᵥ τ := by
    rw [modular_T_zpow_smul]; simp
  have hδ : γ * ModularGroup.T ^ (L : ℤ) * γ⁻¹ ∈ Gamma1 L := by
    have h1 : ModularGroup.T ^ (L : ℤ) ∈ CongruenceSubgroup.Gamma L := by
      simpa using ModularGroup_T_pow_mem_Gamma (L : ℤ) (L : ℤ) dvd_rfl
    have h2 := (Gamma_normal L).conj_mem _ h1 γ
    rw [Gamma_mem] at h2
    rw [Gamma1_mem]
    exact ⟨h2.1, h2.2.2.2, h2.2.2.1⟩
  have e : (f ∣[(k : ℤ)] γ) ∣[(k : ℤ)] (ModularGroup.T ^ (L : ℤ)) = f ∣[(k : ℤ)] γ := by
    rw [← SlashAction.slash_mul,
      (inv_mul_cancel_right (γ * ModularGroup.T ^ (L : ℤ)) γ).symm,
      SlashAction.slash_mul, hinv _ hδ]
  have h := congrFun e τ
  have hden : denom (ModularGroup.T ^ (L : ℤ) : SL(2, ℤ)) τ = 1 := by
    rw [ModularGroup.denom_apply, ModularGroup.coe_T_zpow]; simp
  rw [ModularForm.SL_slash_apply (f := f ∣[(k : ℤ)] γ), hT, hden, one_zpow, mul_one] at h
  exact h

end GlobalTheory.EisM.OnGammaOne

namespace GlobalTheory.EisM.OnGammaOne

/- English proof (translation)
Use `set c : ℝ := ((γ 1 0 : ℤ) : ℝ)`. Use `set d : ℝ := ((γ 1 1 : ℤ) : ℝ)`. Use `⟨(|c| * L + |d|) ^ 2 + c ^ 2, by positivity, fun τ h1 h2 => ?_⟩` and prove the remaining obligations. Establish `hns : Complex.normSq (denom γ τ) = (c * τ.re + d) ^ 2 + (c * τ.im) ^ 2`. Rewrite using `[ModularGroup.denom_apply, Complex.normSq_apply]`.

Simplify using `[c, d]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hns]`. Establish `hy0 : 0 ≤ τ.im` using `τ.im_pos.le`. Establish `hy2 : 1 ≤ τ.im ^ 2` using `by nlinarith`.

Prove the components needed by the constructor for the conclusion. Distinguish the cases in `hc : γ 1 0 = 0`. Establish `hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1`. Use `γ.2` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`.

Conclude with `this`. Rewrite `hdet` using `[hc, mul_zero, sub_zero]`. Establish `hd : γ 1 1 = 1 ∨ γ 1 1 = -1`. Break down `Int.eq_one_or_neg_one_of_mul_eq_one' hdet with h | h` into its components or cases. Conclude with `Or.inl h.2`.

Conclude with `Or.inr h.2`. Establish `hc' : c = 0` using `by simp [c, hc]`. Apply the tactic sequence `have hd' : d ^ 2 = 1 := by rcases hd with h | h <;> simp [d, h]`. Rewrite using `[hc']`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hc1 : 1 ≤ c ^ 2`. Establish `: (1 : ℤ) ≤ (γ 1 0) ^ 2`. Use `Int.one_le_abs hc` as an intermediate fact. Use polynomial arithmetic with `[sq_abs (γ 1 0)]`. Establish `: ((1 : ℤ) : ℝ) ≤ (((γ 1 0) ^ 2 : ℤ) : ℝ)` using `by exact_mod_cast this`.

Simplify `this` using `[c]`. Use polynomial arithmetic with `[sq_nonneg (c * τ.re + d)]`. Establish `hM : |c * τ.re + d| ≤ |c| * L + |d|`. Combine the equalities or inequalities in the displayed calculation. Establish `hM2 : (c * τ.re + d) ^ 2 ≤ (|c| * L + |d|) ^ 2`.

Rewrite using `[← sq_abs]`. Conclude with `pow_le_pow_left₀ (abs_nonneg _) hM 2`. Establish `hM0 : 0 ≤ (|c| * L + |d|) ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem normSq_denom_bounds (L : ℕ) (γ : SL(2, ℤ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℍ, 1 ≤ τ.im → |τ.re| ≤ L →
      1 ≤ Complex.normSq (denom γ τ) ∧ Complex.normSq (denom γ τ) ≤ K * τ.im ^ 2 := by
  set c : ℝ := ((γ 1 0 : ℤ) : ℝ)
  set d : ℝ := ((γ 1 1 : ℤ) : ℝ)
  refine ⟨(|c| * L + |d|) ^ 2 + c ^ 2, by positivity, fun τ h1 h2 => ?_⟩
  have hns : Complex.normSq (denom γ τ) = (c * τ.re + d) ^ 2 + (c * τ.im) ^ 2 := by
    rw [ModularGroup.denom_apply, Complex.normSq_apply]
    simp [c, d]
    ring
  rw [hns]
  have hy0 : 0 ≤ τ.im := τ.im_pos.le
  have hy2 : 1 ≤ τ.im ^ 2 := by nlinarith
  constructor
  · by_cases hc : γ 1 0 = 0
    · have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
        have := γ.2; rw [Matrix.det_fin_two] at this; exact this
      rw [hc, mul_zero, sub_zero] at hdet
      have hd : γ 1 1 = 1 ∨ γ 1 1 = -1 := by
        rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with h | h
        · exact Or.inl h.2
        · exact Or.inr h.2
      have hc' : c = 0 := by simp [c, hc]
      have hd' : d ^ 2 = 1 := by rcases hd with h | h <;> simp [d, h]
      rw [hc']; nlinarith
    · have hc1 : 1 ≤ c ^ 2 := by
        have : (1 : ℤ) ≤ (γ 1 0) ^ 2 := by
          have := Int.one_le_abs hc
          nlinarith [sq_abs (γ 1 0)]
        have : ((1 : ℤ) : ℝ) ≤ (((γ 1 0) ^ 2 : ℤ) : ℝ) := by exact_mod_cast this
        simpa [c] using this
      nlinarith [sq_nonneg (c * τ.re + d)]
  · have hM : |c * τ.re + d| ≤ |c| * L + |d| := by
      calc |c * τ.re + d| ≤ |c * τ.re| + |d| := abs_add_le _ _
        _ = |c| * |τ.re| + |d| := by rw [abs_mul]
        _ ≤ |c| * L + |d| := by gcongr
    have hM2 : (c * τ.re + d) ^ 2 ≤ (|c| * L + |d|) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hM 2
    have hM0 : 0 ≤ (|c| * L + |d|) ^ 2 := by positivity
    nlinarith

/- English proof (translation)
Take `⟨C, A, hC⟩` from `hf`. Take `⟨K, hK0, hK⟩` from `normSq_denom_bounds L γ`. Use `⟨|C| * (1 + K ^ A), A, fun τ h1 h2 => ?_⟩` and prove the remaining obligations. Take `⟨hD1, hDK⟩` from `hK τ h1 h2`. Use `set D := Complex.normSq (denom γ τ) with hD`.

Use `set y := τ.im with hy`. Establish `hy0 : 0 < y` using `τ.im_pos`. Establish `hD0 : 0 < D` using `by linarith`. Establish `him : (γ • τ).im = y / D` using `ModularGroup.im_smul_eq_div_normSq γ τ`. Establish `hw1 : (γ • τ).im ^ A ≤ y ^ A`.

Rewrite using `[him]`. Conclude with `pow_le_pow_left₀ (by positivity) (div_le_self hy0.le hD1) A`. Establish `hw2 : ((γ • τ).im ^ A)⁻¹ ≤ K ^ A * y ^ A`. Rewrite using `[him, ← inv_pow, inv_div, ← mul_pow]`. Use `pow_le_pow_left₀ (by positivity) ?_ A` and prove the remaining obligations.

Rewrite using `[div_le_iff₀ hy0]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hden : ‖denom γ τ ^ (-(k : ℤ))‖ ≤ 1`. Establish `hn : 1 ≤ ‖denom γ τ‖`. Establish `: 1 ≤ ‖denom γ τ‖ ^ 2` using `by rw [← Complex.normSq_eq_norm_sq]; exact hD1`.

Use polynomial arithmetic with `[norm_nonneg (denom γ τ)]`. Rewrite using `[norm_zpow, zpow_neg, zpow_natCast]`. Conclude with `inv_le_one_of_one_le₀ (one_le_pow₀ hn)`. Rewrite using `[ModularForm.SL_slash_apply, norm_mul]`. Establish `hfw` using `hC (γ • τ)`.

Establish `hpos : 0 ≤ (γ • τ).im ^ A + ((γ • τ).im ^ A)⁻¹`. Use `(γ • τ).im_pos` as an intermediate fact. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_one]`.

Conclude with `hfw.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hpos)`. Use `_ ≤ |C| * (y ^ A + K ^ A * y ^ A) := by gcongr`. Use `_ = |C| * (1 + K ^ A) * y ^ A := by ring`.
-/
theorem growth {f : ℍ → ℂ} (hf : Mod f) (k L : ℕ) (γ : SL(2, ℤ)) :
    ∃ (C : ℝ) (A : ℕ), ∀ τ : ℍ, 1 ≤ τ.im → |τ.re| ≤ L → ‖(f ∣[(k : ℤ)] γ) τ‖ ≤ C * τ.im ^ A := by
  obtain ⟨C, A, hC⟩ := hf
  obtain ⟨K, hK0, hK⟩ := normSq_denom_bounds L γ
  refine ⟨|C| * (1 + K ^ A), A, fun τ h1 h2 => ?_⟩
  obtain ⟨hD1, hDK⟩ := hK τ h1 h2
  set D := Complex.normSq (denom γ τ) with hD
  set y := τ.im with hy
  have hy0 : 0 < y := τ.im_pos
  have hD0 : 0 < D := by linarith
  have him : (γ • τ).im = y / D := ModularGroup.im_smul_eq_div_normSq γ τ
  have hw1 : (γ • τ).im ^ A ≤ y ^ A := by
    rw [him]
    exact pow_le_pow_left₀ (by positivity) (div_le_self hy0.le hD1) A
  have hw2 : ((γ • τ).im ^ A)⁻¹ ≤ K ^ A * y ^ A := by
    rw [him, ← inv_pow, inv_div, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ A
    rw [div_le_iff₀ hy0]
    nlinarith
  have hden : ‖denom γ τ ^ (-(k : ℤ))‖ ≤ 1 := by
    have hn : 1 ≤ ‖denom γ τ‖ := by
      have : 1 ≤ ‖denom γ τ‖ ^ 2 := by rw [← Complex.normSq_eq_norm_sq]; exact hD1
      nlinarith [norm_nonneg (denom γ τ)]
    rw [norm_zpow, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hn)
  rw [ModularForm.SL_slash_apply, norm_mul]
  have hfw := hC (γ • τ)
  have hpos : 0 ≤ (γ • τ).im ^ A + ((γ • τ).im ^ A)⁻¹ := by
    have := (γ • τ).im_pos; positivity
  calc ‖f (γ • τ)‖ * ‖denom γ τ ^ (-(k : ℤ))‖ ≤ ‖f (γ • τ)‖ * 1 :=
        mul_le_mul_of_nonneg_left hden (norm_nonneg _)
    _ ≤ |C| * ((γ • τ).im ^ A + ((γ • τ).im ^ A)⁻¹) := by
        rw [mul_one]; exact hfw.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hpos)
    _ ≤ |C| * (y ^ A + K ^ A * y ^ A) := by gcongr
    _ = |C| * (1 + K ^ A) * y ^ A := by ring

end GlobalTheory.EisM.OnGammaOne

open GlobalTheory.EisM.OnGammaOne in

/- English proof (translation)
Introduce `k L N ε a hL hNL ha`. Use `haveI : NeZero L := ⟨hL.ne'⟩`. Establish `hinv : ∀ γ ∈ Gamma1 L, qs a ∣[(k : ℤ)] γ = qs a` using `fun γ hγ => slash_inv hNL ha.2 γ hγ`. Establish `hhol` using `GlobalTheory.T.mdifferentiable_qExpansion_of_coeffPolynomialGrowth a ha.1`. Use `⟨{ toFun := qs a, slash_action_eq' := ?_, holo' := hhol, bdd_at_cusps' := ?_ }, rfl⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨A, (hA : A ∈ Gamma1 L), rfl⟩`. Conclude with `hinv A hA`. Introduce `c hc`. Rewrite `hc` using `[Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]`. Rewrite using `[OnePoint.isBoundedAt_iff_forall_SL2Z hc]`.

Introduce `γ _`. Take `⟨C, A, hC⟩` from `growth (GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth a ha.1) k L γ`. Establish `hs : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qs a ∣[(k : ℤ)] γ)`. Rewrite using `[ModularForm.SL_slash]`. Conclude with `hhol.slash _ _`.

Conclude with `GlobalTheory.T.isBoundedAtImInfty_of_periodic_polynomial_bound _ L C A hL hs (periodic hinv γ) hC`.
-/
theorem GlobalTheory.EisM.modularForm_gammaOne_of_MF :
    ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 0 < L → N ∣ L → MF k L (ch ε) a →
      ∃ f : ModularForm (Gamma1 L) (k : ℤ), ⇑f = qs a := by
  intro k L N ε a hL hNL ha
  haveI : NeZero L := ⟨hL.ne'⟩
  have hinv : ∀ γ ∈ Gamma1 L, qs a ∣[(k : ℤ)] γ = qs a := fun γ hγ => slash_inv hNL ha.2 γ hγ
  have hhol := GlobalTheory.T.mdifferentiable_qExpansion_of_coeffPolynomialGrowth a ha.1
  refine ⟨{ toFun := qs a, slash_action_eq' := ?_, holo' := hhol, bdd_at_cusps' := ?_ }, rfl⟩
  · rintro _ ⟨A, (hA : A ∈ Gamma1 L), rfl⟩
    exact hinv A hA
  · intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    obtain ⟨C, A, hC⟩ := growth (GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth a ha.1) k L γ
    have hs : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qs a ∣[(k : ℤ)] γ) := by
      rw [ModularForm.SL_slash]; exact hhol.slash _ _
    exact GlobalTheory.T.isBoundedAtImInfty_of_periodic_polynomial_bound _ L C A hL hs (periodic hinv γ) hC
