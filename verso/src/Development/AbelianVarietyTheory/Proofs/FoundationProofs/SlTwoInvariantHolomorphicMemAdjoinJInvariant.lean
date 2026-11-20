import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Definitions.Foundations.SiegelNeZeroIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExponentsIntegralOfTranslationInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerFunctionSlTwoIntInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerFunctionTendstoConstTermExponentialStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstOfSlTwoIntInvariantBoundedUpperHalfPlaneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesPowOfLeadingQInvStatement

noncomputable section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.LevelOne

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Use `set a0 := (X.exp h).coeff 0 with ha0`. Establish `hsupp : ∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ n : ℕ, r = n`. Introduce `r hr`. Take `⟨m, rfl⟩` from `GlobalTheory.T.exponents_integral_of_translation_invariant X h (hinv _) r hr`. Establish `hm : 0 ≤ m`.

Assume the negation of the conclusion as `hm`. Conclude with `hr (hneg _ (by exact_mod_cast (not_le.1 hm)))`. Conclude with `⟨m.toNat, by rw [← Int.cast_natCast, Int.toNat_of_nonneg hm]⟩`. Take `⟨B, t, hB⟩` from `GlobalTheory.T.modularTower_function_tendsto_constTerm_exponential X h φ hd.continuousOn ha hsupp`. Establish `hinvφ` using `GlobalTheory.T.modularTower_function_slTwoInt_invariant X h φ hd.continuousOn ha hinv`.

Establish `hexp1 : ∀ z : ℂ, t < z.im → Real.exp (-(2 * Real.pi * (z.im - t))) ≤ 1`. Introduce `z hz`. Rewrite using `[Real.exp_le_one_iff]`. Establish `: 0 < z.im - t` using `by linarith`. Use `Real.pi_pos` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Take `⟨c, hc⟩` from `GlobalTheory.T.const_of_slTwoInt_invariant_bounded_upperHalfPlane φ hd hinvφ ⟨‖ε a0‖ + |B|, t, fun z hz hzt => by`. Establish `h1` using `hB z hz hzt`. Establish `h2` using `hexp1 z hzt`. Establish `h3 : B * Real.exp (-(2 * Real.pi * (z.im - t))) ≤ |B|`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Establish `hca : c = ε a0`. Establish `hle : ∀ s : ℝ, max t 0 < s → ‖c - ε a0‖ ≤ B * Real.exp (-(2 * Real.pi * (s - t)))`. Introduce `s hs`.

Establish `hs0 : 0 < s` using `lt_of_le_of_lt (le_max_right _ _) hs`. Establish `hst : t < s` using `lt_of_le_of_lt (le_max_left _ _) hs`. Establish `hz : ((s : ℂ) * Complex.I) ∈ Hs` using `by simp [Hs, hs0]`. Use `hB _ hz (by simpa using hst)` as an intermediate fact. Rewrite `this` using `[hc _ hz]`.

Simplify using `using this`. Establish `ht : Filter.Tendsto (fun s : ℝ => B * Real.exp (-(2 * Real.pi * (s - t)))) Filter.atTop (nhds 0)`. Establish `h1 : Filter.Tendsto (fun s : ℝ => 2 * Real.pi * (s - t)) Filter.atTop Filter.atTop`. Apply `Filter.Tendsto.const_mul_atTop Real.two_pi_pos` to reduce the goal to its premises. Conclude with `Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id`.

Establish `h2` using `(Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul B`. Simplify using `using h2`. Establish `h0 : ‖c - ε a0‖ ≤ 0` using `ge_of_tendsto ht (Filter.eventually_gt_atTop (max t 0) |>.mono hle)`. Use `norm_le_zero_iff.1 h0` as an intermediate fact. Conclude with `sub_eq_zero.1 this`.

Apply `SiegelModel.an_injective X` to reduce the goal to its premises. Rewrite using `[ha, X.an_c]`. Conclude with `SiegelModel.germ_eq_of_eqOn fun z hz => by rw [hc z hz, hca]`.
-/
theorem eq_const_of_nonneg [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (h : X.K) (hinv : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h)
    (φ : ℂ → ℂ) (hd : DifferentiableOn ℂ φ Hs) (ha : X.an h = (φ : Mero))
    (hneg : ∀ r : ℚ, r < 0 → (X.exp h).coeff r = 0) :
    h = algebraMap Ω X.K ((X.exp h).coeff 0) := by
  set a0 := (X.exp h).coeff 0 with ha0
  have hsupp : ∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ n : ℕ, r = n := by
    intro r hr
    obtain ⟨m, rfl⟩ := GlobalTheory.T.exponents_integral_of_translation_invariant X h (hinv _) r hr
    have hm : 0 ≤ m := by
      by_contra hm
      exact hr (hneg _ (by exact_mod_cast (not_le.1 hm)))
    exact ⟨m.toNat, by rw [← Int.cast_natCast, Int.toNat_of_nonneg hm]⟩
  obtain ⟨B, t, hB⟩ := GlobalTheory.T.modularTower_function_tendsto_constTerm_exponential X h φ hd.continuousOn ha hsupp
  have hinvφ := GlobalTheory.T.modularTower_function_slTwoInt_invariant X h φ hd.continuousOn ha hinv
  have hexp1 : ∀ z : ℂ, t < z.im → Real.exp (-(2 * Real.pi * (z.im - t))) ≤ 1 := by
    intro z hz
    rw [Real.exp_le_one_iff]
    have : 0 < z.im - t := by linarith
    have := Real.pi_pos
    nlinarith
  obtain ⟨c, hc⟩ := GlobalTheory.T.const_of_slTwoInt_invariant_bounded_upperHalfPlane φ hd hinvφ ⟨‖ε a0‖ + |B|, t, fun z hz hzt => by
    have h1 := hB z hz hzt
    have h2 := hexp1 z hzt
    have h3 : B * Real.exp (-(2 * Real.pi * (z.im - t))) ≤ |B| := by
      calc B * Real.exp (-(2 * Real.pi * (z.im - t))) ≤ |B| * Real.exp (-(2 * Real.pi * (z.im - t))) :=
            mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_pos _).le
        _ ≤ |B| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg B)
        _ = |B| := mul_one _
    calc ‖φ z‖ = ‖(φ z - ε a0) + ε a0‖ := by ring_nf
      _ ≤ ‖φ z - ε a0‖ + ‖ε a0‖ := norm_add_le _ _
      _ ≤ ‖ε a0‖ + |B| := by linarith⟩
  have hca : c = ε a0 := by
    have hle : ∀ s : ℝ, max t 0 < s → ‖c - ε a0‖ ≤ B * Real.exp (-(2 * Real.pi * (s - t))) := by
      intro s hs
      have hs0 : 0 < s := lt_of_le_of_lt (le_max_right _ _) hs
      have hst : t < s := lt_of_le_of_lt (le_max_left _ _) hs
      have hz : ((s : ℂ) * Complex.I) ∈ Hs := by simp [Hs, hs0]
      have := hB _ hz (by simpa using hst)
      rw [hc _ hz] at this
      simpa using this
    have ht : Filter.Tendsto (fun s : ℝ => B * Real.exp (-(2 * Real.pi * (s - t)))) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun s : ℝ => 2 * Real.pi * (s - t)) Filter.atTop Filter.atTop := by
        apply Filter.Tendsto.const_mul_atTop Real.two_pi_pos
        exact Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id
      have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul B
      simpa using h2
    have h0 : ‖c - ε a0‖ ≤ 0 := ge_of_tendsto ht (Filter.eventually_gt_atTop (max t 0) |>.mono hle)
    have := norm_le_zero_iff.1 h0
    exact sub_eq_zero.1 this
  apply SiegelModel.an_injective X
  rw [ha, X.an_c]
  exact SiegelModel.germ_eq_of_eqOn fun z hz => by rw [hc z hz, hca]

/- English proof (translation)
Introduce `Ω _ _ _ ε X _ hj`. Take `⟨ψ, hψ, hψa⟩` from `hj`. Establish `key : ∀ n : ℕ, ∀ h : X.K, (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)) → (∀ r : ℚ, r < -(n : ℚ) → (X.exp h).coeff r = 0) → h ∈ Algebra.adjoin Ω {X.jK}`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Introduce `h hinv hol hneg`. Take `⟨φ, hd, ha⟩` from `hol`. Rewrite using `[eq_const_of_nonneg X h hinv φ hd ha (by simpa using hneg)]`. Conclude with `Subalgebra.algebraMap_mem _ _`.

Consider the case `succ n ih`. Introduce `h hinv hol hneg`. Take `⟨φ, hd, ha⟩` from `hol`. Take `⟨c, hcdef⟩ : ∃ c : Ω, c = (X.exp h).coeff (-((n + 1 : ℕ) : ℚ))` from `⟨_, rfl⟩`. Take `⟨h', hh'⟩ : ∃ h' : X.K, h' = h - algebraMap Ω X.K c * X.jK ^ (n + 1)` from `⟨_, rfl⟩`.

Establish `hj` using `GlobalTheory.T.hahnSeries_pow_of_leading_qInv (X.exp X.jK) X.j_exp.1 X.j_exp.2.1 (n + 1)`. Establish `hinv' : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) h' = h'`. Introduce `γ`. Rewrite using `[hh', map_sub, map_mul, map_pow, X.j_inv, hinv, AlgEquiv.commutes]`. Establish `hol' : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h' = (φ : Mero)`.

Use `⟨fun z => φ z - ε c * ψ z ^ (n + 1), ?_, ?_⟩` and prove the remaining obligations. Conclude with `hd.sub ((hψ.pow _).const_mul _)`. Rewrite using `[hh', map_sub, map_mul, map_pow, X.an_c, ha, hψa]`. Both sides reduce to the same expression. Establish `hneg' : ∀ r : ℚ, r < -(n : ℚ) → (X.exp h').coeff r = 0`.

Introduce `r hr`. Assume the negation of the conclusion as `hrz`. Take `⟨m, rfl⟩` from `GlobalTheory.T.exponents_integral_of_translation_invariant X h' (hinv' _) r hrz`. Apply `hrz` to reduce the goal to its premises. Establish `hcoe : (X.exp h').coeff (m : ℚ) = (X.exp h).coeff m - c * ((X.exp X.jK) ^ (n + 1)).coeff m`.

Rewrite using `[hh', map_sub, map_mul, AlgHom.commutes, map_pow, HahnSeries.coeff_sub, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]`. Rewrite using `[hcoe]`. Establish `hm : m ≤ -((n : ℤ) + 1)`. Establish `: (m : ℚ) < -(n : ℚ)` using `hr`. Establish `: m < -(n : ℤ)` using `by exact_mod_cast this`.

Use linear arithmetic over natural numbers and integers. Break down `hm.lt_or_eq with hlt | heq` into its components or cases. Establish `hq : (m : ℚ) < -((n + 1 : ℕ) : ℚ)` using `by push_cast; exact_mod_cast hlt`. Rewrite using `[hneg _ hq, hj.2 _ hq]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hq : (m : ℚ) = -((n + 1 : ℕ) : ℚ)` using `by rw [heq]; push_cast; ring`. Rewrite using `[hq, hj.1, hcdef]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem` using `ih h' hinv' hol' hneg'`. Establish `hsum : h = h' + algebraMap Ω X.K c * X.jK ^ (n + 1)` using `by rw [hh']; abel`.

Establish `hjm : X.jK ∈ Algebra.adjoin Ω {X.jK}` using `Algebra.self_mem_adjoin_singleton Ω X.jK`. Rewrite using `[hsum]`. Conclude with `add_mem hmem (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem hjm _))`. Introduce `h hinv hol`. Use `key ⌈-(X.exp h).order⌉₊ h hinv hol fun r hr => HahnSeries.coeff_eq_zero_of_lt_order ?_` and prove the remaining obligations.

Use `Nat.le_ceil (-(X.exp h).order)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mem_adjoin_j : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ h : X.K,
    (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)) →
    h ∈ Algebra.adjoin Ω {X.jK} := by
  intro Ω _ _ _ ε X _ hj
  obtain ⟨ψ, hψ, hψa⟩ := hj
  have key : ∀ n : ℕ, ∀ h : X.K, (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) →
      (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)) →
      (∀ r : ℚ, r < -(n : ℚ) → (X.exp h).coeff r = 0) → h ∈ Algebra.adjoin Ω {X.jK} := by
    intro n
    induction n with
    | zero =>
      intro h hinv hol hneg
      obtain ⟨φ, hd, ha⟩ := hol
      rw [eq_const_of_nonneg X h hinv φ hd ha (by simpa using hneg)]
      exact Subalgebra.algebraMap_mem _ _
    | succ n ih =>
      intro h hinv hol hneg
      obtain ⟨φ, hd, ha⟩ := hol
      obtain ⟨c, hcdef⟩ : ∃ c : Ω, c = (X.exp h).coeff (-((n + 1 : ℕ) : ℚ)) := ⟨_, rfl⟩
      obtain ⟨h', hh'⟩ : ∃ h' : X.K, h' = h - algebraMap Ω X.K c * X.jK ^ (n + 1) := ⟨_, rfl⟩
      have hj := GlobalTheory.T.hahnSeries_pow_of_leading_qInv (X.exp X.jK) X.j_exp.1 X.j_exp.2.1 (n + 1)
      have hinv' : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) h' = h' := by
        intro γ
        rw [hh', map_sub, map_mul, map_pow, X.j_inv, hinv, AlgEquiv.commutes]
      have hol' : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h' = (φ : Mero) := by
        refine ⟨fun z => φ z - ε c * ψ z ^ (n + 1), ?_, ?_⟩
        · exact hd.sub ((hψ.pow _).const_mul _)
        · rw [hh', map_sub, map_mul, map_pow, X.an_c, ha, hψa]
          rfl
      have hneg' : ∀ r : ℚ, r < -(n : ℚ) → (X.exp h').coeff r = 0 := by
        intro r hr
        by_contra hrz
        obtain ⟨m, rfl⟩ := GlobalTheory.T.exponents_integral_of_translation_invariant X h' (hinv' _) r hrz
        apply hrz
        have hcoe : (X.exp h').coeff (m : ℚ) =
            (X.exp h).coeff m - c * ((X.exp X.jK) ^ (n + 1)).coeff m := by
          rw [hh', map_sub, map_mul, AlgHom.commutes, map_pow, HahnSeries.coeff_sub, HahnSeries.algebraMap_apply',
            PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C,
            HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
        rw [hcoe]
        have hm : m ≤ -((n : ℤ) + 1) := by
          have : (m : ℚ) < -(n : ℚ) := hr
          have : m < -(n : ℤ) := by exact_mod_cast this
          omega
        rcases hm.lt_or_eq with hlt | heq
        · have hq : (m : ℚ) < -((n + 1 : ℕ) : ℚ) := by push_cast; exact_mod_cast hlt
          rw [hneg _ hq, hj.2 _ hq]
          ring
        · have hq : (m : ℚ) = -((n + 1 : ℕ) : ℚ) := by rw [heq]; push_cast; ring
          rw [hq, hj.1, hcdef]
          ring
      have hmem := ih h' hinv' hol' hneg'
      have hsum : h = h' + algebraMap Ω X.K c * X.jK ^ (n + 1) := by rw [hh']; abel
      have hjm : X.jK ∈ Algebra.adjoin Ω {X.jK} := Algebra.self_mem_adjoin_singleton Ω X.jK
      rw [hsum]
      exact add_mem hmem (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem hjm _))
  intro h hinv hol
  refine key ⌈-(X.exp h).order⌉₊ h hinv hol fun r hr => HahnSeries.coeff_eq_zero_of_lt_order ?_
  have := Nat.le_ceil (-(X.exp h).order)
  linarith

end GlobalTheory.KZ.LevelOne
