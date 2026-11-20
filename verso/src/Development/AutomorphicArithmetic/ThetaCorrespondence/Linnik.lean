import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.PrimesInProgressionNonempty
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimesAPIntervalOfPrimesRel
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimesInProgressionsRelativeErrorStatement

namespace UpperTheory.Lit

/- English proof (translation)
Apply `ContinuousOn.intervalIntegrable` to reduce the goal to its premises. Establish `key : ∀ t ∈ Set.uIcc a b, 2 ≤ t` using `fun t ht => le_trans (le_inf ha hb) ht.1`. Apply `ContinuousOn.div continuousOn_const` to reduce the goal to its premises. Conclude with `Real.continuousOn_log.mono (fun t ht => Set.mem_compl_singleton_iff.mpr (by linarith [key t ht] : (0:ℝ) < t).ne')`. Introduce `t ht`.

Conclude with `(Real.log_pos (by linarith [key t ht])).ne'`.
-/
private theorem intervalIntegrable_inv_log_theta_correspondence (a b : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  have key : ∀ t ∈ Set.uIcc a b, 2 ≤ t := fun t ht => le_trans (le_inf ha hb) ht.1
  apply ContinuousOn.div continuousOn_const
  · exact Real.continuousOn_log.mono (fun t ht =>
      Set.mem_compl_singleton_iff.mpr (by linarith [key t ht] : (0:ℝ) < t).ne')
  · intro t ht
    exact (Real.log_pos (by linarith [key t ht])).ne'

/- English proof (translation)
Unfold `Formalism.HermitianLattices.GL2PrimeSums.Li`. Rewrite using `[intervalIntegral.integral_interval_sub_left (intervalIntegrable_inv_log_theta_correspondence 2 X le_rfl (by linarith)) (intervalIntegrable_inv_log_theta_correspondence 2 Y le_rfl hY)]`. Apply `intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_inv_log_theta_correspondence Y X hY (by linarith))` to reduce the goal to its premises. Introduce `t ht`. Conclude with `one_div_pos.mpr (Real.log_pos (by linarith [ht.1]))`.

Conclude with `h`.
-/
private theorem li_sub_li_pos_of_lt (Y X : ℝ) (hY : 2 ≤ Y) (h : Y < X) :
    0 < Formalism.HermitianLattices.GL2PrimeSums.Li X - Formalism.HermitianLattices.GL2PrimeSums.Li Y := by
  unfold Formalism.HermitianLattices.GL2PrimeSums.Li
  rw [intervalIntegral.integral_interval_sub_left (intervalIntegrable_inv_log_theta_correspondence 2 X le_rfl (by linarith))
    (intervalIntegrable_inv_log_theta_correspondence 2 Y le_rfl hY)]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_inv_log_theta_correspondence Y X hY (by linarith))
  · intro t ht
    exact one_div_pos.mpr (Real.log_pos (by linarith [ht.1]))
  · exact h

/- English proof (translation)
Unfold `Formalism.HermitianLattices.GL2PrimeSums.Li`. Conclude with `intervalIntegral.integral_nonneg hX (fun t ht => one_div_nonneg.mpr (Real.log_nonneg (by linarith [ht.1])))`.
-/
private theorem li_nonneg_of_two_le (X : ℝ) (hX : 2 ≤ X) : 0 ≤ Formalism.HermitianLattices.GL2PrimeSums.Li X := by
  unfold Formalism.HermitianLattices.GL2PrimeSums.Li
  exact intervalIntegral.integral_nonneg hX
    (fun t ht => one_div_nonneg.mpr (Real.log_nonneg (by linarith [ht.1])))

/- English proof (translation)
Establish `h` using `li_sub_li_pos_of_lt 2 X le_rfl hX`. Establish `h2 : Formalism.HermitianLattices.GL2PrimeSums.Li 2 = 0`. Unfold `Formalism.HermitianLattices.GL2PrimeSums.Li`. Conclude with `intervalIntegral.integral_same`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem li_pos_of_two_lt (X : ℝ) (hX : 2 < X) : 0 < Formalism.HermitianLattices.GL2PrimeSums.Li X := by
  have h := li_sub_li_pos_of_lt 2 X le_rfl hX
  have h2 : Formalism.HermitianLattices.GL2PrimeSums.Li 2 = 0 := by
    unfold Formalism.HermitianLattices.GL2PrimeSums.Li
    exact intervalIntegral.integral_same
  linarith

/- English proof (translation)
Introduce and unpack `⟨c₁, c₂, c₃, CA, cS, hc₁, hc₁', hc₂, hc₃, hCA, hcS, H⟩`. Use `set L : ℝ := |Real.log (4 * CA)| + 1 with hL`. Establish `hL1 : 1 ≤ L`. Use `abs_nonneg (Real.log (4 * CA))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Choose the witnesses or unpack the hypotheses as in `⟨A, hA1, hAc₂, hAL⟩ : ∃ A : ℝ, 1 ≤ A ∧ c₂ ≤ A ∧ L ^ 2 ≤ c₃ * A := by`. Use `⟨max (max 1 c₂) (L ^ 2 / c₃), le_trans (le_max_left _ _) (le_max_left _ _), le_trans (le_max_right _ _) (le_max_left _ _), ?_⟩` and prove the remaining obligations. Establish `: L ^ 2 / c₃ ≤ max (max 1 c₂) (L ^ 2 / c₃)` using `le_max_right _ _`. Rewrite `this` using `[div_le_iff₀ hc₃, mul_comm]`. Then use the resulting hypothesis. Use `⟨A, hA1, ?_⟩` and prove the remaining obligations.

Introduce `a M hM hcop`. Use `haveI : NeZero M := ⟨by omega⟩`. Take `⟨-, -, H3⟩` from `H M (by omega)`. Establish `hM3 : (3:ℝ) ≤ M` using `by exact_mod_cast (show 3 ≤ M by omega)`. Establish `hMpos : (0:ℝ) < M` using `by linarith`.

Establish `hlogM : 1 ≤ Real.log M`. Rewrite using `[← Real.log_exp 1]`. Conclude with `Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])`. Use `set X : ℝ := (M : ℝ) ^ A with hXdef`. Establish `hlogX : Real.log X = A * Real.log M`.

Rewrite using `[hXdef]`. Conclude with `Real.log_rpow hMpos A`. Establish `hX3 : 3 ≤ X`. Use `Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ M) hA1` as an intermediate fact. Rewrite `this` using `[Real.rpow_one]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hXc₂ : (M : ℝ) ^ c₂ ≤ X` using `Real.rpow_le_rpow_of_exponent_le (by linarith) hAc₂`. Establish `herr : CA * (Real.exp (-c₃ * Real.log X / Real.log M) + Real.exp (-√(c₃ * Real.log X))) < 1`. Rewrite using `[hlogX]`. Establish `hlM : Real.log (M : ℝ) ≠ 0` using `(by linarith : (0:ℝ) < Real.log M).ne'`.

Establish `e1 : -c₃ * (A * Real.log M) / Real.log M = -(c₃ * A)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1]`. Establish `hLL : L ≤ L ^ 2` using `by nlinarith`. Establish `i1 : Real.exp (-(c₃ * A)) ≤ Real.exp (-L)` using `Real.exp_le_exp.mpr (by linarith)`.

Establish `i2 : Real.exp (-√(c₃ * (A * Real.log M))) ≤ Real.exp (-L)`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `s1 : √(L ^ 2) ≤ √(c₃ * (A * Real.log M))` using `Real.sqrt_le_sqrt (by`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg hc₃.le (by linarith : (0:ℝ) ≤ A)) (by linarith : (0:ℝ) ≤ Real.log M - 1)])`. Rewrite `s1` using `[Real.sqrt_sq (by linarith)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hE : Real.exp (-L) * (4 * CA) < 1`. Rewrite using `[← Real.exp_log (by positivity : (0:ℝ) < 4 * CA), ← Real.exp_add, ← Real.exp_zero]`. Conclude with `Real.exp_lt_exp.mpr (by linarith [le_abs_self (Real.log (4 * CA))])`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left (add_le_add i1 i2) hCA.le]`.

Establish `key : ∃ (θ : ℤ) (β : ℝ), GlobalTheory.Lin.ExcData c₁ M a θ β ∧ 0 < Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X`. Distinguish the cases in `hex : ∃ (χ : DirichletCharacter ℂ M) (β : ℝ), GlobalTheory.Lin.IsExc c₁ χ β`. Take `⟨χ, β, hχ⟩` from `hex`. Establish `hunit : IsUnit (a : ZMod M)` using `(ZMod.isUnit_iff_coprime a M).mpr hcop`. Establish `h2 : χ (a : ZMod M) ^ 2 = 1`.

Rewrite using `[← MulChar.pow_apply' χ (by norm_num : (2:ℕ) ≠ 0), hχ.1, MulChar.one_apply hunit]`. Establish `hlpos : 0 < Real.log M` using `by linarith`. Establish `hβlog : Real.log M - c₁ < β * Real.log M`. Use `mul_lt_mul_of_pos_right hχ.2.1 hlpos` as an intermediate fact. Rewrite `this` using `[sub_mul, one_mul, div_mul_cancel₀ _ hlpos.ne']`. Then use the resulting hypothesis.

Establish `hXβ : 2 ≤ X ^ β`. Rewrite using `[Real.rpow_def_of_pos (by linarith), hlogX]`. Establish `hpos : 0 < β * Real.log M` using `by linarith`. Establish `: Real.log 2 ≤ A * Real.log M * β`. Establish `h7 : Real.log 2 < 7 / 8` using `by linarith [Real.log_two_lt_d9]`.

Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hA1) hpos.le]`. Combine the equalities or inequalities in the displayed calculation. Establish `hXβX : X ^ β < X`. Use `Real.rpow_lt_rpow_of_exponent_lt (by linarith : 1 < X) hχ.2.2.1` as an intermediate fact. Rewrite `this` using `[Real.rpow_one]`. Then use the resulting hypothesis.

Break down `mul_self_eq_one_iff.mp (show χ (a : ZMod M) * χ (a : ZMod M) = 1 by rw [← sq]; exact h2) with h | h` into its components or cases. Use `⟨1, β, Or.inr ⟨χ, hχ, by rw [h]; simp⟩, ?_⟩` and prove the remaining obligations. Unfold `Formalism.HermitianLattices.GL2PrimeSums.Emain`. Use `li_sub_li_pos_of_lt _ _ hXβ hXβX` as an intermediate fact. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨-1, β, Or.inr ⟨χ, hχ, by rw [h]; simp⟩, ?_⟩` and prove the remaining obligations. Unfold `Formalism.HermitianLattices.GL2PrimeSums.Emain`. Use `li_nonneg_of_two_le _ hXβ` as an intermediate fact. Use `li_pos_of_two_lt X (by linarith)` as an intermediate fact.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨0, 0, Or.inl ⟨rfl, fun χ β h => hex ⟨χ, β, h⟩⟩, ?_⟩` and prove the remaining obligations. Unfold `Formalism.HermitianLattices.GL2PrimeSums.Emain`. Simplify using `only [Int.cast_zero, zero_mul, sub_zero]`.

Conclude with `li_pos_of_two_lt X (by linarith)`. Take `⟨θ, β, hexc, hpos⟩` from `key`. Establish `hb` using `H3 a θ β hcop hexc X hXc₂`. Establish `hcard : 0 < ({p ∈ Finset.Icc 1 ⌊X⌋₊ | Nat.Prime p ∧ p ≡ a [MOD M]}).card`. Rewrite using `[Nat.pos_iff_ne_zero]`.

Introduce `h0`. Rewrite `hb` using `[h0]`. Simplify using `only [Nat.cast_zero, mul_zero, zero_sub, abs_neg] at hb`. Rewrite `hb` using `[abs_of_pos hpos]`. Combine the linear relations using `[mul_lt_of_lt_one_left hpos herr]`.

Take `⟨p, hp⟩` from `Finset.card_pos.mp hcard`. Rewrite `hp` using `[Finset.mem_filter, Finset.mem_Icc]`. Conclude with `⟨p, hp.2.1, hp.2.2, (Nat.le_floor_iff (by linarith)).mp hp.1.2⟩`.
-/
theorem exists_prime_modEq_le_rpow_of_primesRel : GlobalTheory.Lin.PrimesRel → ∃ A : ℝ, 1 ≤ A ∧ ∀ a M : ℕ, 2 < M → a.Coprime M →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD M] ∧ (p : ℝ) ≤ (M : ℝ) ^ A := by
  rintro ⟨c₁, c₂, c₃, CA, cS, hc₁, hc₁', hc₂, hc₃, hCA, hcS, H⟩
  set L : ℝ := |Real.log (4 * CA)| + 1 with hL
  have hL1 : 1 ≤ L := by
    have := abs_nonneg (Real.log (4 * CA))
    linarith
  obtain ⟨A, hA1, hAc₂, hAL⟩ : ∃ A : ℝ, 1 ≤ A ∧ c₂ ≤ A ∧ L ^ 2 ≤ c₃ * A := by
    refine ⟨max (max 1 c₂) (L ^ 2 / c₃), le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), ?_⟩
    have : L ^ 2 / c₃ ≤ max (max 1 c₂) (L ^ 2 / c₃) := le_max_right _ _
    rwa [div_le_iff₀ hc₃, mul_comm] at this
  refine ⟨A, hA1, ?_⟩
  intro a M hM hcop
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨-, -, H3⟩ := H M (by omega)
  have hM3 : (3:ℝ) ≤ M := by exact_mod_cast (show 3 ≤ M by omega)
  have hMpos : (0:ℝ) < M := by linarith
  have hlogM : 1 ≤ Real.log M := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  set X : ℝ := (M : ℝ) ^ A with hXdef
  have hlogX : Real.log X = A * Real.log M := by
    rw [hXdef]
    exact Real.log_rpow hMpos A
  have hX3 : 3 ≤ X := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ M) hA1
    rw [Real.rpow_one] at this
    linarith
  have hXc₂ : (M : ℝ) ^ c₂ ≤ X := Real.rpow_le_rpow_of_exponent_le (by linarith) hAc₂
  have herr : CA * (Real.exp (-c₃ * Real.log X / Real.log M) +
      Real.exp (-√(c₃ * Real.log X))) < 1 := by
    rw [hlogX]
    have hlM : Real.log (M : ℝ) ≠ 0 := (by linarith : (0:ℝ) < Real.log M).ne'
    have e1 : -c₃ * (A * Real.log M) / Real.log M = -(c₃ * A) := by
      field_simp
    rw [e1]
    have hLL : L ≤ L ^ 2 := by nlinarith
    have i1 : Real.exp (-(c₃ * A)) ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by linarith)
    have i2 : Real.exp (-√(c₃ * (A * Real.log M))) ≤ Real.exp (-L) := by
      apply Real.exp_le_exp.mpr
      have s1 : √(L ^ 2) ≤ √(c₃ * (A * Real.log M)) := Real.sqrt_le_sqrt (by
        nlinarith [mul_nonneg (mul_nonneg hc₃.le (by linarith : (0:ℝ) ≤ A))
          (by linarith : (0:ℝ) ≤ Real.log M - 1)])
      rw [Real.sqrt_sq (by linarith)] at s1
      linarith
    have hE : Real.exp (-L) * (4 * CA) < 1 := by
      rw [← Real.exp_log (by positivity : (0:ℝ) < 4 * CA), ← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith [le_abs_self (Real.log (4 * CA))])
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add i1 i2) hCA.le]
  have key : ∃ (θ : ℤ) (β : ℝ), GlobalTheory.Lin.ExcData c₁ M a θ β ∧
      0 < Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X := by
    by_cases hex : ∃ (χ : DirichletCharacter ℂ M) (β : ℝ), GlobalTheory.Lin.IsExc c₁ χ β
    · obtain ⟨χ, β, hχ⟩ := hex
      have hunit : IsUnit (a : ZMod M) := (ZMod.isUnit_iff_coprime a M).mpr hcop
      have h2 : χ (a : ZMod M) ^ 2 = 1 := by
        rw [← MulChar.pow_apply' χ (by norm_num : (2:ℕ) ≠ 0), hχ.1, MulChar.one_apply hunit]
      have hlpos : 0 < Real.log M := by linarith
      have hβlog : Real.log M - c₁ < β * Real.log M := by
        have := mul_lt_mul_of_pos_right hχ.2.1 hlpos
        rwa [sub_mul, one_mul, div_mul_cancel₀ _ hlpos.ne'] at this
      have hXβ : 2 ≤ X ^ β := by
        rw [Real.rpow_def_of_pos (by linarith), hlogX]
        have hpos : 0 < β * Real.log M := by linarith
        have : Real.log 2 ≤ A * Real.log M * β := by
          have h7 : Real.log 2 < 7 / 8 := by linarith [Real.log_two_lt_d9]
          nlinarith [mul_nonneg (sub_nonneg.mpr hA1) hpos.le]
        calc (2:ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
          _ ≤ _ := Real.exp_le_exp.mpr this
      have hXβX : X ^ β < X := by
        have := Real.rpow_lt_rpow_of_exponent_lt (by linarith : 1 < X) hχ.2.2.1
        rwa [Real.rpow_one] at this
      rcases mul_self_eq_one_iff.mp
          (show χ (a : ZMod M) * χ (a : ZMod M) = 1 by rw [← sq]; exact h2) with h | h
      · refine ⟨1, β, Or.inr ⟨χ, hχ, by rw [h]; simp⟩, ?_⟩
        unfold Formalism.HermitianLattices.GL2PrimeSums.Emain
        have := li_sub_li_pos_of_lt _ _ hXβ hXβX
        push_cast
        linarith
      · refine ⟨-1, β, Or.inr ⟨χ, hχ, by rw [h]; simp⟩, ?_⟩
        unfold Formalism.HermitianLattices.GL2PrimeSums.Emain
        have := li_nonneg_of_two_le _ hXβ
        have := li_pos_of_two_lt X (by linarith)
        push_cast
        linarith
    · refine ⟨0, 0, Or.inl ⟨rfl, fun χ β h => hex ⟨χ, β, h⟩⟩, ?_⟩
      unfold Formalism.HermitianLattices.GL2PrimeSums.Emain
      simp only [Int.cast_zero, zero_mul, sub_zero]
      exact li_pos_of_two_lt X (by linarith)
  obtain ⟨θ, β, hexc, hpos⟩ := key
  have hb := H3 a θ β hcop hexc X hXc₂
  have hcard : 0 < ({p ∈ Finset.Icc 1 ⌊X⌋₊ | Nat.Prime p ∧ p ≡ a [MOD M]}).card := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    rw [h0] at hb
    simp only [Nat.cast_zero, mul_zero, zero_sub, abs_neg] at hb
    rw [abs_of_pos hpos] at hb
    linarith [mul_lt_of_lt_one_left hpos herr]
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  exact ⟨p, hp.2.1, hp.2.2, (Nat.le_floor_iff (by linarith)).mp hp.1.2⟩

/- English proof (translation)
Take `⟨A, hA, h⟩` from `exists_prime_modEq_le_rpow_of_primesRel GlobalTheory.T.primesInProgressions_relativeError`. Use `GlobalTheory.Published.linnik_iff_exists_prime.2 ⟨3, A, by norm_num, by linarith, fun a q _ hq hc => ?_⟩` and prove the remaining obligations. Establish `hq1 : (1 : ℝ) ≤ (q : ℝ) ^ A` using `Real.one_le_rpow (by exact_mod_cast hq) (by linarith)`. Distinguish the cases in `h2 : 2 < q`. Take `⟨p, h1, h3, h4⟩` from `h a q h2 hc`.

Conclude with `⟨p, h1, h3, by linarith⟩`. Use `⟨3, Nat.prime_three, ?_, by push_cast; linarith⟩` and prove the remaining obligations. Establish `: q = 1 ∨ q = 2` using `by omega`. Break down `this with rfl | rfl` into its components or cases. Conclude with `Nat.modEq_one`.

Establish `: a % 2 = 1` using `Nat.odd_iff.1 (Nat.coprime_two_right.1 hc)`. Unfold `Nat.ModEq`. Use linear arithmetic over natural numbers and integers.
-/
theorem linnik : GlobalTheory.Published.Linnik := by
  obtain ⟨A, hA, h⟩ := exists_prime_modEq_le_rpow_of_primesRel GlobalTheory.T.primesInProgressions_relativeError
  refine GlobalTheory.Published.linnik_iff_exists_prime.2 ⟨3, A, by norm_num, by linarith, fun a q _ hq hc => ?_⟩
  have hq1 : (1 : ℝ) ≤ (q : ℝ) ^ A := Real.one_le_rpow (by exact_mod_cast hq) (by linarith)
  by_cases h2 : 2 < q
  · obtain ⟨p, h1, h3, h4⟩ := h a q h2 hc
    exact ⟨p, h1, h3, by linarith⟩
  · refine ⟨3, Nat.prime_three, ?_, by push_cast; linarith⟩
    have : q = 1 ∨ q = 2 := by omega
    rcases this with rfl | rfl
    · exact Nat.modEq_one
    · have : a % 2 = 1 := Nat.odd_iff.1 (Nat.coprime_two_right.1 hc)
      unfold Nat.ModEq; omega

end UpperTheory.Lit
