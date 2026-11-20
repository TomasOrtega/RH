import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinWronskianNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JInvariantEqualSl2OrbitStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EllipticPointsStabilizerStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.LevelOneLocal

/- English proof (translation)
Establish `h0 : valueAtInfty (ModularForm.E hk : ℍ → ℂ) = 1`. Rewrite using `[← qExpansion_coeff_zero one_pos (ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.E hk) one_pos one_mem_strictPeriods_SL) (SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E hk) one_mem_strictPeriods_SL)]`. Conclude with `EisensteinSeries.E_qExpansion_coeff_zero hk hk2`. Take `⟨c, hc, h⟩` from `ModularFormClass.exp_decay_sub_atImInfty' (ModularForm.E hk)`. Rewrite `h` using `[h0]`.

Establish `h2 : Tendsto (fun τ : ℍ ↦ Real.exp (-c * τ.im)) atImInfty (𝓝 0)`. Use `Real.tendsto_exp_atBot.comp ?_` and prove the remaining obligations. Conclude with `Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_comap`. Simplify using `using (h.trans_tendsto h2).add_const 1`.
-/
theorem tendsto_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    Tendsto (ModularForm.E hk : ℍ → ℂ) atImInfty (𝓝 1) := by
  have h0 : valueAtInfty (ModularForm.E hk : ℍ → ℂ) = 1 := by
    rw [← qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.E hk) one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E hk) one_mem_strictPeriods_SL)]
    exact EisensteinSeries.E_qExpansion_coeff_zero hk hk2
  obtain ⟨c, hc, h⟩ := ModularFormClass.exp_decay_sub_atImInfty' (ModularForm.E hk)
  rw [h0] at h
  have h2 : Tendsto (fun τ : ℍ ↦ Real.exp (-c * τ.im)) atImInfty (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    exact Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_comap
  simpa using (h.trans_tendsto h2).add_const 1

/- English proof (translation)
The claim follows from `tendsto_E _ ⟨2, rfl⟩`.
-/
theorem tendsto_E₄ : Tendsto (E₄ : ℍ → ℂ) atImInfty (𝓝 1) := tendsto_E _ ⟨2, rfl⟩

/- English proof (translation)
The claim follows from `tendsto_E _ ⟨3, rfl⟩`.
-/
theorem tendsto_E₆ : Tendsto (E₆ : ℍ → ℂ) atImInfty (𝓝 1) := tendsto_E _ ⟨3, rfl⟩

/- English proof (translation)
Introduce `h`. Apply `ModularForm.discriminant_ne_zero τ` to reduce the goal to its premises. Rewrite using `[ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, h, zero_div]`.
-/
theorem cube_sub_sq_ne_zero (τ : ℍ) : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := by
  intro h
  apply ModularForm.discriminant_ne_zero τ
  rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, h, zero_div]

/- English proof (translation)
The claim follows from `isMF_coe_top E₄`.
-/
theorem isMF_E₄ : IsMF ⊤ 4 (E₄ : ℍ → ℂ) := isMF_coe_top E₄

/- English proof (translation)
The claim follows from `isMF_coe_top E₆`.
-/
theorem isMF_E₆ : IsMF ⊤ 6 (E₆ : ℍ → ℂ) := isMF_coe_top E₆

/- English proof (translation)
The claim follows from `mdifferentiableAt_iff.mp (hf τ)`.
-/
theorem differentiableAt_comp {f : ℍ → ℂ} (hf : MDiff f) (τ : ℍ) :
    DifferentiableAt ℂ (f ∘ ofComplex) τ :=
  mdifferentiableAt_iff.mp (hf τ)

/- English proof (translation)
Establish `h4` using `(differentiableAt_comp isMF_E₄.2.1 τ).hasDerivAt`. Establish `h6` using `(differentiableAt_comp isMF_E₆.2.1 τ).hasDerivAt`. Establish `h` using `((h4.fun_pow 3).const_mul α).fun_sub ((h6.fun_pow 2).const_mul β)`. Establish `e : (α • (E₄ : ℍ → ℂ) ^ 3 - β • (E₆ : ℍ → ℂ) ^ 2) ∘ ofComplex = fun x => α * (⇑E₄ ∘ ofComplex) x ^ 3 - β * (⇑E₆ ∘ ofComplex) x ^ 2`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Rewrite using `[e, h.deriv]`. Simplify using the standard rewrite rules.
-/
theorem deriv_comb (α β : ℂ) (τ : ℍ) :
    deriv ((α • (E₄ : ℍ → ℂ) ^ 3 - β • (E₆ : ℍ → ℂ) ^ 2) ∘ ofComplex) τ =
      α * (3 * E₄ τ ^ 2 * deriv (⇑E₄ ∘ ofComplex) τ) - β * (2 * E₆ τ * deriv (⇑E₆ ∘ ofComplex) τ) := by
  have h4 := (differentiableAt_comp isMF_E₄.2.1 τ).hasDerivAt
  have h6 := (differentiableAt_comp isMF_E₆.2.1 τ).hasDerivAt
  have h := ((h4.fun_pow 3).const_mul α).fun_sub ((h6.fun_pow 2).const_mul β)
  have e : (α • (E₄ : ℍ → ℂ) ^ 3 - β • (E₆ : ℍ → ℂ) ^ 2) ∘ ofComplex =
      fun x => α * (⇑E₄ ∘ ofComplex) x ^ 3 - β * (⇑E₆ ∘ ofComplex) x ^ 2 := by
    ext x; simp
  rw [e, h.deriv]
  simp

/- English proof (translation)
Introduce `τ₀`. Establish `hD` using `cube_sub_sq_ne_zero τ₀`. Distinguish the cases in `h6 : E₆ τ₀ = 0`. Take `⟨u, hu, hp⟩` from `(GlobalTheory.T.elliptic_points_stabilizer τ₀).1 h6`. Establish `h4 : E₄ τ₀ ≠ 0` using `fun h => hD (by simp [h, h6])`.

Use `⟨4, 0, 6, E₆, u, hu, by norm_num, hp, by norm_num, by decide, isMF_E₆, fun τ hτ => ⟨?_, ?_⟩, ⟨1, one_ne_zero, tendsto_E₆⟩, ?_⟩` and prove the remaining obligations. Introduce `h`. Conclude with `GlobalTheory.T.eisenstein_wronskian_ne_zero τ (by simp [h, hτ])`. Conclude with `GlobalTheory.T.j_invariant_equal_sl2_orbit τ τ₀ (by simp [h6, hτ])`. Introduce and unpack `d hd ⟨m, rfl⟩`.

Take `⟨m, rfl⟩` from `Int.eq_ofNat_of_zero_le (show 0 ≤ m by push_cast at hd; omega)`. Use `⟨(E₄ : ℍ → ℂ) ^ m, ?_, by simpa using fun h => absurd h h4⟩` and prove the remaining obligations. Use `isMF_E₄.pow m` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `h4 : E₄ τ₀ = 0`. Take `⟨u, hu, hp⟩` from `(GlobalTheory.T.elliptic_points_stabilizer τ₀).2 h4`. Use `⟨6, 0, 4, E₄, u, hu, by norm_num, hp, by norm_num, by decide, isMF_E₄, fun τ hτ => ⟨?_, ?_⟩, ⟨1, one_ne_zero, tendsto_E₄⟩, ?_⟩` and prove the remaining obligations. Introduce `h`.

Conclude with `GlobalTheory.T.eisenstein_wronskian_ne_zero τ (by simp [h, hτ])`. Conclude with `GlobalTheory.T.j_invariant_equal_sl2_orbit τ τ₀ (by simp [h4, hτ])`. Introduce and unpack `d hd ⟨m, rfl⟩`. Take `⟨m, rfl⟩` from `Int.eq_ofNat_of_zero_le (show 0 ≤ m by push_cast at hd; omega)`. Use `⟨(E₆ : ℍ → ℂ) ^ m, ?_, by simpa using fun h => absurd h h6⟩` and prove the remaining obligations.

Use `isMF_E₆.pow m` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨2, 4, 12, (E₆ τ₀ ^ 2) • (E₄ : ℍ → ℂ) ^ 3 - (E₄ τ₀ ^ 3) • (E₆ : ℍ → ℂ) ^ 2, -1, ?_, by norm_num, ?_, by norm_num, by decide, ?_, fun τ hτ => ?_, ⟨E₆ τ₀ ^ 2 - E₄ τ₀ ^ 3, fun h => hD (by linear_combination -h), ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[ModularGroup.SL_neg_smul, one_smul]`. Establish `: denom ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ₀ = -1` using `by simp [denom]`. Rewrite using `[this]`. Conclude with `IsPrimitiveRoot.neg_one 0 (by norm_num)`. Conclude with `((isMF_E₄.pow 3).smul _).sub ((isMF_E₆.pow 2).smul _)`.

Establish `hz : E₆ τ₀ ^ 2 * E₄ τ ^ 3 - E₄ τ₀ ^ 3 * E₆ τ ^ 2 = 0` using `by simpa using hτ`. Use `⟨?_, GlobalTheory.T.j_invariant_equal_sl2_orbit τ τ₀ (by linear_combination hz)⟩` and prove the remaining obligations. Establish `hDτ` using `cube_sub_sq_ne_zero τ`. Establish `k4 : E₄ τ ≠ 0`. Introduce `h`.

Establish `: E₆ τ = 0` using `by simpa [h, h4] using hz`. Conclude with `hDτ (by simp [h, this])`. Rewrite using `[deriv_comb]`. Introduce `h`. Establish `hW` using `GlobalTheory.T.eisenstein_wronskian_ne_zero τ`.

Apply `mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h6) (pow_ne_zero 3 k4)) hW` to reduce the goal to its premises. Take the linear combination `(2 * E₄ τ * deriv (⇑E₆ ∘ ofComplex) τ) * hz - (E₄ τ * E₆ τ) * h`. Use `((tendsto_E₄.pow 3).const_mul (E₆ τ₀ ^ 2)).sub ((tendsto_E₆.pow 2).const_mul (E₄ τ₀ ^ 3))` as an intermediate fact. Simplify using `only [one_pow, mul_one] at this`. Conclude with `this`.

Introduce and unpack `d hd ⟨m, rfl⟩`. Take `⟨m, rfl⟩` from `Int.eq_ofNat_of_zero_le (show 0 ≤ m by push_cast at hd; omega)`. Break down `Nat.even_or_odd' m with ⟨p, rfl | rfl⟩` into its components or cases. Use `⟨(E₄ : ℍ → ℂ) ^ (p + 1), ?_, by simpa using h4⟩` and prove the remaining obligations. Use `isMF_E₄.pow (p + 1)` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨(E₄ : ℍ → ℂ) ^ p * E₆, (isMF_E₄.pow p).mul isMF_E₆ (by push_cast; ring), ?_⟩` and prove the remaining obligations. Conclude with `mul_ne_zero (pow_ne_zero p h4) h6`.
-/
theorem exists_local_data : ∀ τ₀ : ℍ, ∃ (n : ℕ) (a b : ℤ) (E : ℍ → ℂ) (u : SL(2, ℤ)), u • τ₀ = τ₀ ∧ 0 < n ∧ IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) n ∧ a < b ∧ Even (b - a) ∧ IsMF ⊤ b E ∧ (∀ τ : ℍ, E τ = 0 → deriv (E ∘ ofComplex) τ ≠ 0 ∧ ∃ γ : SL(2, ℤ), τ = γ • τ₀) ∧ (∃ c : ℂ, c ≠ 0 ∧ Tendsto E atImInfty (𝓝 c)) ∧ ∀ d : ℤ, 0 ≤ d → (n : ℤ) ∣ d → ∃ e : ℍ → ℂ, IsMF ⊤ (d + a) e ∧ e τ₀ ≠ 0 := by
  intro τ₀
  have hD := cube_sub_sq_ne_zero τ₀
  by_cases h6 : E₆ τ₀ = 0
  · obtain ⟨u, hu, hp⟩ := (GlobalTheory.T.elliptic_points_stabilizer τ₀).1 h6
    have h4 : E₄ τ₀ ≠ 0 := fun h => hD (by simp [h, h6])
    refine ⟨4, 0, 6, E₆, u, hu, by norm_num, hp, by norm_num, by decide, isMF_E₆, fun τ hτ => ⟨?_, ?_⟩,
      ⟨1, one_ne_zero, tendsto_E₆⟩, ?_⟩
    · intro h
      exact GlobalTheory.T.eisenstein_wronskian_ne_zero τ (by simp [h, hτ])
    · exact GlobalTheory.T.j_invariant_equal_sl2_orbit τ τ₀ (by simp [h6, hτ])
    · rintro d hd ⟨m, rfl⟩
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ m by push_cast at hd; omega)
      refine ⟨(E₄ : ℍ → ℂ) ^ m, ?_, by simpa using fun h => absurd h h4⟩
      have := isMF_E₄.pow m
      convert this using 1
      push_cast; ring
  by_cases h4 : E₄ τ₀ = 0
  · obtain ⟨u, hu, hp⟩ := (GlobalTheory.T.elliptic_points_stabilizer τ₀).2 h4
    refine ⟨6, 0, 4, E₄, u, hu, by norm_num, hp, by norm_num, by decide, isMF_E₄, fun τ hτ => ⟨?_, ?_⟩,
      ⟨1, one_ne_zero, tendsto_E₄⟩, ?_⟩
    · intro h
      exact GlobalTheory.T.eisenstein_wronskian_ne_zero τ (by simp [h, hτ])
    · exact GlobalTheory.T.j_invariant_equal_sl2_orbit τ τ₀ (by simp [h4, hτ])
    · rintro d hd ⟨m, rfl⟩
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ m by push_cast at hd; omega)
      refine ⟨(E₆ : ℍ → ℂ) ^ m, ?_, by simpa using fun h => absurd h h6⟩
      have := isMF_E₆.pow m
      convert this using 1
      push_cast; ring
  refine ⟨2, 4, 12, (E₆ τ₀ ^ 2) • (E₄ : ℍ → ℂ) ^ 3 - (E₄ τ₀ ^ 3) • (E₆ : ℍ → ℂ) ^ 2, -1, ?_, by norm_num, ?_,
    by norm_num, by decide, ?_, fun τ hτ => ?_, ⟨E₆ τ₀ ^ 2 - E₄ τ₀ ^ 3, fun h => hD (by linear_combination -h), ?_⟩,
    ?_⟩
  · rw [ModularGroup.SL_neg_smul, one_smul]
  · have : denom ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ₀ = -1 := by simp [denom]
    rw [this]
    exact IsPrimitiveRoot.neg_one 0 (by norm_num)
  · exact ((isMF_E₄.pow 3).smul _).sub ((isMF_E₆.pow 2).smul _)
  · have hz : E₆ τ₀ ^ 2 * E₄ τ ^ 3 - E₄ τ₀ ^ 3 * E₆ τ ^ 2 = 0 := by simpa using hτ
    refine ⟨?_, GlobalTheory.T.j_invariant_equal_sl2_orbit τ τ₀ (by linear_combination hz)⟩
    have hDτ := cube_sub_sq_ne_zero τ
    have k4 : E₄ τ ≠ 0 := by
      intro h
      have : E₆ τ = 0 := by simpa [h, h4] using hz
      exact hDτ (by simp [h, this])
    rw [deriv_comb]
    intro h
    have hW := GlobalTheory.T.eisenstein_wronskian_ne_zero τ
    apply mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h6) (pow_ne_zero 3 k4)) hW
    linear_combination (2 * E₄ τ * deriv (⇑E₆ ∘ ofComplex) τ) * hz - (E₄ τ * E₆ τ) * h
  · have := ((tendsto_E₄.pow 3).const_mul (E₆ τ₀ ^ 2)).sub ((tendsto_E₆.pow 2).const_mul (E₄ τ₀ ^ 3))
    simp only [one_pow, mul_one] at this
    exact this
  · rintro d hd ⟨m, rfl⟩
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ m by push_cast at hd; omega)
    rcases Nat.even_or_odd' m with ⟨p, rfl | rfl⟩
    · refine ⟨(E₄ : ℍ → ℂ) ^ (p + 1), ?_, by simpa using h4⟩
      have := isMF_E₄.pow (p + 1)
      convert this using 1
      push_cast; ring
    · refine ⟨(E₄ : ℍ → ℂ) ^ p * E₆, (isMF_E₄.pow p).mul isMF_E₆ (by push_cast; ring), ?_⟩
      exact mul_ne_zero (pow_ne_zero p h4) h6

end GlobalTheory.LevelOneLocal
