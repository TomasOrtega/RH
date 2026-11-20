import Mathlib
import Formalism.PeriodIntegrals.Transference
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.DualTransport

open Module

namespace PI.Tr

/- English proof (translation)
Establish `hrk : finrank ℤ Λ = 1` using `(ZLattice.rank ℝ Λ).trans h1`. Set `b` to `Module.finBasisOfFinrankEq ℤ Λ hrk`. Use `⟨(b 0 : E), (b 0).2, fun h => b.ne_zero 0 (Subtype.ext h), ?_⟩` and prove the remaining obligations. Introduce `x hx`. Use `⟨b.repr ⟨x, hx⟩ 0, ?_⟩` and prove the remaining obligations.

Establish `h2 : ((b.repr ⟨x, hx⟩ 0 • b 0 : Λ) : E) = x`. Establish `hs` using `b.sum_repr ⟨x, hx⟩`. Rewrite `hs` using `[Fin.sum_univ_one]`. Rewrite using `[hs]`. Rewrite using `[Int.cast_smul_eq_zsmul]`.

Conclude with `h2.symm.trans (Submodule.coe_smul _ _)`.
-/
private theorem exists_generator_of_finrank_eq_one_zLattice {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (h1 : finrank ℝ E = 1) :
    ∃ a ∈ Λ, a ≠ 0 ∧ ∀ x ∈ Λ, ∃ k : ℤ, x = (k : ℝ) • a := by
  have hrk : finrank ℤ Λ = 1 := (ZLattice.rank ℝ Λ).trans h1
  let b := Module.finBasisOfFinrankEq ℤ Λ hrk
  refine ⟨(b 0 : E), (b 0).2, fun h => b.ne_zero 0 (Subtype.ext h), ?_⟩
  intro x hx
  refine ⟨b.repr ⟨x, hx⟩ 0, ?_⟩
  have h2 : ((b.repr ⟨x, hx⟩ 0 • b 0 : Λ) : E) = x := by
    have hs := b.sum_repr ⟨x, hx⟩
    rw [Fin.sum_univ_one] at hs
    rw [hs]
  rw [Int.cast_smul_eq_zsmul]
  exact h2.symm.trans (Submodule.coe_smul _ _)

/- English proof (translation)
Introduce `E _ _ _ Λ _ _ lam u hdim hlam hdual`. Establish `hdim' : finrank ℝ E ≤ 1` using `hdim`. Break down `Nat.le_one_iff_eq_zero_or_eq_one.mp hdim' with h0 | h1` into its components or cases. Establish `: Subsingleton E` using `Module.finrank_zero_iff.mp h0`. Use `⟨0, Λ.zero_mem, ?_⟩` and prove the remaining obligations.

Rewrite using `[Subsingleton.elim u 0, h0]`. Simplify using the standard rewrite rules. Take `⟨a, haΛ, ha0, hmul⟩` from `exists_generator_of_finrank_eq_one_zLattice Λ h1`. Choose the witnesses or unpack the hypotheses as in `⟨t, rfl⟩ : ∃ t : ℝ, u = t • a := by`. Take `⟨c, hc⟩` from `(finrank_eq_one_iff_of_nonzero' a ha0).mp h1 u`.

Conclude with `⟨c, hc.symm⟩`. Establish `hα : 0 < ‖a‖` using `norm_pos_iff.mpr ha0`. Rewrite using `[h1, Nat.cast_one]`. Distinguish the cases in `hc : lam * ‖a‖ ≤ 1`. Use `⟨((round t : ℤ) : ℝ) • a, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Int.cast_smul_eq_zsmul]`. Conclude with `Λ.smul_mem _ haΛ`. Rewrite using `[← sub_smul, norm_smul, Real.norm_eq_abs]`. Combine the equalities or inequalities in the displayed calculation. Use `push Not at hc`.

Establish `hα2 : ‖a‖ ^ 2 ≠ 0` using `by positivity`. Establish `key : ∀ s : ℝ, inner ℝ (s • a) ((‖a‖ ^ 2)⁻¹ • a) = s`. Introduce `s`. Rewrite using `[real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, inv_mul_cancel₀ hα2, mul_one]`. Establish `hnorm : ‖(‖a‖ ^ 2)⁻¹ • a‖ < lam`.

Rewrite using `[norm_smul, norm_inv, norm_pow, norm_norm]`. Establish `e : (‖a‖ ^ 2)⁻¹ * ‖a‖ * ‖a‖ = 1`. Rewrite using `[mul_assoc, ← sq, inv_mul_cancel₀ hα2]`. Establish `hlt : (‖a‖ ^ 2)⁻¹ * ‖a‖ * ‖a‖ < lam * ‖a‖`. Rewrite using `[e]`.

Conclude with `hc`. Conclude with `lt_of_mul_lt_mul_right hlt hα.le`. Take `⟨m, hm⟩` from `hdual ((‖a‖ ^ 2)⁻¹ • a) (by`. Introduce `x hx`. Take `⟨k, rfl⟩` from `hmul x hx`.

Conclude with `⟨k, key _⟩) hnorm`. Rewrite `hm` using `[key]`. Use `⟨(m : ℝ) • a, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Int.cast_smul_eq_zsmul]`. Conclude with `Λ.smul_mem _ haΛ`.

Rewrite using `[hm, sub_self, norm_zero, zero_mul]`. Evaluate the numerical expressions.
-/
theorem keySmall : KeySmall := by
  intro E _ _ _ Λ _ _ lam u hdim hlam hdual
  have hdim' : finrank ℝ E ≤ 1 := hdim
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdim' with h0 | h1
  · have : Subsingleton E := Module.finrank_zero_iff.mp h0
    refine ⟨0, Λ.zero_mem, ?_⟩
    rw [Subsingleton.elim u 0, h0]
    simp
  · obtain ⟨a, haΛ, ha0, hmul⟩ := exists_generator_of_finrank_eq_one_zLattice Λ h1
    obtain ⟨t, rfl⟩ : ∃ t : ℝ, u = t • a := by
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' a ha0).mp h1 u
      exact ⟨c, hc.symm⟩
    have hα : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    rw [h1, Nat.cast_one]
    by_cases hc : lam * ‖a‖ ≤ 1
    · refine ⟨((round t : ℤ) : ℝ) • a, ?_, ?_⟩
      · rw [Int.cast_smul_eq_zsmul]
        exact Λ.smul_mem _ haΛ
      · rw [← sub_smul, norm_smul, Real.norm_eq_abs]
        calc |t - ((round t : ℤ) : ℝ)| * ‖a‖ * lam ≤ (1 / 2) * ‖a‖ * lam :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (abs_sub_round t) (norm_nonneg a)) hlam.le
          _ = (1 / 2) * (lam * ‖a‖) := by ring
          _ ≤ (1 / 2) * 1 := mul_le_mul_of_nonneg_left hc (by norm_num)
          _ = 1 / 2 := by ring
    · push Not at hc
      have hα2 : ‖a‖ ^ 2 ≠ 0 := by positivity
      have key : ∀ s : ℝ, inner ℝ (s • a) ((‖a‖ ^ 2)⁻¹ • a) = s := by
        intro s
        rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
          inv_mul_cancel₀ hα2, mul_one]
      have hnorm : ‖(‖a‖ ^ 2)⁻¹ • a‖ < lam := by
        rw [norm_smul, norm_inv, norm_pow, norm_norm]
        have e : (‖a‖ ^ 2)⁻¹ * ‖a‖ * ‖a‖ = 1 := by
          rw [mul_assoc, ← sq, inv_mul_cancel₀ hα2]
        have hlt : (‖a‖ ^ 2)⁻¹ * ‖a‖ * ‖a‖ < lam * ‖a‖ := by
          rw [e]
          exact hc
        exact lt_of_mul_lt_mul_right hlt hα.le
      obtain ⟨m, hm⟩ := hdual ((‖a‖ ^ 2)⁻¹ • a)
        (by
          intro x hx
          obtain ⟨k, rfl⟩ := hmul x hx
          exact ⟨k, key _⟩) hnorm
      rw [key] at hm
      refine ⟨(m : ℝ) • a, ?_, ?_⟩
      · rw [Int.cast_smul_eq_zsmul]
        exact Λ.smul_mem _ haΛ
      · rw [hm, sub_self, norm_zero, zero_mul]
        norm_num

end PI.Tr
