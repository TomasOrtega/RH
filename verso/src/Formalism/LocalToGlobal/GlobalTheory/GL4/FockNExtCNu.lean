import Formalism.LocalToGlobal.Columns.MultiFactorialEqTripleProd
import Formalism.SharpRestriction.GlobalSchurBounds.SlopeMaxOpenOfHookTwoLeV

open MvPolynomial

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.L2.Col Formalism.MainNotions.flipTwoThree Formalism.L2.DIV

section Mono

variable {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.hw Formalism.GradedWeylDivisibility.lpMinor`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, RingHom.map_det]`. Use `congr 2`.

Use extensionality with `p q`. Simplify using `[RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.map_X]`.
-/
private theorem map_algebraMap_rat_complex_hw {N : ℕ} (ν : Fin N → ℕ) :
    MvPolynomial.map (algebraMap ℚ ℂ) (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) ν) = Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν := by
  unfold Formalism.GradedWeylDivisibility.hw Formalism.GradedWeylDivisibility.lpMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext p q
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.map_X]

/- English proof (translation)
Establish `hprod : (∏ s, ((lam.natW s).factorial : ℝ)) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun s _ => by exact_mod_cast (Nat.factorial_pos _).ne'`. Unfold `extremal cNu`. Rewrite using `[← map_algebraMap_rat_complex_hw, Formalism.L2.Col.fock_norm_rational_eq, div_mul_cancel₀ _ hprod]`.
-/
theorem fockN_ext_cNu (lam : DomWeight n) :
    fockN (extremal ℂ n lam) = cNu lam.natW * ∏ s, ((lam.natW s).factorial : ℝ) := by
  have hprod : (∏ s, ((lam.natW s).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun s _ => by exact_mod_cast (Nat.factorial_pos _).ne'
  unfold extremal cNu
  rw [← map_algebraMap_rat_complex_hw, Formalism.L2.Col.fock_norm_rational_eq, div_mul_cancel₀ _ hprod]

/- English proof (translation)
Establish `hnn : (0 : ℚ) ≤ Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW)`. Unfold `Formalism.GradedWeylDivisibility.fockQ`. Conclude with `Finset.sum_nonneg fun m _ => mul_nonneg (mul_self_nonneg _) (Nat.cast_nonneg _)`. Establish `hpos : (0 : ℚ) < Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW)` using `lt_of_le_of_ne hnn (Formalism.L2.DIV.we_hw_norm_ne le_rfl lam.natW).symm`. Unfold `cNu`.

Apply `div_pos` to reduce the goal to its premises. Conclude with `hpos` after adjusting the coercions. Conclude with `Finset.prod_pos fun s _ => by exact_mod_cast Nat.factorial_pos _`.
-/
theorem cNu_natW_pos (lam : DomWeight n) : 0 < cNu lam.natW := by
  have hnn : (0 : ℚ) ≤ Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW) := by
    unfold Formalism.GradedWeylDivisibility.fockQ
    exact Finset.sum_nonneg fun m _ => mul_nonneg (mul_self_nonneg _) (Nat.cast_nonneg _)
  have hpos : (0 : ℚ) < Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW) :=
    lt_of_le_of_ne hnn (Formalism.L2.DIV.we_hw_norm_ne le_rfl lam.natW).symm
  unfold cNu
  apply div_pos
  · exact_mod_cast hpos
  · exact Finset.prod_pos fun s _ => by exact_mod_cast Nat.factorial_pos _

def monCnu (lam : ι → DomWeight n) : ℝ := ((n : ℝ) ^ (∑ τ, dW (lam τ)) * ∏ τ, cNu (lam τ).natW)⁻¹

/- English proof (translation)
Establish `hmul` using `Nat.multinomial_spec Finset.univ g`. Establish `hle : Nat.multinomial Finset.univ g ≤ n ^ (∑ a, g a)`. Establish `h` using `Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin n)) (fun _ => (1 : ℕ)) (∑ a, g a)`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, one_pow, Finset.prod_const_one, Nat.cast_id] at h`. Rewrite using `[h]`.

Apply `Finset.single_le_sum (f := fun k => Nat.multinomial Finset.univ k) (fun _ _ => Nat.zero_le _)` to reduce the goal to its premises. Rewrite using `[Finset.mem_piAntidiag]`. Conclude with `⟨rfl, fun i _ => Finset.mem_univ i⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem sub_one_mul_padicValNat_factorial_le' {n : ℕ} (g : Fin n → ℕ) :
    (∑ a, g a).factorial ≤ n ^ (∑ a, g a) * ∏ a, (g a).factorial := by
  classical
  have hmul := Nat.multinomial_spec Finset.univ g
  have hle : Nat.multinomial Finset.univ g ≤ n ^ (∑ a, g a) := by
    have h := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin n)) (fun _ => (1 : ℕ)) (∑ a, g a)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, one_pow,
      Finset.prod_const_one, Nat.cast_id] at h
    rw [h]
    apply Finset.single_le_sum (f := fun k => Nat.multinomial Finset.univ k) (fun _ _ => Nat.zero_le _)
    rw [Finset.mem_piAntidiag]
    exact ⟨rfl, fun i _ => Finset.mem_univ i⟩
  calc (∑ a, g a).factorial = (∏ a, (g a).factorial) * Nat.multinomial Finset.univ g := hmul.symm
    _ ≤ (∏ a, (g a).factorial) * n ^ (∑ a, g a) := Nat.mul_le_mul_left _ hle
    _ = _ := mul_comm _ _

/- English proof (translation)
Establish `hC : 0 < ∏ τ, cNu (lam τ).natW` using `Finset.prod_pos fun τ _ => cNu_natW_pos (lam τ)`. Establish `hF : (0 : ℝ) < ∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ)` using `Finset.prod_pos fun τ _ => Finset.prod_pos fun s _ => by exact_mod_cast Nat.factorial_pos _`. Establish `hND : (0 : ℝ) < (n : ℝ) ^ (∑ τ, dW (lam τ))`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality.

Simplify using `[dW]`. Conclude with `pow_pos (by exact_mod_cast hn) _`. Establish `hext : extremalFockNormProduct lam = (∏ τ, cNu (lam τ).natW) * ∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ)`. Unfold `extremalFockNormProduct`. Rewrite using `[← Finset.prod_mul_distrib]`.

Conclude with `Finset.prod_congr rfl fun τ _ => fockN_ext_cNu (lam τ)`. Establish `hcombN : ∏ τ, ∏ s, ((lam τ).natW s).factorial ≤ Formalism.L2.DIV.mfact m.1 * n ^ (∑ τ, dW (lam τ))`. Establish `hmf : Formalism.L2.DIV.mfact m.1 = ∏ τ, ∏ s, ∏ a, (m.1 (τ, a, s)).factorial`. Unfold `Formalism.L2.DIV.mfact`. Rewrite using `[Finset.prod_subset (Finset.subset_univ _) (fun k _ hk => by`.

Rewrite using `[show m.1 k = 0 from by simpa using hk, Nat.factorial_zero])]`. Rewrite using `[Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_prod_type, Finset.prod_comm]`. Establish `hpow : n ^ (∑ τ, dW (lam τ)) = ∏ τ, ∏ s, n ^ ((lam τ).natW s)`.

Rewrite using `[← Finset.prod_pow_eq_pow_sum]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Unfold `dW`. Rewrite using `[← Finset.prod_pow_eq_pow_sum]`. Rewrite using `[hmf, hpow, ← Finset.prod_mul_distrib]`.

Apply `Finset.prod_le_prod (fun _ _ => Nat.zero_le _)` to reduce the goal to its premises. Introduce `τ _`. Rewrite using `[← Finset.prod_mul_distrib]`. Apply `Finset.prod_le_prod (fun _ _ => Nat.zero_le _)` to reduce the goal to its premises. Introduce `s _`.

Establish `h` using `sub_one_mul_padicValNat_factorial_le' (fun a => m.1 (τ, a, s))`. Rewrite `h` using `[m.2 τ s]`. Conclude with `h.trans (le_of_eq (mul_comm _ _))`. Establish `hcomb : (∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ)) ≤ (Formalism.L2.DIV.mfact m.1 : ℝ) * (n : ℝ) ^ (∑ τ, dW (lam τ))`. Conclude with `hcombN` after adjusting the coercions.

Unfold `monCnu monW`. Rewrite using `[hext, inv_eq_one_div, div_le_div_iff₀ (mul_pos hND hC) (mul_pos hC hF)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem monW_ge_cNu (lam : ι → DomWeight n) (m : MonI lam) : monCnu lam ≤ monW lam m := by
  classical
  have hC : 0 < ∏ τ, cNu (lam τ).natW := Finset.prod_pos fun τ _ => cNu_natW_pos (lam τ)
  have hF : (0 : ℝ) < ∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ) :=
    Finset.prod_pos fun τ _ => Finset.prod_pos fun s _ => by exact_mod_cast Nat.factorial_pos _
  have hND : (0 : ℝ) < (n : ℝ) ^ (∑ τ, dW (lam τ)) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [dW]
    · exact pow_pos (by exact_mod_cast hn) _
  have hext : extremalFockNormProduct lam = (∏ τ, cNu (lam τ).natW) * ∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ) := by
    unfold extremalFockNormProduct
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => fockN_ext_cNu (lam τ)
  have hcombN : ∏ τ, ∏ s, ((lam τ).natW s).factorial ≤ Formalism.L2.DIV.mfact m.1 * n ^ (∑ τ, dW (lam τ)) := by
    have hmf : Formalism.L2.DIV.mfact m.1 = ∏ τ, ∏ s, ∏ a, (m.1 (τ, a, s)).factorial := by
      unfold Formalism.L2.DIV.mfact
      rw [Finset.prod_subset (Finset.subset_univ _) (fun k _ hk => by
        rw [show m.1 k = 0 from by simpa using hk, Nat.factorial_zero])]
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [Fintype.prod_prod_type, Finset.prod_comm]
    have hpow : n ^ (∑ τ, dW (lam τ)) = ∏ τ, ∏ s, n ^ ((lam τ).natW s) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun τ _ => ?_
      unfold dW
      rw [← Finset.prod_pow_eq_pow_sum]
    rw [hmf, hpow, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro τ _
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro s _
    have h := sub_one_mul_padicValNat_factorial_le' (fun a => m.1 (τ, a, s))
    rw [m.2 τ s] at h
    exact h.trans (le_of_eq (mul_comm _ _))
  have hcomb : (∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ)) ≤
      (Formalism.L2.DIV.mfact m.1 : ℝ) * (n : ℝ) ^ (∑ τ, dW (lam τ)) := by
    exact_mod_cast hcombN
  unfold monCnu monW
  rw [hext, inv_eq_one_div, div_le_div_iff₀ (mul_pos hND hC) (mul_pos hC hF)]
  calc 1 * ((∏ τ, cNu (lam τ).natW) * ∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ))
      = (∏ τ, cNu (lam τ).natW) * ∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ) := one_mul _
    _ ≤ (∏ τ, cNu (lam τ).natW) * ((Formalism.L2.DIV.mfact m.1 : ℝ) * (n : ℝ) ^ (∑ τ, dW (lam τ))) :=
      mul_le_mul_of_nonneg_left hcomb hC.le
    _ = _ := by ring

/- English proof (translation)
Unfold `monCnu`. Apply `inv_pos.mpr` to reduce the goal to its premises. Apply `mul_pos` to reduce the goal to its premises. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality.

Simplify using `[dW]`. Conclude with `pow_pos (by exact_mod_cast hn) _`. Conclude with `Finset.prod_pos fun τ _ => cNu_natW_pos (lam τ)`.
-/
theorem monCnu_pos (lam : ι → DomWeight n) : 0 < monCnu lam := by
  unfold monCnu
  apply inv_pos.mpr
  apply mul_pos
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [dW]
    · exact pow_pos (by exact_mod_cast hn) _
  · exact Finset.prod_pos fun τ _ => cNu_natW_pos (lam τ)

/- English proof (translation)
Establish `hn' : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `hc : ∀ τ, cNu (lam τ).natW ≠ 0` using `fun τ => (cNu_natW_pos (lam τ)).ne'`. Unfold `monCnu`. Rewrite using `[Real.log_inv, neg_neg, Real.log_mul (pow_ne_zero _ hn'.ne') (Finset.prod_ne_zero_iff.mpr fun τ _ => hc τ), Real.log_pow, Real.log_prod (fun τ _ => hc τ), Finset.sum_add_distrib]`. Use `push_cast`.

Rewrite using `[Finset.sum_mul]`.
-/
theorem log_monCnu (lam : ι → DomWeight n) (hn : 0 < n) :
    -Real.log (monCnu lam) = ∑ τ, ((dW (lam τ) : ℝ) * Real.log n + Real.log (cNu (lam τ).natW)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : ∀ τ, cNu (lam τ).natW ≠ 0 := fun τ => (cNu_natW_pos (lam τ)).ne'
  unfold monCnu
  rw [Real.log_inv, neg_neg, Real.log_mul (pow_ne_zero _ hn'.ne') (Finset.prod_ne_zero_iff.mpr fun τ _ => hc τ),
    Real.log_pow, Real.log_prod (fun τ _ => hc τ), Finset.sum_add_distrib]
  push_cast
  rw [Finset.sum_mul]

end Mono

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
