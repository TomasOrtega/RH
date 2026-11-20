import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLatTau
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModCMPoint
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModVanish
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmForm
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmQ

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Establish `hmon : (Polynomial.C (P.leadingCoeff)⁻¹ * P).Monic` using `Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ h0)`. Establish `hdeg : (Polynomial.C (P.leadingCoeff)⁻¹ * P).natDegree ≠ 0`. Rewrite using `[Polynomial.natDegree_C_mul (inv_ne_zero h0)]`. Introduce `hd`. Rewrite `hx` using `[Polynomial.eq_C_of_natDegree_eq_zero hd, Polynomial.eval_C]`.

Apply `h0` to reduce the goal to its premises. Rewrite using `[Polynomial.leadingCoeff, hd]`. Conclude with `hx`. Use `IsIntegral.of_aeval_monic_of_isIntegral_coeff hmon hdeg ?_ ?_` and prove the remaining obligations. Rewrite using `[Polynomial.eval_mul, hx, mul_zero]`.

Conclude with `isIntegral_zero`. Introduce `i`. Rewrite using `[Polynomial.coeff_C_mul]`. Conclude with `hu.mul (hP i)`.
-/
theorem isIntegral_of_root {P : Polynomial ℂ} (hP : ∀ i, IsIntegral ℤ (P.coeff i))
    (hu : IsIntegral ℤ (P.leadingCoeff)⁻¹) (h0 : P.leadingCoeff ≠ 0) {x : ℂ} (hx : P.eval x = 0) :
    IsIntegral ℤ x := by
  have hmon : (Polynomial.C (P.leadingCoeff)⁻¹ * P).Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ h0)
  have hdeg : (Polynomial.C (P.leadingCoeff)⁻¹ * P).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_C_mul (inv_ne_zero h0)]
    intro hd
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd, Polynomial.eval_C] at hx
    apply h0
    rw [Polynomial.leadingCoeff, hd]
    exact hx
  refine IsIntegral.of_aeval_monic_of_isIntegral_coeff hmon hdeg ?_ ?_
  · rw [Polynomial.eval_mul, hx, mul_zero]
    exact isIntegral_zero
  · intro i
    rw [Polynomial.coeff_C_mul]
    exact hu.mul (hP i)

/- English proof (translation)
Take `⟨n0, u, hu1, hu2, hu3, hlow, hcoef⟩` from `gmQ_low hm hsq`. Establish `hmf : IsMF (12 * ((2 * (Tm m).card : ℕ) : ℤ)) (Gm m)` using `(gmForm hm).congr_weight (by push_cast; ring)`. Take `⟨P, hPR, -, hlead, hval⟩` from `qPrin_low (Rm m) _ (Gm m) hmf (gmQ_coeffIn hm) n0 u hu3 hlow hcoef`. Establish `h1` using `hval τ`. Rewrite `h1` using `[h]`.

Establish `h2 : P.eval (jT τ) = 0`. Break down `mul_eq_zero.mp h1.symm with h3 | h3` into its components or cases. Conclude with `absurd h3 (pow_ne_zero _ (DD_ne_zero τ))`. Conclude with `h3`. Conclude with `isIntegral_of_root (fun i => Rm_isIntegral hm (hPR i)) (by rw [hlead]; exact Rm_isIntegral hm hu2) (by rw [hlead]; exact hu3) h2`.
-/
theorem jT_isIntegral {m : ℕ} (hm : 0 < m) (hsq : ¬ IsSquare m) {τ : ℍ} (h : Gm m τ = 0) :
    IsIntegral ℤ (jT τ) := by
  obtain ⟨n0, u, hu1, hu2, hu3, hlow, hcoef⟩ := gmQ_low hm hsq
  have hmf : IsMF (12 * ((2 * (Tm m).card : ℕ) : ℤ)) (Gm m) :=
    (gmForm hm).congr_weight (by push_cast; ring)
  obtain ⟨P, hPR, -, hlead, hval⟩ := qPrin_low (Rm m) _ (Gm m) hmf (gmQ_coeffIn hm) n0 u hu3 hlow hcoef
  have h1 := hval τ
  rw [h] at h1
  have h2 : P.eval (jT τ) = 0 := by
    rcases mul_eq_zero.mp h1.symm with h3 | h3
    · exact absurd h3 (pow_ne_zero _ (DD_ne_zero τ))
    · exact h3
  exact isIntegral_of_root (fun i => Rm_isIntegral hm (hPR i)) (by rw [hlead]; exact Rm_isIntegral hm hu2)
    (by rw [hlead]; exact hu3) h2

/- English proof (translation)
Introduce `d L hsf hd4 hL`. Take `⟨c, τ, hτ⟩` from `latTau L`. Establish `hd : 0 < d` using `by omega`. Take `⟨A, B, C, D, h1, h2, h3⟩` from `cmPoint hd hL hτ (-1) 2`. Rewrite using `[jInv_eq_jT hτ]`.

Use `jT_isIntegral hd ?_ (Gm_vanish hd τ A B C D (by linarith) ?_)` and prove the remaining obligations. Introduce and unpack `⟨r, hr⟩`. Establish `: r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3` using `by omega`. Apply the tactic sequence `rcases this with h | h | h | h <;> simp [hr, Nat.mul_mod, h] at hd4`. Rewrite using `[← h1, h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cm1 : JInvariantIntegrality := by
  intro d L hsf hd4 hL
  obtain ⟨c, τ, hτ⟩ := latTau L
  have hd : 0 < d := by omega
  obtain ⟨A, B, C, D, h1, h2, h3⟩ := cmPoint hd hL hτ (-1) 2
  rw [jInv_eq_jT hτ]
  refine jT_isIntegral hd ?_ (Gm_vanish hd τ A B C D (by linarith) ?_)
  · rintro ⟨r, hr⟩
    have : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
    rcases this with h | h | h | h <;> simp [hr, Nat.mul_mod, h] at hd4
  · rw [← h1, h2]; ring

end ReciprocityTheory.ChartRestriction.L1
