import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.CotQExp

/- English proof (translation)
Establish `h : (π : ℂ) * Complex.cot (π * w) = π * Complex.I - 2 * π * Complex.I * ∑' n : ℕ, cexp (2 * π * Complex.I * w) ^ n` using `pi_mul_cot_pi_q_exp (⟨w, hw⟩ : ℍ)`. Establish `hq : ‖cexp (2 * π * Complex.I * w)‖ < 1` using `UpperHalfPlane.norm_exp_two_pi_I_lt_one (⟨w, hw⟩ : ℍ)`. Establish `hs : Summable fun n : ℕ => cexp (2 * π * Complex.I * w) ^ n` using `summable_geometric_of_norm_lt_one hq`. Establish `hs1 : Summable fun n : ℕ => cexp (2 * π * Complex.I * w) ^ (n + 1)` using `(summable_nat_add_iff 1).2 hs`. Establish `h2` using `hs1.hasSum.mul_left (-2 * π * Complex.I)`.

Establish `e : (π : ℂ) * Complex.cot (π * w) + π * Complex.I = -2 * π * Complex.I * ∑' n : ℕ, cexp (2 * π * Complex.I * w) ^ (n + 1)`. Rewrite using `[h, hs.tsum_eq_zero_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h2`.
-/
theorem hasSum_pi_cot (w : ℂ) (hw : 0 < w.im) :
    HasSum (fun m : ℕ => -2 * π * Complex.I * cexp (2 * π * Complex.I * w) ^ (m + 1))
      (π * Complex.cot (π * w) + π * Complex.I) := by
  have h : (π : ℂ) * Complex.cot (π * w) =
      π * Complex.I - 2 * π * Complex.I * ∑' n : ℕ, cexp (2 * π * Complex.I * w) ^ n :=
    pi_mul_cot_pi_q_exp (⟨w, hw⟩ : ℍ)
  have hq : ‖cexp (2 * π * Complex.I * w)‖ < 1 :=
    UpperHalfPlane.norm_exp_two_pi_I_lt_one (⟨w, hw⟩ : ℍ)
  have hs : Summable fun n : ℕ => cexp (2 * π * Complex.I * w) ^ n :=
    summable_geometric_of_norm_lt_one hq
  have hs1 : Summable fun n : ℕ => cexp (2 * π * Complex.I * w) ^ (n + 1) :=
    (summable_nat_add_iff 1).2 hs
  have h2 := hs1.hasSum.mul_left (-2 * π * Complex.I)
  have e : (π : ℂ) * Complex.cot (π * w) + π * Complex.I =
      -2 * π * Complex.I * ∑' n : ℕ, cexp (2 * π * Complex.I * w) ^ (n + 1) := by
    rw [h, hs.tsum_eq_zero_add]
    ring
  rw [e]
  exact h2

/- English proof (translation)
Introduce `L φ z hL hz h0`. Establish `hLc : (L : ℂ) ≠ 0` using `by exact_mod_cast hL.ne'`. Establish `hLr : (0 : ℝ) < L` using `by exact_mod_cast hL`. Establish `hsum0 : ∑ r ∈ Finset.range L, φ r = 0`. Simplify `h0` using `[hat]`.

Establish `him : ∀ r : ℕ, 0 < ((z + r) / L : ℂ).im`. Introduce `r`. Rewrite using `[Complex.div_natCast_im]`. Simplify using `using div_pos hz hLr`. Establish `hs` using `hasSum_sum (s := Finset.range L) (fun r _ => (hasSum_pi_cot _ (him r)).mul_left (φ r / L))`.

Rewrite using `[← tsum_mul_left]`. Establish `e1 : ∑ r ∈ Finset.range L, φ r * (π / L * Complex.cot (π * ((z + r) / L))) = ∑ r ∈ Finset.range L, φ r / L * (π * Complex.cot (π * ((z + r) / L)) + π * Complex.I)`. Establish `: ∑ r ∈ Finset.range L, φ r / L * (π * Complex.cot (π * ((z + r) / L)) + π * Complex.I) = ∑ r ∈ Finset.range L, φ r * (π / L * Complex.cot (π * ((z + r) / L))) + (∑ r ∈ Finset.range L, φ r) * (π * Complex.I / L)`. Rewrite using `[Finset.sum_mul, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hsum0, zero_mul, add_zero]`. Rewrite using `[e1, ← hs.tsum_eq]`. Use `tsum_congr fun m => ?_` and prove the remaining obligations. Rewrite using `[hat, Finset.sum_mul, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[← Complex.exp_nat_mul, mul_assoc (φ r), ← Complex.exp_add]`. Establish `e2 : ((m + 1 : ℕ) : ℂ) * (2 * π * Complex.I * ((z + r) / L)) = 2 * π * Complex.I * (r * (((m + 1 : ℕ) : ℤ) : ℂ)) / L + 2 * π * Complex.I * (m + 1 : ℕ) * z / L`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_cot_eq_qexp : ∀ (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 0 < L → 0 < z.im → hat φ 0 = 0 →
    ∑ r ∈ Finset.range L, φ r * (π / L * Complex.cot (π * ((z + r) / L))) =
      -2 * π * Complex.I / L *
        ∑' m : ℕ, hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L) := by
  intro L φ z hL hz h0
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hsum0 : ∑ r ∈ Finset.range L, φ r = 0 := by
    simpa [hat] using h0
  have him : ∀ r : ℕ, 0 < ((z + r) / L : ℂ).im := by
    intro r
    rw [Complex.div_natCast_im]
    simpa using div_pos hz hLr
  have hs := hasSum_sum (s := Finset.range L)
    (fun r _ => (hasSum_pi_cot _ (him r)).mul_left (φ r / L))
  rw [← tsum_mul_left]
  have e1 : ∑ r ∈ Finset.range L, φ r * (π / L * Complex.cot (π * ((z + r) / L))) =
      ∑ r ∈ Finset.range L, φ r / L * (π * Complex.cot (π * ((z + r) / L)) + π * Complex.I) := by
    have : ∑ r ∈ Finset.range L, φ r / L * (π * Complex.cot (π * ((z + r) / L)) + π * Complex.I)
        = ∑ r ∈ Finset.range L, φ r * (π / L * Complex.cot (π * ((z + r) / L)))
          + (∑ r ∈ Finset.range L, φ r) * (π * Complex.I / L) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    rw [this, hsum0, zero_mul, add_zero]
  rw [e1, ← hs.tsum_eq]
  refine tsum_congr fun m => ?_
  rw [hat, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Complex.exp_nat_mul, mul_assoc (φ r), ← Complex.exp_add]
  have e2 : ((m + 1 : ℕ) : ℂ) * (2 * π * Complex.I * ((z + r) / L)) =
      2 * π * Complex.I * (r * (((m + 1 : ℕ) : ℤ) : ℂ)) / L
        + 2 * π * Complex.I * (m + 1 : ℕ) * z / L := by
    push_cast
    ring
  rw [e2]
  ring

end GlobalTheory.CotQExp
