import Mathlib
import Formalism.ThetaSupremumBounds.StatementA

open Finset MeasureTheory
open scoped ComplexConjugate Real

namespace Formalism.DimensionVariation

open Formalism.LatticeIndexTer (ph)

/- English proof (translation)
Introduce `Pl ι _ _ W _ _ _ r ν n s Th c Rc lam Om S hν hνn hs hsq hTc hTs hTb hsupp hR hOm hlam`. Establish `hB` using `hI Pl ι W r ν s Th (fun u => Rc.sum (fun e A => mono (cj u) e • A)) S hν hs hsq hTb hR`. Establish `hJ` using `hF (Pl × ι) Th c S hTc hTs hTb`. Establish `h1 : ∀ e (u : Pl × ι → ℂ), (Th u * (Real.exp (-(nsq u)) : ℂ)) • mono (cj u) e • Rc e = (Th u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) • Rc e` using `fun e u => by`. Rewrite using `[smul_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hint : ∫ u : Pl × ι → ℂ, (Th u * (Real.exp (-(nsq u)) : ℂ)) • Rc.sum (fun e A => mono (cj u) e • A) = (π : ℂ) ^ (Fintype.card Pl * Fintype.card ι) • Rc.sum (fun e A => (c e * (mfact e : ℂ)) • A)`. Simplify using `only [Finsupp.sum, Finset.smul_sum]`. Repeatedly rewrite using `[h1]`.

Rewrite using `[integral_finset_sum _ fun e _ => (hJ e).1.smul_const (Rc e)]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[integral_smul_const, (hJ e).2, Fintype.card_prod, smul_smul]`. Establish `hP : Rc.sum (fun e A => (c e * (mfact e : ℂ) * ∏ x : Pl × ι, lam x.1 ^ e x) • A) = (∏ τ, lam τ ^ n τ) • Rc.sum (fun e A => (c e * (mfact e : ℂ)) • A)`. Simplify using `only [Finsupp.sum, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun e he => ?_` and prove the remaining obligations. Establish `hl : ∏ x : Pl × ι, lam x.1 ^ e x = ∏ τ, lam τ ^ n τ`. Simplify using `only [Fintype.prod_prod_type, Finset.prod_pow_eq_pow_sum]`. Conclude with `Finset.prod_congr rfl fun τ _ => by rw [hsupp e he τ]`. Rewrite using `[hl, smul_smul, mul_comm (∏ τ, lam τ ^ n τ)]`.

Use `set X := Rc.sum (fun e A => (c e * (mfact e : ℂ)) • A) with hXdef`. Establish `hpi : (0 : ℝ) < π ^ (Fintype.card Pl * Fintype.card ι)` using `by positivity`. Establish `hX : ‖X‖ ≤ S * ∏ τ, (Real.exp (1 / 2) * (2 * (n τ : ℝ) + 2) ^ Fintype.card ι * Real.exp ((∑ i, ph (ν τ i)) / 2))`. Rewrite `hB` using `[hint, norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, mul_div_cancel_left₀ _ hpi.ne']`. Simplify `hB` using `only [hνn]`.

Establish `e1 : Real.exp (1 / 2) ^ 2 = Real.exp 1` using `by rw [← Real.exp_nat_mul]; norm_num`. Establish `e2 : ∀ x : ℝ, Real.exp (x / 2) ^ 2 = Real.exp x` using `fun x => by`. Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hY : ∀ τ, (Real.exp (1 / 2) * (2 * (n τ : ℝ) + 2) ^ Fintype.card ι * Real.exp ((∑ i, ph (ν τ i)) / 2)) ^ 2 = Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * Fintype.card ι) * Real.exp (∑ i, ph (ν τ i))` using `fun τ => by`. Rewrite using `[mul_pow, mul_pow, e1, e2, ← pow_mul, mul_comm (Fintype.card ι) 2]`. Establish `hS : ‖X‖ ^ 2 ≤ S ^ 2 * ∏ τ, (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * Fintype.card ι) * Real.exp (∑ i, ph (ν τ i)))`. Establish `h2 : ‖X‖ ^ 2 ≤ (S * ∏ τ, (Real.exp (1 / 2) * (2 * (n τ : ℝ) + 2) ^ Fintype.card ι * Real.exp ((∑ i, ph (ν τ i)) / 2))) ^ 2` using `by gcongr`.

Rewrite `h2` using `[mul_pow, ← Finset.prod_pow, Finset.prod_congr rfl fun τ _ => hY τ]`. Then use the resulting hypothesis. Establish `hL : ‖∏ τ, lam τ ^ n τ‖ ^ 2 = ∏ τ, (Om τ)⁻¹ ^ n τ`. Rewrite using `[norm_prod, ← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[norm_pow, ← pow_mul, mul_comm, pow_mul, hlam]`.

Rewrite using `[hP, norm_smul, mul_pow, hL, Finset.prod_mul_distrib, mul_left_comm (S ^ 2)]`. Conclude with `mul_le_mul_of_nonneg_left hS (Finset.prod_nonneg fun τ _ => pow_nonneg (inv_nonneg.2 (hOm τ).le) _)`.
-/
theorem blockBound_of (hF : FockJet) (hI : BlockIntegral) : BlockBound := by
  intro Pl ι _ _ W _ _ _ r ν n s Th c Rc lam Om S hν hνn hs hsq hTc hTs hTb hsupp hR hOm hlam
  have hB := hI Pl ι W r ν s Th (fun u => Rc.sum (fun e A => mono (cj u) e • A)) S hν hs hsq hTb hR
  have hJ := hF (Pl × ι) Th c S hTc hTs hTb
  have h1 : ∀ e (u : Pl × ι → ℂ), (Th u * (Real.exp (-(nsq u)) : ℂ)) • mono (cj u) e • Rc e =
      (Th u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) • Rc e := fun e u => by
    rw [smul_smul]; congr 1; ring
  have hint : ∫ u : Pl × ι → ℂ, (Th u * (Real.exp (-(nsq u)) : ℂ)) • Rc.sum (fun e A => mono (cj u) e • A) =
      (π : ℂ) ^ (Fintype.card Pl * Fintype.card ι) • Rc.sum (fun e A => (c e * (mfact e : ℂ)) • A) := by
    simp only [Finsupp.sum, Finset.smul_sum]
    simp_rw [h1]
    rw [integral_finset_sum _ fun e _ => (hJ e).1.smul_const (Rc e)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [integral_smul_const, (hJ e).2, Fintype.card_prod, smul_smul]
  have hP : Rc.sum (fun e A => (c e * (mfact e : ℂ) * ∏ x : Pl × ι, lam x.1 ^ e x) • A) =
      (∏ τ, lam τ ^ n τ) • Rc.sum (fun e A => (c e * (mfact e : ℂ)) • A) := by
    simp only [Finsupp.sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have hl : ∏ x : Pl × ι, lam x.1 ^ e x = ∏ τ, lam τ ^ n τ := by
      simp only [Fintype.prod_prod_type, Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_congr rfl fun τ _ => by rw [hsupp e he τ]
    rw [hl, smul_smul, mul_comm (∏ τ, lam τ ^ n τ)]
  set X := Rc.sum (fun e A => (c e * (mfact e : ℂ)) • A) with hXdef
  have hpi : (0 : ℝ) < π ^ (Fintype.card Pl * Fintype.card ι) := by positivity
  have hX : ‖X‖ ≤ S * ∏ τ, (Real.exp (1 / 2) * (2 * (n τ : ℝ) + 2) ^ Fintype.card ι *
      Real.exp ((∑ i, ph (ν τ i)) / 2)) := by
    rw [hint, norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      mul_div_cancel_left₀ _ hpi.ne'] at hB
    simpa only [hνn] using hB
  have e1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have e2 : ∀ x : ℝ, Real.exp (x / 2) ^ 2 = Real.exp x := fun x => by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hY : ∀ τ, (Real.exp (1 / 2) * (2 * (n τ : ℝ) + 2) ^ Fintype.card ι *
      Real.exp ((∑ i, ph (ν τ i)) / 2)) ^ 2 = Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * Fintype.card ι) *
      Real.exp (∑ i, ph (ν τ i)) := fun τ => by
    rw [mul_pow, mul_pow, e1, e2, ← pow_mul, mul_comm (Fintype.card ι) 2]
  have hS : ‖X‖ ^ 2 ≤ S ^ 2 * ∏ τ, (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * Fintype.card ι) *
      Real.exp (∑ i, ph (ν τ i))) := by
    have h2 : ‖X‖ ^ 2 ≤ (S * ∏ τ, (Real.exp (1 / 2) * (2 * (n τ : ℝ) + 2) ^ Fintype.card ι *
        Real.exp ((∑ i, ph (ν τ i)) / 2))) ^ 2 := by gcongr
    rwa [mul_pow, ← Finset.prod_pow, Finset.prod_congr rfl fun τ _ => hY τ] at h2
  have hL : ‖∏ τ, lam τ ^ n τ‖ ^ 2 = ∏ τ, (Om τ)⁻¹ ^ n τ := by
    rw [norm_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [norm_pow, ← pow_mul, mul_comm, pow_mul, hlam]
  rw [hP, norm_smul, mul_pow, hL, Finset.prod_mul_distrib, mul_left_comm (S ^ 2)]
  exact mul_le_mul_of_nonneg_left hS
    (Finset.prod_nonneg fun τ _ => pow_nonneg (inv_nonneg.2 (hOm τ).le) _)

end Formalism.DimensionVariation
