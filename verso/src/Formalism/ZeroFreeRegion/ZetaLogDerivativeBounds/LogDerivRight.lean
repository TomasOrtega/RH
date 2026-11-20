import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormLogDerivLeLamF

open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation

noncomputable section

namespace Formalism.ZF

/- English proof (translation)
Take `⟨B, hB⟩` from `log_deriv_riemannZeta_add_inv_sub_bounded.bound`. Take `⟨ε, hε, hball⟩` from `Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hB)`. Use `⟨max (max B 0) (lamF (1 + ε / 2)), le_max_of_le_left (le_max_right _ _), fun s hs => (norm_logDeriv_le_lamF hs).trans ?_⟩` and prove the remaining obligations. Establish `hσ1 : 0 < s.re - 1` using `sub_pos.mpr hs`. Establish `hpos : 0 < 1 / (s.re - 1)` using `by positivity`.

Break down `lt_or_ge s.re (1 + ε / 2) with hlt | hge` into its components or cases. Establish `hreal : ‖((s.re : ℂ) - 1)‖ = s.re - 1`. Rewrite using `[← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hσ1.le]`. Establish `hd : dist (s.re : ℂ) 1 < ε`. Rewrite using `[Complex.dist_eq, hreal]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hne : (s.re : ℂ) ∈ ({1}ᶜ : Set ℂ)`. Simplify using `only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_eq_one]`. Conclude with `hs.ne'`. Establish `hb` using `hball hd hne`.

Simplify using `only [norm_one, mul_one] at hb`. Establish `hL` using `LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := (s.re : ℂ)) (by simpa using hs)`. Rewrite using `[lamF_eq_norm hs, hL, neg_div, norm_neg]`. Establish `htri : ‖deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)‖ ≤ ‖deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ) + ((s.re : ℂ) - 1)⁻¹‖ + ‖((s.re : ℂ) - 1)⁻¹‖`. Use `norm_sub_le (deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ) + ((s.re : ℂ) - 1)⁻¹) (((s.re : ℂ) - 1)⁻¹)` as an intermediate fact.

Simplify using `using this`. Rewrite `htri` using `[norm_inv, hreal]`. Establish `: B ≤ max (max B 0) (lamF (1 + ε / 2))` using `le_max_of_le_left (le_max_left _ _)`. Rewrite using `[one_div]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1 : lamF s.re ≤ lamF (1 + ε / 2)` using `lamF_anti (by linarith) hge`. Establish `: lamF (1 + ε / 2) ≤ max (max B 0) (lamF (1 + ε / 2))` using `le_max_right _ _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem logDerivBoundRightHalfPlane : LogDerivRight := by
  obtain ⟨B, hB⟩ := log_deriv_riemannZeta_add_inv_sub_bounded.bound
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hB)
  refine ⟨max (max B 0) (lamF (1 + ε / 2)), le_max_of_le_left (le_max_right _ _),
    fun s hs => (norm_logDeriv_le_lamF hs).trans ?_⟩
  have hσ1 : 0 < s.re - 1 := sub_pos.mpr hs
  have hpos : 0 < 1 / (s.re - 1) := by positivity
  rcases lt_or_ge s.re (1 + ε / 2) with hlt | hge
  · have hreal : ‖((s.re : ℂ) - 1)‖ = s.re - 1 := by
      rw [← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hσ1.le]
    have hd : dist (s.re : ℂ) 1 < ε := by
      rw [Complex.dist_eq, hreal]; linarith
    have hne : (s.re : ℂ) ∈ ({1}ᶜ : Set ℂ) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_eq_one]; exact hs.ne'
    have hb := hball hd hne
    simp only [norm_one, mul_one] at hb
    have hL := LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := (s.re : ℂ)) (by simpa using hs)
    rw [lamF_eq_norm hs, hL, neg_div, norm_neg]
    have htri : ‖deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)‖ ≤
        ‖deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ) + ((s.re : ℂ) - 1)⁻¹‖ +
          ‖((s.re : ℂ) - 1)⁻¹‖ := by
      have := norm_sub_le (deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ) +
        ((s.re : ℂ) - 1)⁻¹) (((s.re : ℂ) - 1)⁻¹)
      simpa using this
    rw [norm_inv, hreal] at htri
    have : B ≤ max (max B 0) (lamF (1 + ε / 2)) :=
      le_max_of_le_left (le_max_left _ _)
    rw [one_div]
    linarith
  · have h1 : lamF s.re ≤ lamF (1 + ε / 2) := lamF_anti (by linarith) hge
    have : lamF (1 + ε / 2) ≤ max (max B 0) (lamF (1 + ε / 2)) := le_max_right _ _
    linarith

end Formalism.ZF
