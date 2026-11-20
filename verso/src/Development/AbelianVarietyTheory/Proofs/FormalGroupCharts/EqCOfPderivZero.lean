import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace GlobalTheory.FormalLog

variable {k : Type} [CommRing k] {σ τ : Type}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pderiv_subst [Fintype σ] {a : σ → MvPowerSeries τ k} (ha : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries σ k) (t : τ) :
    pderiv k t (subst a f) = ∑ s, subst a (pderiv k s f) * pderiv k t (a s) :=
  GlobalTheory.FormalCalc.pderiv_subst (hasSubst_of_constantCoeff_zero ha) f t

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pderiv_comm (u v : τ) (g : MvPowerSeries τ k) : pderiv k u (pderiv k v g) = pderiv k v (pderiv k u g) := by
  classical
  ext n
  simp only [coeff_pderiv]
  by_cases h : u = v
  · subst h; rfl
  · rw [show n + Finsupp.single u 1 + Finsupp.single v 1 = n + Finsupp.single v 1 + Finsupp.single u 1 by abel]
    simp only [Finsupp.add_apply, Finsupp.single_apply, if_neg h, if_neg (Ne.symm h), add_zero]
    ring

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Substitute using the available equality. Both sides reduce to the same expression. Extract witnesses or component facts from the available result.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem eq_C_of_pderiv_zero [Algebra ℚ k] {g : MvPowerSeries τ k} (h : ∀ v, pderiv k v g = 0) :
    g = C (constantCoeff g) := by
  classical
  ext n
  rw [coeff_C]
  split_ifs with hn
  · subst hn; rfl
  · obtain ⟨v, hv⟩ : ∃ v, n v ≠ 0 := by
      by_contra hc; push Not at hc; exact hn (Finsupp.ext hc)
    have hle : Finsupp.single v 1 ≤ n := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hv)
    have h1 := congrArg (coeff (n - Finsupp.single v 1)) (h v)
    rw [coeff_pderiv, map_zero, tsub_add_cancel_of_le hle] at h1
    have hc' : (n - Finsupp.single v 1 : τ →₀ ℕ) v + 1 = n v := by
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
    have hc : (((n - Finsupp.single v 1 : τ →₀ ℕ) v : ℕ) : k) + 1 = ((n v : ℕ) : k) := by
      rw [← hc']; push_cast; ring
    rw [hc] at h1
    have hu : IsUnit ((n v : ℕ) : k) := by
      have : ((n v : ℕ) : k) = algebraMap ℚ k (n v : ℚ) := by simp
      rw [this]; exact (IsUnit.mk0 _ (by exact_mod_cast hv)).map _
    rcases hu with ⟨w, hw⟩
    rw [← hw] at h1
    simpa using congrArg (· * ((w⁻¹ : kˣ) : k)) h1

end GlobalTheory.FormalLog
