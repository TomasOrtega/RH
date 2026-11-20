import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ComplexConjugate
open MvPolynomial

noncomputable section

namespace FSInv

open CP

/- English proof (translation)
Introduce `N n P hP`. Establish `hdeg : ∀ a ∈ P.support, a.degree = n` using `fun a ha => (IsHomogeneous.degree_eq_sum_deg_support ((mem_homogeneousSubmodule _ _).mp hP) ha).symm`. Establish `hmem : ∀ a ∈ P.support, monomial a (1 : ℂ) ∈ H0 N n` using `fun a ha => (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial _ (hdeg a ha))`. Establish `hsum : ∀ s ⊆ P.support, (∑ b ∈ s, P.coeff b • monomial b (1 : ℂ)) ∈ H0 N n` using `fun s hs => Submodule.sum_mem _ fun b hb => Submodule.smul_mem _ _ (hmem b (hs hb))`. Establish `hright : ∀ R ∈ H0 N n, ∀ s ⊆ P.support, l2Inner (N` using `N) n R (∑ b ∈ s, P.coeff b • monomial b (1 : ℂ)) = ∑ b ∈ s, P.coeff b * l2Inner n R (monomial b 1) := by`.

Introduce `R hR s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _`. Simplify using `[l2Inner, fsPair]`. Consider the case `insert b s hb ih`.

Introduce `hs`. Establish `hs' : s ⊆ P.support` using `(Finset.subset_insert _ _).trans hs`. Rewrite using `[Finset.sum_insert hb, Finset.sum_insert hb, add_comm, (hS N n _ _ R (hsum s hs') (hmem b (hs (Finset.mem_insert_self _ _))) hR _).2.1, ih hs', add_comm]`. Establish `hleft : ∀ R ∈ H0 N n, ∀ s ⊆ P.support, l2Inner (N` using `N) n (∑ b ∈ s, P.coeff b • monomial b (1 : ℂ)) R = ∑ b ∈ s, conj (P.coeff b) * l2Inner n (monomial b 1) R := by`. Introduce `R hR s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _`. Simplify using `[l2Inner, fsPair]`. Consider the case `insert b s hb ih`. Introduce `hs`.

Establish `hs' : s ⊆ P.support` using `(Finset.subset_insert _ _).trans hs`. Rewrite using `[Finset.sum_insert hb, Finset.sum_insert hb, add_comm, (hS N n _ _ R (hsum s hs') (hmem b (hs (Finset.mem_insert_self _ _))) hR _).1, ih hs', add_comm]`. Establish `hPs : P = ∑ a ∈ P.support, P.coeff a • monomial a (1 : ℂ)` using `by conv_lhs => rw [P.as_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`.

Establish `hdiag : ∀ a ∈ P.support, l2Inner (N` using `N) n (monomial a (1 : ℂ)) (monomial a 1) = (((∏ i, ((a i).factorial : ℝ)) * N.factorial / (n + N).factorial : ℝ) : ℂ) := by`. Introduce `a ha`. Rewrite using `[hI, ← fubiniStudy_l2Norm_sq_eq, ← hdeg a ha, fubiniStudy_l2Norm_monomial_sq]`. Establish `key : l2Inner (N` using `N) n P P = ∑ a ∈ P.support, conj (P.coeff a) * P.coeff a * (((∏ i, ((a i).factorial : ℝ)) * N.factorial / (n + N).factorial : ℝ) : ℂ) := by conv_lhs => rw [hPs]`. Rewrite using `[hleft _ (hsum _ subset_rfl) _ subset_rfl]`.

Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Rewrite using `[hright _ (hmem a ha) _ subset_rfl, Finset.mul_sum, Finset.sum_eq_single a, hdiag a ha, mul_assoc]`. Introduce `b hb hba`. Establish `h0 : l2Inner (N` using `N) n (monomial a (1 : ℂ)) (monomial b 1) = 0 := by`. Rewrite using `[← hdeg a ha]`.

Conclude with `hO N a b (Ne.symm hba) (by rw [hdeg a ha, hdeg b hb])`. Rewrite using `[h0, mul_zero, mul_zero]`. Introduce `ha'`. Conclude with `absurd ha ha'`. Rewrite using `[fubiniStudy_l2Norm_sq_eq]`.

Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[← hI N n P, key]`. Use `push_cast`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.conj_mul']`.
-/
theorem Parseval.proof (hO : Orth.Statement) (hS : Sesq.Statement) (hI : InnerSelf.Statement) :
    Parseval.Statement := by
  intro N n P hP
  have hdeg : ∀ a ∈ P.support, a.degree = n := fun a ha =>
    (IsHomogeneous.degree_eq_sum_deg_support ((mem_homogeneousSubmodule _ _).mp hP) ha).symm
  have hmem : ∀ a ∈ P.support, monomial a (1 : ℂ) ∈ H0 N n := fun a ha =>
    (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial _ (hdeg a ha))
  have hsum : ∀ s ⊆ P.support, (∑ b ∈ s, P.coeff b • monomial b (1 : ℂ)) ∈ H0 N n := fun s hs =>
    Submodule.sum_mem _ fun b hb => Submodule.smul_mem _ _ (hmem b (hs hb))

  have hright : ∀ R ∈ H0 N n, ∀ s ⊆ P.support,
      l2Inner (N := N) n R (∑ b ∈ s, P.coeff b • monomial b (1 : ℂ)) =
        ∑ b ∈ s, P.coeff b * l2Inner n R (monomial b 1) := by
    intro R hR s
    induction s using Finset.induction_on with
    | empty => intro _; simp [l2Inner, fsPair]
    | insert b s hb ih =>
      intro hs
      have hs' : s ⊆ P.support := (Finset.subset_insert _ _).trans hs
      rw [Finset.sum_insert hb, Finset.sum_insert hb, add_comm,
        (hS N n _ _ R (hsum s hs') (hmem b (hs (Finset.mem_insert_self _ _))) hR _).2.1,
        ih hs', add_comm]

  have hleft : ∀ R ∈ H0 N n, ∀ s ⊆ P.support,
      l2Inner (N := N) n (∑ b ∈ s, P.coeff b • monomial b (1 : ℂ)) R =
        ∑ b ∈ s, conj (P.coeff b) * l2Inner n (monomial b 1) R := by
    intro R hR s
    induction s using Finset.induction_on with
    | empty => intro _; simp [l2Inner, fsPair]
    | insert b s hb ih =>
      intro hs
      have hs' : s ⊆ P.support := (Finset.subset_insert _ _).trans hs
      rw [Finset.sum_insert hb, Finset.sum_insert hb, add_comm,
        (hS N n _ _ R (hsum s hs') (hmem b (hs (Finset.mem_insert_self _ _))) hR _).1,
        ih hs', add_comm]
  have hPs : P = ∑ a ∈ P.support, P.coeff a • monomial a (1 : ℂ) := by
    conv_lhs => rw [P.as_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_monomial, smul_eq_mul, mul_one]
  have hdiag : ∀ a ∈ P.support, l2Inner (N := N) n (monomial a (1 : ℂ)) (monomial a 1) =
      (((∏ i, ((a i).factorial : ℝ)) * N.factorial / (n + N).factorial : ℝ) : ℂ) := by
    intro a ha
    rw [hI, ← fubiniStudy_l2Norm_sq_eq, ← hdeg a ha, fubiniStudy_l2Norm_monomial_sq]
  have key : l2Inner (N := N) n P P = ∑ a ∈ P.support, conj (P.coeff a) * P.coeff a *
      (((∏ i, ((a i).factorial : ℝ)) * N.factorial / (n + N).factorial : ℝ) : ℂ) := by
    conv_lhs => rw [hPs]
    rw [hleft _ (hsum _ subset_rfl) _ subset_rfl]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hright _ (hmem a ha) _ subset_rfl, Finset.mul_sum,
      Finset.sum_eq_single a, hdiag a ha, mul_assoc]
    · intro b hb hba
      have h0 : l2Inner (N := N) n (monomial a (1 : ℂ)) (monomial b 1) = 0 := by
        rw [← hdeg a ha]
        exact hO N a b (Ne.symm hba) (by rw [hdeg a ha, hdeg b hb])
      rw [h0, mul_zero, mul_zero]
    · intro ha'; exact absurd ha ha'
  rw [fubiniStudy_l2Norm_sq_eq]
  apply Complex.ofReal_injective
  rw [← hI N n P, key]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.conj_mul']

end FSInv

end

end GroundTheory.Heights₂.Heights
