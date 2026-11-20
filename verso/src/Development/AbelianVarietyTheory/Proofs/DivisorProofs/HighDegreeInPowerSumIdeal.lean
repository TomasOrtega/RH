import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialReductionModElementaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanPsumEqSpanEsymm
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory

attribute [local instance] MvPolynomial.gradedAlgebra in

/- English proof (translation)
Introduce `N d P hP hd`. Take `⟨R, hR, hPR⟩` from `GlobalTheory.T.polynomial_reduction_mod_elementary N P`. Rewrite `hPR` using `[← GlobalTheory.span_psum_eq_span_esymm N]`. Establish `hhom : (Ideal.span ((fun k => psum (Fin N) ℝ k) '' Set.Icc 1 N)).IsHomogeneous (homogeneousSubmodule (Fin N) ℝ)`. Use `Ideal.homogeneous_span _ _ ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, -, rfl⟩`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_homogeneousSubmodule]`. Conclude with `IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i k`. Establish `h1 : homogeneousComponent d (P - R) ∈ Ideal.span ((fun k => psum (Fin N) ℝ k) '' Set.Icc 1 N)` using `homogeneousComponent_mem_of_mem hhom hPR d`.

Establish `h2 : homogeneousComponent d R = 0` using `by clear hPR h1`. Proceed by induction on `hR using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨m, hm, rfl⟩` from `hx`. Establish `hdeg : m.degree ≤ N * (N - 1) / 2`.

Rewrite using `[Finsupp.degree_eq_sum, ← Finset.sum_range_id, ← Fin.sum_univ_eq_sum_range (fun i => i) N]`. Conclude with `Finset.sum_le_sum fun i _ => hm i`. Establish `hx : (monomial m (1 : ℝ)).IsHomogeneous m.degree` using `isHomogeneous_monomial _ rfl`. Rewrite using `[homogeneousComponent_of_mem hx, if_neg (by omega)]`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]`. Consider the case `smul a x _ hx => rw [map_smul, hx, smul_zero]`. Rewrite `h1` using `[map_sub, h2, sub_zero, homogeneousComponent_of_mem hP, if_pos rfl]`. Conclude with `h1`.
-/
theorem coinvariant_vanish_above_top_degree :
    ∀ (N d : ℕ) (P : MvPolynomial (Fin N) ℝ), P.IsHomogeneous d → N * (N - 1) / 2 < d →
      P ∈ Ideal.span ((fun k => psum (Fin N) ℝ k) '' Set.Icc 1 N) := by
  intro N d P hP hd
  obtain ⟨R, hR, hPR⟩ := GlobalTheory.T.polynomial_reduction_mod_elementary N P
  rw [← GlobalTheory.span_psum_eq_span_esymm N] at hPR
  have hhom : (Ideal.span ((fun k => psum (Fin N) ℝ k) '' Set.Icc 1 N)).IsHomogeneous
      (homogeneousSubmodule (Fin N) ℝ) := by
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨k, -, rfl⟩
    refine ⟨k, ?_⟩
    rw [mem_homogeneousSubmodule]
    exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i k
  have h1 : homogeneousComponent d (P - R) ∈
      Ideal.span ((fun k => psum (Fin N) ℝ k) '' Set.Icc 1 N) :=
    homogeneousComponent_mem_of_mem hhom hPR d
  have h2 : homogeneousComponent d R = 0 := by
    clear hPR h1
    induction hR using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm, rfl⟩ := hx
      have hdeg : m.degree ≤ N * (N - 1) / 2 := by
        rw [Finsupp.degree_eq_sum, ← Finset.sum_range_id, ← Fin.sum_univ_eq_sum_range (fun i => i) N]
        exact Finset.sum_le_sum fun i _ => hm i
      have hx : (monomial m (1 : ℝ)).IsHomogeneous m.degree := isHomogeneous_monomial _ rfl
      rw [homogeneousComponent_of_mem hx, if_neg (by omega)]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul a x _ hx => rw [map_smul, hx, smul_zero]
  rw [map_sub, h2, sub_zero, homogeneousComponent_of_mem hP, if_pos rfl] at h1
  exact h1

end GlobalTheory
