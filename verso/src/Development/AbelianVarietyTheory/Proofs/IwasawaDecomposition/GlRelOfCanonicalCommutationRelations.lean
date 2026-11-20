import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel

open Matrix GlobalTheory.Mem.Lift

namespace GlobalTheory.Mem.Lift

/- English proof (translation)
Take `⟨hx, hd, hc⟩` from `h`. Establish `e1 : x k * d l * (x k' * d l') = x k * (d l * x k' - x k' * d l) * d l' + x k * x k' * (d l * d l')` using `by noncomm_ring`. Establish `e2 : x k' * d l' * (x k * d l) = x k' * (d l' * x k - x k * d l') * d l + x k' * x k * (d l' * d l)` using `by noncomm_ring`. Rewrite using `[e1, e2, hc, hc, hx k' k, hd l' l]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem IsCCR.comm_monomial {A : Type} [Ring A] {κ : Type} [DecidableEq κ] {x d : κ → A} (h : IsCCR x d)
    (k l k' l' : κ) : x k * d l * (x k' * d l') - x k' * d l' * (x k * d l) =
      (if k' = l then x k * d l' else 0) - (if k = l' then x k' * d l else 0) := by
  obtain ⟨hx, hd, hc⟩ := h
  have e1 : x k * d l * (x k' * d l') = x k * (d l * x k' - x k' * d l) * d l' + x k * x k' * (d l * d l') := by
    noncomm_ring
  have e2 : x k' * d l' * (x k * d l) = x k' * (d l' * x k - x k * d l') * d l + x k' * x k * (d l' * d l) := by
    noncomm_ring
  rw [e1, e2, hc, hc, hx k' k, hd l' l]
  split_ifs <;> simp

/- English proof (translation)
Use `⟨fun i j k l => ?_, fun a b c e => ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (f := fun s t => x (k, s) * d (l, s) * (x (i, t) * d (j, t))), ← Finset.sum_sub_distrib]`. Repeatedly rewrite using `[← Finset.sum_sub_distrib, h.comm_monomial, Finset.sum_sub_distrib, Prod.mk.injEq]`. Use `congr 1`.

Distinguish the cases in `hjk : j = k`. Simplify using `[hjk]`. Simplify using `[hjk, Ne.symm hjk]`. Distinguish the cases in `hli : l = i`. Simplify using `[hli]`.

Simplify using `[hli, Ne.symm hli]`. Use `beta_reduce`. Rewrite using `[neg_mul_neg, neg_mul_neg, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (f := fun s t => x (s, e) * d (s, c) * (x (t, b) * d (t, a))), ← Finset.sum_sub_distrib]`. Repeatedly rewrite using `[← Finset.sum_sub_distrib, h.comm_monomial, Finset.sum_sub_distrib, Prod.mk.injEq]`. Apply the tactic sequence `by_cases hbc : b = c <;> by_cases hea : e = a <;> simp [hbc, hea, sub_eq_neg_add, add_comm]`.
-/
theorem glRel_of_isCCR (A : Type) [Ring A] (n m : ℕ) (x d : Fin n × Fin m → A) (h : IsCCR x d) :
    Formalism.REAL.GlRel (fun i j : Fin n => ∑ a, x (i, a) * d (j, a)) ∧
      Formalism.REAL.GlRel (fun a b : Fin m => -∑ i, x (i, b) * d (i, a)) := by
  refine ⟨fun i j k l => ?_, fun a b c e => ?_⟩
  · beta_reduce
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (f := fun s t => x (k, s) * d (l, s) * (x (i, t) * d (j, t))),
      ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, h.comm_monomial, Finset.sum_sub_distrib, Prod.mk.injEq]
    congr 1
    · by_cases hjk : j = k
      · simp [hjk]
      · simp [hjk, Ne.symm hjk]
    · by_cases hli : l = i
      · simp [hli]
      · simp [hli, Ne.symm hli]
  · beta_reduce
    rw [neg_mul_neg, neg_mul_neg, Finset.sum_mul_sum, Finset.sum_mul_sum,
      Finset.sum_comm (f := fun s t => x (s, e) * d (s, c) * (x (t, b) * d (t, a))), ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, h.comm_monomial, Finset.sum_sub_distrib, Prod.mk.injEq]
    by_cases hbc : b = c <;> by_cases hea : e = a <;> simp [hbc, hea, sub_eq_neg_add, add_comm]

end GlobalTheory.Mem.Lift
