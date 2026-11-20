import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.ChordSecondLogDeriv

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

section Consistency

variable {K : Type} [Field K] {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_fibre (fa : G →+ G) (wp : G → K) (al : K)
    (h : ∀ T, fa T ≠ 0 → al ^ 2 * wp (fa T) =
      wp T + ∑ P ∈ Finset.univ.filter (fun P => fa P = 0 ∧ P ≠ 0), (wp (T + P) - wp P))
    (T₀ : G) (hT₀ : fa T₀ ≠ 0) :
    ∑ T ∈ Finset.univ.filter (fun T => fa T = fa T₀), wp T =
      al ^ 2 * wp (fa T₀) + ∑ P ∈ Finset.univ.filter (fun P => fa P = 0 ∧ P ≠ 0), wp P := by
  have hsplit : ∀ f : G → K, ∑ P ∈ Finset.univ.filter (fun P => fa P = 0), f P =
      f 0 + ∑ P ∈ Finset.univ.filter (fun P => fa P = 0 ∧ P ≠ 0), f P := by
    intro f
    rw [← Finset.add_sum_erase _ _ (by simp : (0 : G) ∈ Finset.univ.filter (fun P => fa P = 0))]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext P; simp [and_comm]
  have hfib : ∑ T ∈ Finset.univ.filter (fun T => fa T = fa T₀), wp T =
      ∑ P ∈ Finset.univ.filter (fun P => fa P = 0), wp (T₀ + P) := by
    apply Finset.sum_nbij' (fun T => T - T₀) (fun P => T₀ + P)
    · intro T hT; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
      rw [map_sub, hT, sub_self]
    · intro P hP; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
      rw [map_add, hP, add_zero]
    · intro T _; simp
    · intro P _; simp
    · intro T _; simp
  have h0 := h T₀ hT₀
  rw [Finset.sum_sub_distrib] at h0
  rw [hfib, hsplit (fun P => wp (T₀ + P)), add_zero, h0]
  ring

end Consistency

section Chord

open PowerSeries

variable {K : Type} [Field K]

end Chord

end Formalism.L2.Th1.C
