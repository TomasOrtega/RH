import Formalism.PeriodIntegrals.BordSlice
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Matrix

noncomputable section

namespace PI.HermitianEmbeddingSlice

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic

variable {k r : ℕ}

def emb (k r : ℕ) (y : Fin (k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := fun i =>
  if h : r ≤ i.val ∧ i.val ≤ r + k then y ⟨i.val - r, by omega⟩ else 0

def dd (k : ℕ) (j : Fin (k + 1)) : ℂ := if j = Fin.last k then -1 else 1

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma Hb_eq : Hb k = diagonal (dd k) := rfl

/- English proof (translation)
Unfold `dd`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
lemma dd_sq (j : Fin (k + 1)) : dd k j * dd k j = 1 := by
  unfold dd
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `dd`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma dd_star (j : Fin (k + 1)) : star (dd k j) = dd k j := by
  unfold dd
  split_ifs <;> simp

end PI.HermitianEmbeddingSlice
