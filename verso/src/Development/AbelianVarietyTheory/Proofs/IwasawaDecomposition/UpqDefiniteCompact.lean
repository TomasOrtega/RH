import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem Jpq_zero_left_eq_neg_one (q : ℕ) : Formalism.UG.Jpq 0 q = -1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · exact i.elim0
  · exact i.elim0
  · exact j.elim0
  · simp [Formalism.UG.Jpq, Matrix.one_apply]

/- English proof (translation)
Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem isCompact_Upq_zero_left (q : ℕ) :
    IsCompact (Formalism.UG.Upq 0 q : Set (GL (Fin 0 ⊕ Fin q) ℂ)) := by
  have hc := Formalism.UG.P.isCompact_units_of_unitary (n := Fin 0 ⊕ Fin q)
    (T := {M | star M * M = 1})
    (isClosed_eq (continuous_star.mul continuous_id) continuous_const) (fun _ h => h)
  convert hc using 1
  ext g
  simp only [SetLike.mem_coe, Set.mem_ofPred_eq]
  rw [Formalism.UG.P.mem_Upq_iff, Jpq_zero_left_eq_neg_one, Matrix.mul_neg, Matrix.mul_one,
    Matrix.neg_mul, neg_inj]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem compactSpace_UpqT_definite :
    ∀ N : ℕ, CompactSpace (UpqT N 0) ∧ CompactSpace (UpqT 0 N) := fun N =>
  ⟨(isCompact_iff_compactSpace.1 (Formalism.UG.P.indefinite_unitary_compact N) :
      CompactSpace (Formalism.UG.Upq N 0 : Set (GL (Fin N ⊕ Fin 0) ℂ))),
    (isCompact_iff_compactSpace.1 (isCompact_Upq_zero_left N) :
      CompactSpace (Formalism.UG.Upq 0 N : Set (GL (Fin 0 ⊕ Fin N) ℂ)))⟩

end GlobalTheory
