import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply
open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff

set_option autoImplicit false

namespace GlobalTheory.ExtOne

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem wedge_single_of_lt {m : ℕ} (i : Fin m) (T : Finset (Fin m)) (hT : ∀ t ∈ T, i < t) :
    wedge i (Pi.single T (1 : ℂ)) = Pi.single (insert i T) 1 := by
  have hiT : i ∉ T := fun h => lt_irrefl i (hT i h)
  funext S
  by_cases hS : S = insert i T
  · subst hS
    have hf : (insert i T).filter (· < i) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.notMem_empty, iff_false, not_and]
      rintro (rfl | hx)
      · exact lt_irrefl x
      · exact fun h => lt_asymm h (hT x hx)
    simp [wedge, sgn, hf, Finset.erase_insert hiT]
  · rw [Pi.single_apply, if_neg hS]
    by_cases hi : i ∈ S
    · have hne : S.erase i ≠ T := by
        intro h; apply hS; rw [← h, Finset.insert_erase hi]
      simp [wedge, hi, Pi.single_apply, hne]
    · simp [wedge, hi]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sum_one_smul_wedge {m : ℕ} (i : Fin m) (x : Ext m) :
    ∑ k, (1 : Matrix (Fin m) (Fin m) ℂ) i k • wedge k x = wedge i x := by
  simp [Matrix.one_apply, ite_smul]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem genProd_one {m : ℕ} (S : Finset (Fin m)) :
    genProd (1 : Matrix (Fin m) (Fin m) ℂ) S = Pi.single S 1 := by
  induction S using Finset.induction_on_min with
  | empty => simp [genProd]
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hsort : (insert a s).sort (· ≤ ·) = a :: s.sort (· ≤ ·) :=
      Finset.sort_insert _ (fun b hb => (ha b hb).le) has
    have ih' : genProd (1 : Matrix (Fin m) (Fin m) ℂ) s = Pi.single s 1 := ih
    unfold genProd at ih' ⊢
    rw [hsort, List.foldr_cons, ih', sum_one_smul_wedge, wedge_single_of_lt a s ha]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem extMap_one : ∀ {m : ℕ}, extMap (1 : Matrix (Fin m) (Fin m) ℂ) = ContinuousLinearMap.id ℂ (Ext m) := by
  intro m
  ext1 w
  rw [extMap_apply, ContinuousLinearMap.id_apply]
  funext T
  simp [genProd_one, Finset.sum_apply, Pi.single_apply]

end GlobalTheory.ExtOne
