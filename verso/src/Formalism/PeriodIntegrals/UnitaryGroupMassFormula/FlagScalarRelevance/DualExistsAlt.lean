import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagScalarRelevance.DualExists

noncomputable section

namespace PI.FRS

open NumberField Formalism.BasicNotions Formalism.MainNotions.S

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem dualExists : DualExists := by
  intro E _ _ _ S m u hu t
  classical
  let L : S.V →ₗ[E] (Fin m → E) := LinearMap.pi (fun k => S.hT (u k))
  have hL : ∀ v k, L v k = S.hT (u k) v := fun v k => rfl
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    set lam : Fin m → E := fun k => f (fun j => if k = j then 1 else 0) with hlam
    have hfv : ∀ v : S.V, ∑ k, S.hT (u k) v * lam k = 0 := by
      intro v
      have h1 : f (L v) = 0 := hf (LinearMap.mem_range_self L v)
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      simpa [hL, smul_eq_mul, hlam] using h1
    set w : S.V := ∑ k, star (lam k) • u k with hw
    have hw0 : w = 0 := by
      refine S.nondeg.1 w (fun v => ?_)
      rw [hw, map_sum, LinearMap.sum_apply]
      rw [← hfv v]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star,
        mul_comm]
    have hlam0 : ∀ k, lam k = 0 := by
      intro k
      have := (Fintype.linearIndependent_iff.1 hu) (fun k => star (lam k)) hw0 k
      simpa using this
    apply hf0
    refine LinearMap.pi_ext (fun i x => ?_)
    have hs : (Pi.single i x : Fin m → E) = x • (fun j => if i = j then 1 else 0) := by
      ext j
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [hs, map_smul]
    have := hlam0 i
    simp only [hlam] at this
    simp [this]
  obtain ⟨v, hv⟩ := hsurj t
  exact ⟨v, fun k => by rw [← hL, hv]⟩

end PI.FRS
