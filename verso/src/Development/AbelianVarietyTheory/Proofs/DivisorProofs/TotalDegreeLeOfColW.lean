import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
open NumberField IsDedekindDomain GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

open MvPolynomial

namespace GlobalTheory.NablaFin

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem totalDegree_le_of_colW {O : Type} [CommRing O] (N : ℕ) (ν : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ weightedHomogeneousSubmodule O (Formalism.GradedWeylDivisibility.colW N N) ν) :
    f.totalDegree ≤ ∑ t, ν t := by
  rw [mem_weightedHomogeneousSubmodule] at hf
  unfold totalDegree
  refine Finset.sup_le fun s hs => ?_
  have hw := hf (mem_support_iff.1 hs)
  rw [← hw, Finsupp.weight_apply]
  refine le_of_eq ?_
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dualWeyl_finite (O : Type) [CommRing O] [IsNoetherianRing O] (N : ℕ) (ν : Fin N → ℕ) :
    Module.Finite O (Formalism.GradedWeylDivisibility.dualWeyl O N N ν) := by
  have hle : Formalism.GradedWeylDivisibility.dualWeyl O N N ν ≤ restrictTotalDegree (Fin N × Fin N) O (∑ t, ν t) := by
    intro f hf
    rw [mem_restrictTotalDegree]
    exact totalDegree_le_of_colW N ν f (by unfold Formalism.GradedWeylDivisibility.dualWeyl at hf; exact hf.1)
  haveI : IsNoetherian O (Formalism.GradedWeylDivisibility.dualWeyl O N N ν) := isNoetherian_of_le hle
  infer_instance

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem nablaT_finite : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (N : ℕ) (ι : Type) [Fintype ι]
    (lam : ι → ℕ → ℕ), Module.Finite O (NablaT O N lam) := by
  intro O _ _ N ι _ lam
  haveI : ∀ τ, Module.Finite O (Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ))) := fun τ => dualWeyl_finite O N _
  exact PiTensorProduct.finite

end GlobalTheory.NablaFin
