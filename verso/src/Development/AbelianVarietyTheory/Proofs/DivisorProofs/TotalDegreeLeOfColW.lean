import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
open NumberField IsDedekindDomain GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

open MvPolynomial

namespace GlobalTheory.NablaFin

/- English proof (translation)
Rewrite `hf` using `[mem_weightedHomogeneousSubmodule]`. Unfold `totalDegree`. Use `Finset.sup_le fun s hs => ?_` and prove the remaining obligations. Establish `hw` using `hf (mem_support_iff.1 hs)`. Rewrite using `[← hw, Finsupp.weight_apply]`.

Use `le_of_eq ?_` and prove the remaining obligations. Simplify using `only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Simplify using `[Formalism.GradedWeylDivisibility.colW, Pi.single_apply]`.
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
Establish `hle : Formalism.GradedWeylDivisibility.dualWeyl O N N ν ≤ restrictTotalDegree (Fin N × Fin N) O (∑ t, ν t)`. Introduce `f hf`. Rewrite using `[mem_restrictTotalDegree]`. Conclude with `totalDegree_le_of_colW N ν f (by unfold Formalism.GradedWeylDivisibility.dualWeyl at hf; exact hf.1)`. Use `haveI : IsNoetherian O (Formalism.GradedWeylDivisibility.dualWeyl O N N ν) := isNoetherian_of_le hle`.

Use `infer_instance`.
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
Introduce `O _ _ N ι _ lam`. Use `haveI : ∀ τ, Module.Finite O (Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ))) := fun τ => dualWeyl_finite O N _`. Conclude with `PiTensorProduct.finite`.
-/
theorem nablaT_finite : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (N : ℕ) (ι : Type) [Fintype ι]
    (lam : ι → ℕ → ℕ), Module.Finite O (NablaT O N lam) := by
  intro O _ _ N ι _ lam
  haveI : ∀ τ, Module.Finite O (Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ))) := fun τ => dualWeyl_finite O N _
  exact PiTensorProduct.finite

end GlobalTheory.NablaFin
