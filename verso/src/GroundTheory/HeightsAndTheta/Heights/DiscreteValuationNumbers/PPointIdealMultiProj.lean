import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPointIdealMultiProj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace PointIdealMultiProj

variable {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L]
  {K : Type*} [DecidableEq K] {ι : K → Type*}

def coneWeight (K : Type*) [DecidableEq K] : K → K → ℕ := fun k => Pi.single k 1

/- English proof (translation)
Rewrite using `[pointConeMap, aeval_monomial, MvPolynomial.algebraMap_apply, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum]`. Use `IsWeightedHomogeneous.C_mul ?_ _` and prove the remaining obligations. Use `IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_` and prove the remaining obligations. Conclude with `((isWeightedHomogeneous_X (R := L) (coneWeight K) p.1).C_mul (z p)).pow (d p)`.
-/
theorem coneMap_monomial_isWeightedHomogeneous (z : (Σ k, ι k) → L) (d : (Σ k, ι k) →₀ ℕ) (a : F) :
    IsWeightedHomogeneous (coneWeight K) (pointConeMap F z (monomial d a))
      (Finsupp.weight (blockWeight ι) d) := by
  rw [pointConeMap, aeval_monomial, MvPolynomial.algebraMap_apply, Finsupp.weight_apply, Finsupp.prod,
    Finsupp.sum]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_
  exact ((isWeightedHomogeneous_X (R := L) (coneWeight K) p.1).C_mul (z p)).pow (d p)

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial d a`. Establish `h1` using `coneMap_monomial_isWeightedHomogeneous (K := K) (F := F) z d a`. Establish `h2 : IsWeightedHomogeneous (blockWeight ι) (monomial d a : MRing ι F) (Finsupp.weight (blockWeight ι) d)` using `isWeightedHomogeneous_monomial _ _ _ rfl`. Distinguish the cases in `h : b = Finsupp.weight (blockWeight ι) d`.

Substitute `h` using the available equality. Rewrite using `[h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_same]`. Rewrite using `[h1.weightedHomogeneousComponent_ne _ h, h2.weightedHomogeneousComponent_ne _ h, map_zero]`. Consider the case `add f g hf hg => simp only [map_add, hf, hg]`.
-/
theorem coneMap_component (z : (Σ k, ι k) → L) (b : K → ℕ) (f : MRing ι F) :
    weightedHomogeneousComponent (coneWeight K) b (pointConeMap F z f) =
      pointConeMap F z (weightedHomogeneousComponent (blockWeight ι) b f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d a =>
    have h1 := coneMap_monomial_isWeightedHomogeneous (K := K) (F := F) z d a
    have h2 : IsWeightedHomogeneous (blockWeight ι) (monomial d a : MRing ι F)
        (Finsupp.weight (blockWeight ι) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases h : b = Finsupp.weight (blockWeight ι) d
    · subst h
      rw [h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_same]
    · rw [h1.weightedHomogeneousComponent_ne _ h, h2.weightedHomogeneousComponent_ne _ h, map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]

/- English proof (translation)
Introduce `F _ L _ _ K _ ι z hz`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `RingHom.ker_isPrime _`. Introduce `f hf b`. Rewrite `hf`, the goal using `[pointIdeal, RingHom.mem_ker]`.

Use `coneMap_component (F := F) z b f` as an intermediate fact. Rewrite `this` using `[show (pointConeMap F z) f = 0 from hf, map_zero]`. Conclude with `this.symm`. Introduce `k`. Take `⟨i, hi⟩` from `hz k`.

Use `⟨i, ?_⟩` and prove the remaining obligations. Rewrite using `[pointIdeal, RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `pointConeMap F z (X ⟨k, i⟩) ≠ 0`. Rewrite using `[pointConeMap, aeval_X]`. Conclude with `mul_ne_zero (by simpa using hi) (X_ne_zero _)`.
-/
theorem proof : PointIdealMultiProj.Statement := by
  intro F _ L _ _ K _ ι z hz
  refine ⟨?_, ?_, ?_⟩
  · exact RingHom.ker_isPrime _
  · intro f hf b
    rw [pointIdeal, RingHom.mem_ker] at hf ⊢
    have := coneMap_component (F := F) z b f
    rw [show (pointConeMap F z) f = 0 from hf, map_zero] at this
    exact this.symm
  · intro k
    obtain ⟨i, hi⟩ := hz k
    refine ⟨i, ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    change pointConeMap F z (X ⟨k, i⟩) ≠ 0
    rw [pointConeMap, aeval_X]
    exact mul_ne_zero (by simpa using hi) (X_ne_zero _)

end PointIdealMultiProj

end

end GroundTheory.Heights₂.Heights.NumbersDVR
