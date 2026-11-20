import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegrePrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} (F : Type) [Field F]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem segreMap_monomial_isMultiHomog (d : ((_ : Unit) × ((k : K) → ι k)) →₀ ℕ) (a : F) :
    IsMultiHomog (segreMap F (monomial d a))
      (fun _ => Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d ()) := by
  unfold IsMultiHomog
  rw [segreMap, aeval_monomial, algebraMap_eq, Finsupp.prod]
  refine IsWeightedHomogeneous.C_mul ?_ a
  have hX : ∀ v : (_ : Unit) × ((k : K) → ι k),
      IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, v.2 k⟩ : MRing ι F)) (fun _ => 1) := by
    intro v
    have := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
      (fun k => (X ⟨k, v.2 k⟩ : MRing ι F)) (fun k => Pi.single k 1)
      (fun k _ => isWeightedHomogeneous_X F _ _)
    convert this using 1
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have := IsWeightedHomogeneous.prod d.support
    (fun v => (∏ k, (X ⟨k, v.2 k⟩ : MRing ι F)) ^ d v) (fun v => d v • (fun _ : K => (1 : ℕ)))
    (fun v _ => (hX v).pow _)
  have e : (fun _ : K => Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d ()) =
      ∑ v ∈ d.support, d v • (fun _ : K => (1 : ℕ)) := by
    ext j
    simp [Finsupp.weight_apply, Finsupp.sum, blockWeight, Finset.sum_apply]
  rw [e]
  exact this

/- English proof (translation)
Proceed by induction. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument.

Split into cases according to the possible forms of the given data. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately.

A detailed English derivation is pending.
-/
theorem segreMap_weightedHomogeneousComponent [Nonempty K] (b : Unit → ℕ)
    (g : MRing (fun _ : Unit => ∀ k, ι k) F) :
    segreMap F (weightedHomogeneousComponent (blockWeight (fun _ : Unit => ∀ k, ι k)) b g) =
      weightedHomogeneousComponent (blockWeight ι) (fun _ => b ()) (segreMap F g) := by
  classical
  induction g using MvPolynomial.induction_on' with
  | monomial d a =>
    have h1 := isWeightedHomogeneous_monomial (blockWeight (fun _ : Unit => ∀ k, ι k)) d a rfl
    rw [weightedHomogeneousComponent_of_mem h1,
      weightedHomogeneousComponent_of_mem (segreMap_monomial_isMultiHomog F d a)]
    have key : b = Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d ↔
        (fun _ : K => b ()) = fun _ => Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d () := by
      constructor
      · rintro rfl; rfl
      · intro h; funext u; cases u; exact congr_fun h (Classical.arbitrary K)
    by_cases h : b = Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d
    · rw [if_pos h, if_pos (key.mp h)]
    · rw [if_neg h, if_neg (mt key.mpr h), map_zero]
  | add p p' hp hp' => simp only [map_add, hp, hp']

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem SegrePrime.proof : SegrePrime.Statement := by
  intro F _ K _ _ _ ι _ q hq
  have := hq.isPrime
  refine ⟨segrePrime.isPrime F q, ?_, ?_⟩
  · intro g hg b
    rw [segrePrime, Ideal.mem_comap] at hg ⊢
    rw [segreMap_weightedHomogeneousComponent]
    exact hq.multiHomog _ hg _
  · intro u
    cases u
    choose i hi using hq.relevant
    refine ⟨i, ?_⟩
    rw [segrePrime, Ideal.mem_comap, segreMap_X, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, _, hk⟩
    exact hi k hk

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
