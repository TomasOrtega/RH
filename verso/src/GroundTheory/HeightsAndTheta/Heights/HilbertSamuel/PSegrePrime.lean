import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegrePrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} (F : Type) [Field F]

/- English proof (translation)
Unfold `IsMultiHomog`. Rewrite using `[segreMap, aeval_monomial, algebraMap_eq, Finsupp.prod]`. Use `IsWeightedHomogeneous.C_mul ?_ a` and prove the remaining obligations. Establish `hX : ∀ v : (_ : Unit) × ((k : K) → ι k), IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, v.2 k⟩ : MRing ι F)) (fun _ => 1)`. Introduce `v`.

Use `IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ (fun k => (X ⟨k, v.2 k⟩ : MRing ι F)) (fun k => Pi.single k 1) (fun k _ => isWeightedHomogeneous_X F _ _)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `IsWeightedHomogeneous.prod d.support (fun v => (∏ k, (X ⟨k, v.2 k⟩ : MRing ι F)) ^ d v) (fun v => d v • (fun _ : K => (1 : ℕ))) (fun v _ => (hX v).pow _)` as an intermediate fact.

Establish `e : (fun _ : K => Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d ()) = ∑ v ∈ d.support, d v • (fun _ : K => (1 : ℕ))`. Use extensionality with `j`. Simplify using `[Finsupp.weight_apply, Finsupp.sum, blockWeight, Finset.sum_apply]`. Rewrite using `[e]`. Conclude with `this`.
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
Proceed by induction on `g using MvPolynomial.induction_on' with`. Consider the case `monomial d a`. Establish `h1` using `isWeightedHomogeneous_monomial (blockWeight (fun _ : Unit => ∀ k, ι k)) d a rfl`. Rewrite using `[weightedHomogeneousComponent_of_mem h1, weightedHomogeneousComponent_of_mem (segreMap_monomial_isMultiHomog F d a)]`. Establish `key : b = Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d ↔ (fun _ : K => b ()) = fun _ => Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d ()`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Both sides reduce to the same expression. Introduce `h`. Use function extensionality and compare the values at `u`.

Consider the cases of `u`. Conclude with `congr_fun h (Classical.arbitrary K)`. Distinguish the cases in `h : b = Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d`. Rewrite using `[if_pos h, if_pos (key.mp h)]`. Rewrite using `[if_neg h, if_neg (mt key.mpr h), map_zero]`.

Consider the case `add p p' hp hp' => simp only [map_add, hp, hp']`.
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
Introduce `F _ K _ _ _ ι _ q hq`. Use `hq.isPrime` as an intermediate fact. Use `⟨segrePrime.isPrime F q, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg b`. Rewrite `hg`, the goal using `[segrePrime, Ideal.mem_comap]`.

Rewrite using `[segreMap_weightedHomogeneousComponent]`. Conclude with `hq.multiHomog _ hg _`. Introduce `u`. Consider the cases of `u`. Use `choose i hi using hq.relevant`.

Use `⟨i, ?_⟩` and prove the remaining obligations. Rewrite using `[segrePrime, Ideal.mem_comap, segreMap_X, Ideal.IsPrime.prod_mem_iff]`. Introduce and unpack `⟨k, _, hk⟩`. Conclude with `hi k hk`.
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
