import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeBadFiniteSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem KHFreeBadFinite.full : KHFreeBadFinite.Statement := by
  intro K _ ι _ e
  refine (Set.Finite.pi (t := fun p : (Σ k, ι k) => Set.Icc (-|e p.1|) |e p.1|)
    (fun p => Set.finite_Icc _ _)).subset ?_
  rintro a ⟨hsum, hneg⟩ ⟨k, i⟩ -
  show a ⟨k, i⟩ ∈ Set.Icc (-|e k|) |e k|
  rw [Set.mem_Icc, ← abs_le]
  have hs : ∑ j, a ⟨k, j⟩ = e k := congrFun hsum k
  rcases hneg k with h | h
  · have hnn : ∀ j, 0 ≤ a ⟨k, j⟩ := by
      intro j
      by_contra hj
      have hj2 : a ⟨k, j⟩ < 0 := lt_of_not_ge hj
      have hj' : j ∈ negSet a k := by simp [negSet, hj2]
      rw [h] at hj'
      simp at hj'
    have h1 : a ⟨k, i⟩ ≤ ∑ j, a ⟨k, j⟩ :=
      Finset.single_le_sum (f := fun j => a ⟨k, j⟩) (fun j _ => hnn j) (Finset.mem_univ i)
    rw [abs_of_nonneg (hnn i)]
    linarith [le_abs_self (e k)]
  · have hng : ∀ j, a ⟨k, j⟩ < 0 := by
      intro j
      have hj : j ∈ negSet a k := by rw [h]; exact Finset.mem_univ j
      simpa [negSet] using hj
    have h1 : -a ⟨k, i⟩ ≤ ∑ j, -a ⟨k, j⟩ :=
      Finset.single_le_sum (f := fun j => -a ⟨k, j⟩) (fun j _ => by linarith [hng j])
        (Finset.mem_univ i)
    rw [Finset.sum_neg_distrib] at h1
    rw [abs_of_neg (hng i)]
    linarith [neg_abs_le (e k)]

end

end GroundTheory.Heights₂.Heights.Kleiman
