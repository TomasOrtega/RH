import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeBadFiniteSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

/- English proof (translation)
Introduce `K _ ι _ e`. Use `(Set.Finite.pi (t := fun p : (Σ k, ι k) => Set.Icc (-|e p.1|) |e p.1|) (fun p => Set.finite_Icc _ _)).subset ?_` and prove the remaining obligations. Introduce and unpack `a ⟨hsum, hneg⟩ ⟨k, i⟩ -`. Use `show a ⟨k, i⟩ ∈ Set.Icc (-|e k|) |e k|`. Rewrite using `[Set.mem_Icc, ← abs_le]`.

Establish `hs : ∑ j, a ⟨k, j⟩ = e k` using `congrFun hsum k`. Break down `hneg k with h | h` into its components or cases. Establish `hnn : ∀ j, 0 ≤ a ⟨k, j⟩`. Introduce `j`. Assume the negation of the conclusion as `hj`.

Establish `hj2 : a ⟨k, j⟩ < 0` using `lt_of_not_ge hj`. Establish `hj' : j ∈ negSet a k` using `by simp [negSet, hj2]`. Rewrite `hj'` using `[h]`. Simplify using `at hj'`. Establish `h1 : a ⟨k, i⟩ ≤ ∑ j, a ⟨k, j⟩` using `Finset.single_le_sum (f := fun j => a ⟨k, j⟩) (fun j _ => hnn j) (Finset.mem_univ i)`.

Rewrite using `[abs_of_nonneg (hnn i)]`. Combine the linear relations using `[le_abs_self (e k)]`. Establish `hng : ∀ j, a ⟨k, j⟩ < 0`. Introduce `j`. Establish `hj : j ∈ negSet a k` using `by rw [h]; exact Finset.mem_univ j`.

Simplify `hj` using `[negSet]`. Establish `h1 : -a ⟨k, i⟩ ≤ ∑ j, -a ⟨k, j⟩` using `Finset.single_le_sum (f := fun j => -a ⟨k, j⟩) (fun j _ => by linarith [hng j]) (Finset.mem_univ i)`. Rewrite `h1` using `[Finset.sum_neg_distrib]`. Rewrite using `[abs_of_neg (hng i)]`. Combine the linear relations using `[neg_abs_le (e k)]`.
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
