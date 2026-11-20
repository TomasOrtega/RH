import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.RestPlOf

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G3

/- English proof (translation)
Unfold `multideg`. Rewrite using `[← Finset.sum_filter]`. Establish `h1 : ∑ c : Fin r, μ (y, c) = ∑ v ∈ (Finset.univ.image fun c : Fin r => (y, c)), μ v`. Rewrite using `[Finset.sum_image]`. Introduce `a _ b _ h`.

Conclude with `(Prod.mk.inj h).2`. Rewrite using `[h1]`. Apply `Finset.sum_subset` to reduce the goal to its premises. Introduce `v hv`. Rewrite `hv` using `[Finset.mem_filter]`.

Rewrite using `[Finset.mem_image]`. Conclude with `⟨v.2, Finset.mem_univ _, by rw [← hv.2]⟩`. Introduce `v hv hnot`. Rewrite `hv` using `[Finset.mem_image]`. Take `⟨c, -, rfl⟩` from `hv`.

Assume the negation of the conclusion as `h`. Conclude with `hnot (Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 h, rfl⟩)`.
-/
theorem sum_fiber_multideg {r : ℕ} (μ : ℤ × Fin r →₀ ℕ) (y : ℤ) :
    ∑ v ∈ μ.support, (if v.1 = y then μ v else 0) = multideg μ y := by
  unfold multideg
  rw [← Finset.sum_filter]
  have h1 : ∑ c : Fin r, μ (y, c) = ∑ v ∈ (Finset.univ.image fun c : Fin r => (y, c)), μ v := by
    rw [Finset.sum_image]
    intro a _ b _ h
    exact (Prod.mk.inj h).2
  rw [h1]
  apply Finset.sum_subset
  · intro v hv
    rw [Finset.mem_filter] at hv
    rw [Finset.mem_image]
    exact ⟨v.2, Finset.mem_univ _, by rw [← hv.2]⟩
  · intro v hv hnot
    rw [Finset.mem_image] at hv
    obtain ⟨c, -, rfl⟩ := hv
    by_contra h
    exact hnot (Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 h, rfl⟩)

/- English proof (translation)
Unfold `wDeg`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun v _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Take `⟨m, hm⟩` from `h`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `Nat.zero_le _`. Use `_ = ∑ m' : Fin r, ∑ v ∈ μ.support, (if v.1 = Fr.fr (jz - 1) (r - 1 - m'.val) then μ v else 0) := Finset.sum_comm`. Use `_ = ∑ m' : Fin r, multideg μ (Fr.fr (jz - 1) (r - 1 - m'.val)) := Finset.sum_congr rfl fun m' _ => sum_fiber_multideg μ _`.
-/
theorem lkW {n' r : ℕ} (Fr : Frames n' r) (jz : ℤ) (μ : ℤ × Fin r →₀ ℕ) :
    wDeg (wSet Fr jz) μ ≤ ∑ m' : Fin r, multideg μ (Fr.fr (jz - 1) (r - 1 - m'.val)) := by
  unfold wDeg
  calc ∑ v ∈ μ.support, (if v.1 ∈ wSet Fr jz then μ v else 0)
      ≤ ∑ v ∈ μ.support, ∑ m' : Fin r, (if v.1 = Fr.fr (jz - 1) (r - 1 - m'.val) then μ v else 0) := by
        refine Finset.sum_le_sum fun v _ => ?_
        split_ifs with h
        · obtain ⟨m, hm⟩ := h
          calc μ v = (if v.1 = Fr.fr (jz - 1) (r - 1 - m.val) then μ v else 0) := by rw [if_pos hm]
            _ ≤ _ := Finset.single_le_sum
              (f := fun m' : Fin r => if v.1 = Fr.fr (jz - 1) (r - 1 - m'.val) then μ v else 0)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
        · exact Nat.zero_le _
    _ = ∑ m' : Fin r, ∑ v ∈ μ.support, (if v.1 = Fr.fr (jz - 1) (r - 1 - m'.val) then μ v else 0) := Finset.sum_comm
    _ = ∑ m' : Fin r, multideg μ (Fr.fr (jz - 1) (r - 1 - m'.val)) :=
        Finset.sum_congr rfl fun m' _ => sum_fiber_multideg μ _

end Formalism.MainNotions.PairMembershipBlocks
