import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHat

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

/- English proof (translation)
Introduce `P`. Take `⟨Mb, hMb⟩ : ∃ Mb : ℝ, Mb = 1 + ∑ π : M.Ty P, ∑ i ∈ Finset.Icc 1 (P.k - 1), |M.rho P π i|` from `⟨_, rfl⟩`. Use `⟨fun j => Mb + ((j : ℕ) : ℝ), fun a b h => ?_, fun j π => ?_⟩` and prove the remaining obligations. Simplify using `only at h`. Establish `h' : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ)` using `add_left_cancel h`.

Conclude with `Fin.ext (by exact_mod_cast h')`. Unfold `M.xC`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `i hi`. Establish `hle : |M.rho P π i| ≤ ∑ π' : M.Ty P, ∑ i' ∈ Finset.Icc 1 (P.k - 1), |M.rho P π' i'|`.

Combine the equalities or inequalities in the displayed calculation. Establish `hpos : 0 < Mb + ((j : ℕ) : ℝ) + M.rho P π i`. Establish `h1` using `neg_abs_le (M.rho P π i)`. Establish `hj : (0 : ℝ) ≤ ((j : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hc : (((Mb + ((j : ℕ) : ℝ) : ℝ) : ℂ) + ((M.rho P π i : ℝ) : ℂ)) = ((Mb + ((j : ℕ) : ℝ) + M.rho P π i : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[hc]`. Conclude with `Complex.ofReal_ne_zero.2 (ne_of_gt hpos)`.
-/
theorem hat_nodes_decay_holds : JDHatNodes := by
  intro P
  classical
  obtain ⟨Mb, hMb⟩ : ∃ Mb : ℝ, Mb = 1 + ∑ π : M.Ty P, ∑ i ∈ Finset.Icc 1 (P.k - 1), |M.rho P π i| := ⟨_, rfl⟩
  refine ⟨fun j => Mb + ((j : ℕ) : ℝ), fun a b h => ?_, fun j π => ?_⟩
  · dsimp only at h
    have h' : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) := add_left_cancel h
    exact Fin.ext (by exact_mod_cast h')
  · unfold M.xC
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    have hle : |M.rho P π i| ≤ ∑ π' : M.Ty P, ∑ i' ∈ Finset.Icc 1 (P.k - 1), |M.rho P π' i'| := by
      calc |M.rho P π i| ≤ ∑ i' ∈ Finset.Icc 1 (P.k - 1), |M.rho P π i'| :=
            Finset.single_le_sum (f := fun i' => |M.rho P π i'|) (fun _ _ => abs_nonneg _) hi
        _ ≤ _ := Finset.single_le_sum (f := fun π' => ∑ i' ∈ Finset.Icc 1 (P.k - 1), |M.rho P π' i'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ π)
    have hpos : 0 < Mb + ((j : ℕ) : ℝ) + M.rho P π i := by
      have h1 := neg_abs_le (M.rho P π i)
      have hj : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hc : (((Mb + ((j : ℕ) : ℝ) : ℝ) : ℂ) + ((M.rho P π i : ℝ) : ℂ)) =
        ((Mb + ((j : ℕ) : ℝ) + M.rho P π i : ℝ) : ℂ) := by push_cast; ring
    rw [hc]
    exact Complex.ofReal_ne_zero.2 (ne_of_gt hpos)

end

end Formalism.FourierDecayAlt.P.CutMP
