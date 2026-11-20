import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardSubspacesContainingRangeQVandermondeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralIndicatorCosetsSubspacesContainingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralIndicatorCosetsKernelSubspacesStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

/- English proof (translation)
Introduce `k _ _ _ _ D D' _ _ _ _ ϖ hϖ t ht s RK hRK sn Rn hRn y`. Establish `hL` using `GlobalTheory.T.sum_integralIndicator_cosets_subspaces_containing k D D' ϖ hϖ s RK hRK y`. Distinguish the cases in `hy : ∀ i j, y i j ∈ 𝒪[k]`. Set `y₀ : Matrix D' D 𝒪[k]` to `fun i j => ⟨y i j, hy i j⟩`. Establish `hy₀ : y = y₀.map (algebraMap 𝒪[k] k)`.

Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[hL.2 y₀ hy₀]`. Establish `hR : ∀ n ∈ Finset.range (Fintype.card D + 1), ∑ g ∈ Rn n, intInd (y * g.1) = (Nat.card {U : Submodule 𝓀[k] (D → 𝓀[k]) // U ≤ LinearMap.ker (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ∧ Module.finrank 𝓀[k] U = n} : ℂ)`. Introduce `n hn`.

Establish `hn' : n ≤ Fintype.card D` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)`. Take `⟨hc, hr⟩` from `hRn n hn'`. Rewrite using `[(GlobalTheory.T.sum_integralIndicator_cosets_kernel_subspaces k D D' ϖ hϖ (sn n) (Rn n) hr y).2 y₀ hy₀, hc]`. Rewrite using `[Finset.sum_congr rfl (fun n hn => by rw [hR n hn])]`. Establish `hC` using `GlobalTheory.T.card_subspaces_containing_range_qVandermonde 𝓀[k] (D → 𝓀[k]) (D' → 𝓀[k]) (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin t s.card (by simp only [Module.finrank_fintype_fun_eq_card]; exact ht) (by simp only [Module.finrank_fintype_fun_eq_card]; exact Finset.card_le_un …`.

Simplify using `only [Module.finrank_fintype_fun_eq_card] at hC`. Rewrite using `[hC]`. Use `push_cast`. Use `Finset.sum_congr rfl (fun n _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [resCard]`.

Rewrite using `[hL.1 hy]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `n hn`. Establish `hn' : n ≤ Fintype.card D` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)`.

Rewrite using `[(GlobalTheory.T.sum_integralIndicator_cosets_kernel_subspaces k D D' ϖ hϖ (sn n) (Rn n) (hRn n hn').2 y).1 hy, mul_zero]`.
-/
theorem GlobalTheory.ParHecke.heckeIdentity_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D D' : Type) [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ t : ℕ, Fintype.card D' = Fintype.card D + t → ∀ (s : Finset D') RK, IsRepsK (torusElt k D' ϖ (indic s)) RK → ∀ (sn : ℕ → Finset D) (Rn : ℕ → Finset (GL D k)), (∀ n ≤ Fintype.card D, (sn n).card = n ∧ IsRepsK (torusElt k D ϖ (-indic (sn n))) (Rn n)) → ∀ y : Matrix D' D k, ∑ g ∈ RK, intInd ((g⁻¹).1 * y) = ∑ n ∈ Finset.range (Fintype.card D + 1), (if n ≤ s.card then ((resCard k ^ (n * (t - (s.card - n))) * Formalism.L2.Col.gaussBin (resCard k) t (s.card - n) : ℕ) : ℂ) else 0) * ∑ g ∈ Rn n, intInd (y * g.1) := by
  intro k _ _ _ _ D D' _ _ _ _ ϖ hϖ t ht s RK hRK sn Rn hRn y
  have hL := GlobalTheory.T.sum_integralIndicator_cosets_subspaces_containing k D D' ϖ hϖ s RK hRK y
  by_cases hy : ∀ i j, y i j ∈ 𝒪[k]
  · let y₀ : Matrix D' D 𝒪[k] := fun i j => ⟨y i j, hy i j⟩
    have hy₀ : y = y₀.map (algebraMap 𝒪[k] k) := by
      ext i j; rfl
    rw [hL.2 y₀ hy₀]
    have hR : ∀ n ∈ Finset.range (Fintype.card D + 1), ∑ g ∈ Rn n, intInd (y * g.1) =
        (Nat.card {U : Submodule 𝓀[k] (D → 𝓀[k]) // U ≤ LinearMap.ker (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ∧ Module.finrank 𝓀[k] U = n} : ℂ) := by
      intro n hn
      have hn' : n ≤ Fintype.card D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      obtain ⟨hc, hr⟩ := hRn n hn'
      rw [(GlobalTheory.T.sum_integralIndicator_cosets_kernel_subspaces k D D' ϖ hϖ (sn n) (Rn n) hr y).2 y₀ hy₀, hc]
    rw [Finset.sum_congr rfl (fun n hn => by rw [hR n hn])]
    have hC := GlobalTheory.T.card_subspaces_containing_range_qVandermonde 𝓀[k] (D → 𝓀[k]) (D' → 𝓀[k]) (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin t s.card
      (by simp only [Module.finrank_fintype_fun_eq_card]; exact ht)
      (by simp only [Module.finrank_fintype_fun_eq_card]; exact Finset.card_le_univ s)
    simp only [Module.finrank_fintype_fun_eq_card] at hC
    rw [hC]
    push_cast
    refine Finset.sum_congr rfl (fun n _ => ?_)
    split_ifs <;> simp [resCard]
  · rw [hL.1 hy]
    symm
    apply Finset.sum_eq_zero
    intro n hn
    have hn' : n ≤ Fintype.card D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rw [(GlobalTheory.T.sum_integralIndicator_cosets_kernel_subspaces k D D' ϖ hϖ (sn n) (Rn n) (hRn n hn').2 y).1 hy, mul_zero]
