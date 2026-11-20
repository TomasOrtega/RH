import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo

/- English proof (translation)
Introduce `n a ha ρ hρ v hv`. Establish `hpos : ∀ i : Fin a, 0 < ‖v.ofLp (Fin.castLE ha i)‖` using `fun i => norm_pos_iff.2 (hv.2 i)`. Establish `hlt : ∀ i : Fin a, ‖v.ofLp (Fin.castLE ha i)‖ < 1 / 2` using `fun i => lt_of_lt_of_le (hv.1 (Fin.castLE ha i)) hρ`. Establish `hneg : ∀ i : Fin a, Real.log ‖v.ofLp (Fin.castLE ha i)‖ < 0` using `fun i => Real.log_neg (hpos i) (by linarith [hlt i])`. Use `⟨?_, fun h0 => ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.sum_map, Finset.sum_div]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Fin.castLEEmb_apply, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog]`. Rewrite using `[abs_of_neg (hneg i)]`. Rewrite using `[Finset.sum_map]`.

Establish `hs` using `Finset.single_le_sum (f := fun i : Fin a => |Real.log ‖v (Fin.castLEEmb ha i)‖|) (fun i _ => abs_nonneg _) (Finset.mem_univ (⟨0, h0⟩ : Fin a))`. Use `le_trans ?_ hs` and prove the remaining obligations. Establish `e : |Real.log ‖v (Fin.castLEEmb ha ⟨0, h0⟩)‖| = -Real.log ‖v.ofLp (Fin.castLE ha ⟨0, h0⟩)‖` using `abs_of_neg (hneg _)`. Simplify using `only [] at e ⊢`. Rewrite using `[e]`.

Establish `hl : Real.log ‖v.ofLp (Fin.castLE ha ⟨0, h0⟩)‖ ≤ Real.log (1 / 2)` using `Real.log_le_log (hpos _) (hlt _).le`. Establish `h2 : Real.log (1 / 2) = -Real.log 2` using `by rw [one_div, Real.log_inv]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tlog_sum_eq_and_log_two_le : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 / 2 → ∀ v : ReciprocityTheory.L2DbarEstimates.V n, v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → (∑ i : Fin a, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp (Fin.castLE ha i)) = (∑ k ∈ Finset.univ.map (Fin.castLEEmb ha), |Real.log ‖v k‖|) / (2 * Real.pi)) ∧ (0 < a → Real.log 2 ≤ ∑ k ∈ Finset.univ.map (Fin.castLEEmb ha), |Real.log ‖v k‖|) := by
  intro n a ha ρ hρ v hv
  have hpos : ∀ i : Fin a, 0 < ‖v.ofLp (Fin.castLE ha i)‖ := fun i => norm_pos_iff.2 (hv.2 i)
  have hlt : ∀ i : Fin a, ‖v.ofLp (Fin.castLE ha i)‖ < 1 / 2 := fun i =>
    lt_of_lt_of_le (hv.1 (Fin.castLE ha i)) hρ
  have hneg : ∀ i : Fin a, Real.log ‖v.ofLp (Fin.castLE ha i)‖ < 0 := fun i =>
    Real.log_neg (hpos i) (by linarith [hlt i])
  refine ⟨?_, fun h0 => ?_⟩
  · rw [Finset.sum_map, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.castLEEmb_apply, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog]
    rw [abs_of_neg (hneg i)]
  · rw [Finset.sum_map]
    have hs := Finset.single_le_sum (f := fun i : Fin a => |Real.log ‖v (Fin.castLEEmb ha i)‖|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ (⟨0, h0⟩ : Fin a))
    refine le_trans ?_ hs
    have e : |Real.log ‖v (Fin.castLEEmb ha ⟨0, h0⟩)‖| = -Real.log ‖v.ofLp (Fin.castLE ha ⟨0, h0⟩)‖ :=
      abs_of_neg (hneg _)
    simp only [] at e ⊢
    rw [e]
    have hl : Real.log ‖v.ofLp (Fin.castLE ha ⟨0, h0⟩)‖ ≤ Real.log (1 / 2) :=
      Real.log_le_log (hpos _) (hlt _).le
    have h2 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    linarith

end GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo
