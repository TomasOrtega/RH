import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.PoinLen

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨i, -, rfl⟩` from `Finset.mem_map.1 h`. Simplify using the standard rewrite rules. Introduce `h`.

Conclude with `Finset.mem_map.2 ⟨⟨k.val, h⟩, Finset.mem_univ _, Fin.ext (by simp)⟩`.
-/
theorem mem_castLE_iff {n a : ℕ} (ha : a ≤ n) (k : Fin n) :
    k ∈ Finset.univ.map (Fin.castLEEmb ha) ↔ k.val < a := by
  constructor
  · intro h
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 h
    simp
  · intro h
    exact Finset.mem_map.2 ⟨⟨k.val, h⟩, Finset.mem_univ _, Fin.ext (by simp)⟩

/- English proof (translation)
Rewrite using `[GlobalTheory.HermFrame.gnorm, GlobalTheory.HermFrame.form_single, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram, diagonal_apply_eq]`. Simplify using `only [Complex.ofReal_re]`.
-/
theorem gnorm_poincareGram_single {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (k : Fin n) :
    GlobalTheory.HermFrame.gnorm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram a z) (Pi.single k 1) =
      √(if k.val < a then 1 / (2 * (‖z k‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (z k) ^ 2)) else 1 / 2) := by
  rw [GlobalTheory.HermFrame.gnorm, GlobalTheory.HermFrame.form_single, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram, diagonal_apply_eq]
  simp only [Complex.ofReal_re]

/- English proof (translation)
Rewrite using `[show (5:ℝ) = √(5 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]`. Apply `Real.sqrt_le_sqrt` to reduce the goal to its premises. Use polynomial arithmetic with `[Real.pi_lt_d2, Real.pi_pos]`.
-/
theorem sqrt_two_mul_pi_le : √(2 * Real.pi ^ 2) ≤ 5 := by
  rw [show (5:ℝ) = √(5 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_le_sqrt
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

/- English proof (translation)
Introduce `n a ha ρ hρ v hv k`. Rewrite using `[gnorm_poincareGram_single, GlobalTheory.GoodMetric.poinWt]`. Distinguish the cases in `hk : k.val < a`. Rewrite using `[if_pos hk, if_pos ((mem_castLE_iff ha k).2 hk)]`. Establish `h0 : v.ofLp k ≠ 0`.

Use `hv.2 ⟨k.val, hk⟩` as an intermediate fact. Simplify `this` using `[Fin.castLE]`. Establish `h1 : ‖v.ofLp k‖ < 1` using `lt_of_lt_of_le (hv.1 k) (by linarith)`. Establish `ht` using `GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog_pos h0 h1`. Establish `hx : 0 < ‖v.ofLp k‖` using `norm_pos_iff.2 h0`.

Establish `hlog : |Real.log ‖v.ofLp k‖| = 2 * Real.pi * GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp k)`. Rewrite using `[abs_of_neg (Real.log_neg hx h1), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog]`. Clear the denominators using the available nonvanishing facts. Express the relevant statement in the definitionally equal form `√(1 / (2 * (‖v.ofLp k‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp k) ^ 2))) * (‖v.ofLp k‖ * |Real.log ‖v.ofLp k‖|) ≤ 5`. Rewrite using `[hlog]`.

Use `set x := ‖v.ofLp k‖`. Use `set t := GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp k)`. Establish `hB : 0 ≤ x * (2 * Real.pi * t)` using `by positivity`. Rewrite using `[← Real.sqrt_sq hB, ← Real.sqrt_mul (by positivity)]`. Use `sqrt_two_mul_pi_le using 2` and compare the differences between its conclusion and the goal.

Clear the denominators using the available nonvanishing facts. Rewrite using `[if_neg hk, if_neg (fun h => hk ((mem_castLE_iff ha k).1 h)), mul_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem gnorm_mul_poinWt_le_five : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 / 2 → ∀ v : ReciprocityTheory.L2DbarEstimates.V n,
    v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → ∀ k : Fin n,
    GlobalTheory.HermFrame.gnorm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram a v.ofLp) (Pi.single k 1) *
      GlobalTheory.GoodMetric.poinWt (Finset.univ.map (Fin.castLEEmb ha)) v k ≤ 5 := by
  intro n a ha ρ hρ v hv k
  rw [gnorm_poincareGram_single, GlobalTheory.GoodMetric.poinWt]
  by_cases hk : k.val < a
  · rw [if_pos hk, if_pos ((mem_castLE_iff ha k).2 hk)]
    have h0 : v.ofLp k ≠ 0 := by
      have := hv.2 ⟨k.val, hk⟩
      simpa [Fin.castLE] using this
    have h1 : ‖v.ofLp k‖ < 1 := lt_of_lt_of_le (hv.1 k) (by linarith)
    have ht := GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog_pos h0 h1
    have hx : 0 < ‖v.ofLp k‖ := norm_pos_iff.2 h0
    have hlog : |Real.log ‖v.ofLp k‖| = 2 * Real.pi * GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp k) := by
      rw [abs_of_neg (Real.log_neg hx h1), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog]
      field_simp
    change √(1 / (2 * (‖v.ofLp k‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp k) ^ 2))) *
      (‖v.ofLp k‖ * |Real.log ‖v.ofLp k‖|) ≤ 5
    rw [hlog]
    set x := ‖v.ofLp k‖
    set t := GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp k)
    have hB : 0 ≤ x * (2 * Real.pi * t) := by positivity
    rw [← Real.sqrt_sq hB, ← Real.sqrt_mul (by positivity)]
    convert sqrt_two_mul_pi_le using 2
    field_simp
  · rw [if_neg hk, if_neg (fun h => hk ((mem_castLE_iff ha k).1 h)), mul_one]
    calc √(1 / 2 : ℝ) ≤ √1 := Real.sqrt_le_sqrt (by norm_num)
      _ ≤ 5 := by rw [Real.sqrt_one]; norm_num

end GlobalTheory.PoinLen
