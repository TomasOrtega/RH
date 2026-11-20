import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin

open ArithmeticFunction.vonMangoldt (residueClass LFunctionResidueClassAux LFunctionResidueClassAux_real
  eqOn_LFunctionResidueClassAux residueClass_apply_zero continuousOn_LFunctionResidueClassAux
  abscissaOfAbsConv_residueClass_le_one) in

/- English proof (translation)
Establish `ha : IsUnit (1 : ZMod 1)` using `isUnit_one`. Establish `hres : ∀ n : ℕ, residueClass (1 : ZMod 1) n = Λ n` using `fun n => Set.indicator_of_mem (s := {n : ℕ | (n : ZMod 1) = 1}) (Subsingleton.elim (α := ZMod 1) _ _) _`. Establish `H {x : ℝ} (hx : 1 < x) : ∑' n, residueClass (1 : ZMod 1) n / (n : ℝ) ^ x = (LFunctionResidueClassAux (1 : ZMod 1) x).re + ((Nat.totient 1 : ℕ) : ℝ)⁻¹ / (x - 1)`. Use `ofReal_injective ?_` and prove the remaining obligations. Simplify using `only [ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast, ofReal_add, ofReal_inv, ofReal_sub, ofReal_one]`.

Repeatedly rewrite using `[← LFunctionResidueClassAux_real ha hx, eqOn_LFunctionResidueClassAux ha <| Set.mem_ofPred.mpr (ofReal_re x ▸ hx), sub_add_cancel, LSeries, LSeries.term]`. Use `tsum_congr fun n ↦ ?_` and prove the remaining obligations. Use `split_ifs with hn`. Simplify using `only [hn, residueClass_apply_zero, ofReal_zero, zero_div]`. Both sides reduce to the same expression.

Establish `hc : ContinuousOn (fun x : ℝ ↦ (LFunctionResidueClassAux (1 : ZMod 1) x).re) (Set.Icc 1 2)` using `continuous_re.continuousOn.comp (t := Set.univ) (continuousOn_LFunctionResidueClassAux (1 : ZMod 1)) (fun ⦃x⦄ a ↦ trivial) |>.comp continuous_ofReal.continuousOn fun x hx ↦ by`. Simplify `hx.1` using `only [Set.mem_ofPred_eq, ofReal_re]`. Take `⟨B, hB⟩` from `bddAbove_def.mp <| IsCompact.bddAbove_image isCompact_Icc hc`. Use `⟨|B| + 1, by linarith [abs_nonneg B], fun s hs hs1 => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `: Summable fun n : ℕ => residueClass (1 : ZMod 1) n / (n : ℝ) ^ (1 + s)` using `LSeries.summable_real_of_abscissaOfAbsConv_lt <| (abscissaOfAbsConv_residueClass_le_one (1 : ZMod 1)).trans_lt <| by`.

Establish `: (1 : ℝ) < 1 + s` using `by linarith`. Conclude with `this` after adjusting the coercions. Simplify `this` using `only [hres]`. Establish `h1` using `H (x := 1 + s) (by linarith)`. Establish `h2` using `hB _ (Set.mem_image_of_mem (fun x : ℝ ↦ (LFunctionResidueClassAux (1 : ZMod 1) x).re) (show 1 + s ∈ Set.Icc (1 : ℝ) 2 from ⟨by linarith, by linarith⟩))`.

Simplify using `only [hres, Nat.totient_one, Nat.cast_one, inv_one, add_sub_cancel_left] at h1`. Rewrite using `[h1, add_div]`. Establish `h3 : |B| ≤ |B| / s`. Rewrite using `[le_div_iff₀ hs]`. Conclude with `mul_le_of_le_one_right (abs_nonneg B) hs1`.

Establish `h4` using `le_abs_self B`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_tsum_vonMangoldt_div_rpow_le_div :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      Summable (fun n : ℕ => Λ n / (n : ℝ) ^ (1 + s)) ∧
        ∑' n : ℕ, Λ n / (n : ℝ) ^ (1 + s) ≤ C / s := by
  have ha : IsUnit (1 : ZMod 1) := isUnit_one
  have hres : ∀ n : ℕ, residueClass (1 : ZMod 1) n = Λ n := fun n =>
    Set.indicator_of_mem (s := {n : ℕ | (n : ZMod 1) = 1}) (Subsingleton.elim (α := ZMod 1) _ _) _
  have H {x : ℝ} (hx : 1 < x) :
      ∑' n, residueClass (1 : ZMod 1) n / (n : ℝ) ^ x =
        (LFunctionResidueClassAux (1 : ZMod 1) x).re
          + ((Nat.totient 1 : ℕ) : ℝ)⁻¹ / (x - 1) := by
    refine ofReal_injective ?_
    simp only [ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast,
      ofReal_add, ofReal_inv, ofReal_sub, ofReal_one]
    simp_rw [← LFunctionResidueClassAux_real ha hx,
      eqOn_LFunctionResidueClassAux ha <| Set.mem_ofPred.mpr (ofReal_re x ▸ hx), sub_add_cancel,
      LSeries, LSeries.term]
    refine tsum_congr fun n ↦ ?_
    split_ifs with hn
    · simp only [hn, residueClass_apply_zero, ofReal_zero, zero_div]
    · rfl
  have hc : ContinuousOn (fun x : ℝ ↦ (LFunctionResidueClassAux (1 : ZMod 1) x).re)
      (Set.Icc 1 2) :=
    continuous_re.continuousOn.comp (t := Set.univ)
      (continuousOn_LFunctionResidueClassAux (1 : ZMod 1))
      (fun ⦃x⦄ a ↦ trivial) |>.comp continuous_ofReal.continuousOn fun x hx ↦ by
        simpa only [Set.mem_ofPred_eq, ofReal_re] using hx.1
  obtain ⟨B, hB⟩ := bddAbove_def.mp <| IsCompact.bddAbove_image isCompact_Icc hc
  refine ⟨|B| + 1, by linarith [abs_nonneg B], fun s hs hs1 => ⟨?_, ?_⟩⟩
  · have : Summable fun n : ℕ => residueClass (1 : ZMod 1) n / (n : ℝ) ^ (1 + s) :=
      LSeries.summable_real_of_abscissaOfAbsConv_lt <|
        (abscissaOfAbsConv_residueClass_le_one (1 : ZMod 1)).trans_lt <| by
          have : (1 : ℝ) < 1 + s := by linarith
          exact_mod_cast this
    simpa only [hres] using this
  · have h1 := H (x := 1 + s) (by linarith)
    have h2 := hB _ (Set.mem_image_of_mem
      (fun x : ℝ ↦ (LFunctionResidueClassAux (1 : ZMod 1) x).re)
      (show 1 + s ∈ Set.Icc (1 : ℝ) 2 from ⟨by linarith, by linarith⟩))
    simp only [hres, Nat.totient_one, Nat.cast_one, inv_one, add_sub_cancel_left] at h1
    rw [h1, add_div]
    have h3 : |B| ≤ |B| / s := by
      rw [le_div_iff₀ hs]
      exact mul_le_of_le_one_right (abs_nonneg B) hs1
    have h4 := le_abs_self B
    linarith

end GlobalTheory.Lin
