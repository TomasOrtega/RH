import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm

/- English proof (translation)
Introduce `Ca Cg cb Cw cT CT C0 C' Cl D large₂ hH hK hC' hCl hCa`. Establish `hStd : Std D large₂` using `⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hK⟩`. Take `⟨_, _, hvI, hv1, hf, _, hfin, _, _, _, _, hg2, hT⟩` from `hH D large₂ hStd`. Take `⟨⟨hS0, _, _⟩, _⟩` from `hK`. Take `⟨_, h2, h3, _, h5, _, h7, _, _, _, h11, h12, _, _, _, _, _, _, _, _, _, _, h23, h24, h25⟩` from `hS0`.

Establish `hL : 1 < large₂.sc.L` using `one_lt_scale_L D large₂`. Establish `hb2 : 2 ≤ large₂.sc.b` using `two_le_scale_b D large₂`. Establish `hlb : Real.log large₂.sc.b = large₂.sc.L` using `log_scale_eq_L D large₂`. Use `⟨by rw [hfin, hf], (two_rank_add_two_eq_m D).symm, h24, by rw [hf]; exact h3, ?_, by rw [hlb]; exact h7, by rw [hf]; exact h5, hb2, by rw [hvI]; exact hv1, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hf]`.

Establish `hm : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 5 * D.R.f` using `by positivity`. Establish `: ((D.R.m ^ 5 * D.R.f : ℕ) : ℝ) ≤ D.R.k`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Conclude with `this` after adjusting the coercions.

Rewrite using `[hvI]`. Establish `hrd : 0 < D.host.rdE` using `pf_rd_pos D`. Establish `hL0 : 0 < large₂.sc.L` using `by linarith`. Establish `h1 : Real.log D.host.rdE ≤ large₂.sc.L`. Use `h11.trans ?_` and prove the remaining obligations.

Rewrite using `[div_le_iff₀ h25]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2v : 2 * D.host.v = D.host.rdE` using `by show 2 * (D.host.rdE / 2) = D.host.rdE; ring`. Rewrite using `[h2v]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hg1 : 1 ≤ D.host.g 1`. Break down `Nat.eq_zero_or_pos (D.host.g 1) with h | h` into its components or cases. Establish `: gS D = 0` using `by simp [gS, h]`. Use linear arithmetic over natural numbers and integers. Conclude with `h`.

Combine the equalities or inequalities in the displayed calculation. Introduce `u`. Use `⟨(hT u).1.one_lt.le, ?_⟩` and prove the remaining obligations. Establish `h` using `(h23 u).2`. Combine the equalities or inequalities in the displayed calculation.

Apply `Real.rpow_le_rpow_of_exponent_le (by linarith)` to reduce the goal to its premises. Establish `: (0 : ℝ) ≤ D.R.m` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem pairsPar : ∀ (Ca Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D), HostC →
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → 1 ≤ C' → 1 ≤ Cl → CT ≤ Ca →
    Module.finrank ℚ D.host.E = 2 * Formalism.HermitianLatticesTheory.fDeg D.host.E ∧ D.R.m = 2 * D.R.rS + 2 ∧ Cl ≤ (D.R.m : ℝ) ∧
    D.R.m ^ 4 ≤ Formalism.HermitianLatticesTheory.fDeg D.host.E ∧ D.R.m ^ 5 * Formalism.HermitianLatticesTheory.fDeg D.host.E ≤ D.R.k ∧
    Cl * ((D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b) ≤ D.R.k ∧ Real.log (Formalism.HermitianLatticesTheory.fDeg D.host.E : ℝ) ≤ Real.sqrt D.R.rS ∧
    2 ≤ large₂.sc.b ∧ 1 ≤ Formalism.HermitianLatticesTheory.vInv D.host.E ∧ 2 * Formalism.HermitianLatticesTheory.vInv D.host.E ≤ large₂.sc.b ∧
    ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (gS D : ℝ) ∧
    ∀ u : D.what₂.Word, 1 ≤ Tu D u ∧ (Tu D u : ℝ) ≤ large₂.sc.b ^ (Ca * (D.R.m : ℝ)) := by
  intro Ca Cg cb Cw cT CT C0 C' Cl D large₂ hH hK hC' hCl hCa
  have hStd : Std D large₂ := ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hK⟩
  obtain ⟨_, _, hvI, hv1, hf, _, hfin, _, _, _, _, hg2, hT⟩ := hH D large₂ hStd
  obtain ⟨⟨hS0, _, _⟩, _⟩ := hK
  obtain ⟨_, h2, h3, _, h5, _, h7, _, _, _, h11, h12, _, _, _, _, _, _, _, _, _, _, h23, h24, h25⟩ := hS0
  have hL : 1 < large₂.sc.L := one_lt_scale_L D large₂
  have hb2 : 2 ≤ large₂.sc.b := two_le_scale_b D large₂
  have hlb : Real.log large₂.sc.b = large₂.sc.L := log_scale_eq_L D large₂
  refine ⟨by rw [hfin, hf], (two_rank_add_two_eq_m D).symm, h24, by rw [hf]; exact h3, ?_, by rw [hlb]; exact h7,
    by rw [hf]; exact h5, hb2, by rw [hvI]; exact hv1, ?_, ?_, ?_⟩
  · rw [hf]
    have hm : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 5 * D.R.f := by positivity
    have : ((D.R.m ^ 5 * D.R.f : ℕ) : ℝ) ≤ D.R.k := by
      push_cast
      calc (D.R.m : ℝ) ^ 5 * D.R.f = 1 * ((D.R.m : ℝ) ^ 5 * D.R.f) * 1 := by ring
        _ ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f) * large₂.sc.L := by gcongr <;> linarith
        _ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring
        _ ≤ D.R.k := h2
    exact_mod_cast this
  · rw [hvI]
    have hrd : 0 < D.host.rdE := pf_rd_pos D
    have hL0 : 0 < large₂.sc.L := by linarith
    have h1 : Real.log D.host.rdE ≤ large₂.sc.L := by
      refine h11.trans ?_
      rw [div_le_iff₀ h25]; nlinarith
    have h2v : 2 * D.host.v = D.host.rdE := by
      show 2 * (D.host.rdE / 2) = D.host.rdE; ring
    rw [h2v]
    calc D.host.rdE = Real.exp (Real.log D.host.rdE) := (Real.exp_log hrd).symm
      _ ≤ Real.exp large₂.sc.L := Real.exp_le_exp.2 h1
      _ = large₂.sc.b := by rw [← hlb, Real.exp_log (by linarith)]
  · have hg1 : 1 ≤ D.host.g 1 := by
      rcases Nat.eq_zero_or_pos (D.host.g 1) with h | h
      · have : gS D = 0 := by simp [gS, h]
        omega
      · exact h
    calc ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g 0 : ℝ) := h12
      _ = (D.host.g 0 : ℝ) * 1 := (mul_one _).symm
      _ ≤ (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := by gcongr; exact_mod_cast hg1
      _ = (gS D : ℝ) := by simp [gS]
  · intro u
    refine ⟨(hT u).1.one_lt.le, ?_⟩
    have h := (h23 u).2
    calc (Tu D u : ℝ) = Tr D u := rfl
      _ ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) := h
      _ ≤ large₂.sc.b ^ (Ca * (D.R.m : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        have : (0 : ℝ) ≤ D.R.m := by positivity
        nlinarith

end GlobalTheory.TypeAsm
