import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HBdNonneg
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PolyConstantLeZBasePowFour
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.SizesOfRows

/- English proof (translation)
Introduce `D large₂ h`. Take `⟨_, _, hm4, hm44, _, hb, _, _, _, hrd, hcond, _, _, _⟩` from `h`. Establish `hk : D.R.m + 3 ≤ D.R.k` using `D.R.m_add_three_le_k`. Establish `ht : D.R.k + D.R.m - 1 + 5 ≤ D.R.t` using `D.R.rank_add_five_le`. Establish `hd : 1 ≤ D.host.d` using `by have := D.host.qd_big.2; omega`.

Establish `hf : 1 ≤ D.R.f`. Establish `: 1 ≤ D.R.m ^ 4` using `Nat.one_le_pow _ _ (by omega)`. Use linear arithmetic over natural numbers and integers. Establish `hN1 : 1 ≤ D.R.N D.R.m` using `by simp only [Formalism.BasicNotions.Ranks.N]; omega`. Establish `hbig2 : bigN D ≤ 2 * D.R.N D.R.m`.

Simplify using `only [bigN, sLen, Formalism.BasicNotions.Ranks.N, Formalism.BasicNotions.Ranks.r]`. Establish `h1 : D.R.k + D.R.m - 1 + 6 ≤ D.R.t + 1` using `by omega`. Establish `h2 : D.R.m * (D.R.k + D.R.m - 1 + 6) ≤ D.R.m * (D.R.t + 1)` using `Nat.mul_le_mul_left _ h1`. Establish `e : D.R.m * (D.R.t + (D.R.k + D.R.m - 1 + 6) + 1) = D.R.m * (D.R.t + 1) + D.R.m * (D.R.k + D.R.m - 1 + 6)` using `by ring`. Use linear arithmetic over natural numbers and integers.

Establish `hmR : (44 : ℝ) ≤ D.R.m` using `by exact_mod_cast hm44`. Establish `hfR : (1 : ℝ) ≤ D.R.f` using `by exact_mod_cast hf`. Establish `hNR : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ)` using `by exact_mod_cast hN1`. Establish `hdR : (1 : ℝ) ≤ (D.host.d : ℝ)` using `by exact_mod_cast hd`. Establish `hbigR : (bigN D : ℝ) ≤ 2 * (D.R.N D.R.m : ℝ)` using `by exact_mod_cast hbig2`.

Establish `hN2 : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 2` using `by nlinarith`. Establish `hP1 : (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d`. Establish `a : (D.R.N D.R.m : ℝ) ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d`. Establish `: (D.R.N D.R.m : ℝ) ^ 2 ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2` using `by nlinarith`. Establish `: D.R.f * (D.R.N D.R.m : ℝ) ^ 2 ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d` using `by nlinarith`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `mul_le_mul_of_nonneg_left a (by linarith : (0:ℝ) ≤ D.R.m)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hP2 : (D.R.f : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d`. Establish `: (1 : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d`.

Establish `: (1:ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ^ 2` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Establish `hmN : 2 * (D.R.N D.R.m : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ)` using `by nlinarith`. Establish `hrd1 : 1 ≤ D.host.rdE` using `Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Pm.one_le_rdE D`.

Establish `hlogb : Real.log large₂.sc.b = large₂.sc.L` using `by show Real.log (Real.exp large₂.sc.L) = large₂.sc.L`. Conclude with `Real.log_exp _`. Use `⟨by linarith, by linarith, by simp only [bigN]; omega, hf, by omega, hrd1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hlogb]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `: (12 : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ)` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sizes_of_sizeRows : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → (bigN D : ℝ) ≤ large₂.sc.b ∧ (D.R.f : ℝ) ≤ large₂.sc.b ∧ 1 ≤ bigN D ∧ 1 ≤ D.R.f ∧ 2 ≤ D.R.m ∧ 1 ≤ D.host.rdE ∧ Real.log D.host.rdE ≤ Real.log large₂.sc.b / 100 ∧ 12 ≤ large₂.sc.b := by
  intro D large₂ h
  obtain ⟨_, _, hm4, hm44, _, hb, _, _, _, hrd, hcond, _, _, _⟩ := h
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have ht : D.R.k + D.R.m - 1 + 5 ≤ D.R.t := D.R.rank_add_five_le
  have hd : 1 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hf : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hN1 : 1 ≤ D.R.N D.R.m := by simp only [Formalism.BasicNotions.Ranks.N]; omega
  have hbig2 : bigN D ≤ 2 * D.R.N D.R.m := by
    simp only [bigN, sLen, Formalism.BasicNotions.Ranks.N, Formalism.BasicNotions.Ranks.r]
    have h1 : D.R.k + D.R.m - 1 + 6 ≤ D.R.t + 1 := by omega
    have h2 : D.R.m * (D.R.k + D.R.m - 1 + 6) ≤ D.R.m * (D.R.t + 1) := Nat.mul_le_mul_left _ h1
    have e : D.R.m * (D.R.t + (D.R.k + D.R.m - 1 + 6) + 1) = D.R.m * (D.R.t + 1) + D.R.m * (D.R.k + D.R.m - 1 + 6) := by ring
    omega
  have hmR : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hm44
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hNR : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hN1
  have hdR : (1 : ℝ) ≤ (D.host.d : ℝ) := by exact_mod_cast hd
  have hbigR : (bigN D : ℝ) ≤ 2 * (D.R.N D.R.m : ℝ) := by exact_mod_cast hbig2
  have hN2 : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
  have hP1 : (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
    have a : (D.R.N D.R.m : ℝ) ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
      have : (D.R.N D.R.m : ℝ) ^ 2 ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
      have : D.R.f * (D.R.N D.R.m : ℝ) ^ 2 ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by nlinarith
      linarith
    have := mul_le_mul_of_nonneg_left a (by linarith : (0:ℝ) ≤ D.R.m)
    linarith
  have hP2 : (D.R.f : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
    have : (1 : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
      have : (1:ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
      nlinarith
    nlinarith
  have hmN : 2 * (D.R.N D.R.m : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) := by nlinarith
  have hrd1 : 1 ≤ D.host.rdE := Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Pm.one_le_rdE D
  have hlogb : Real.log large₂.sc.b = large₂.sc.L := by
    show Real.log (Real.exp large₂.sc.L) = large₂.sc.L
    exact Real.log_exp _
  refine ⟨by linarith, by linarith, by simp only [bigN]; omega, hf, by omega, hrd1, ?_, ?_⟩
  · rw [hlogb]; linarith
  · have : (12 : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) := by nlinarith
    linarith

end GlobalTheory.SizesOfRows
