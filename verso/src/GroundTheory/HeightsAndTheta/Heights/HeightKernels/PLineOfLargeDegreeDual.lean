import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

/- English proof (translation)
Introduce `hZ1 hZ2 hEx K _ _ i hi F ε hε`. Take `⟨II, hII⟩` from `hEx`. Take `⟨T, _, _, ⟨b⟩⟩` from `hBasis K i F`. Establish `hb` using `hBij K i F T b`. Use `set A := dualLine F b hb with hA`.

Use `set e : ℝ := -F.slope + 1 / 2 * Real.log i + ε with he`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hW : ∀ W : Ideal (MRing (dualBlocks T)), IsArithVar W 1 → dualIdeal b ≤ W → e * degC W ≤ II Unit (dualBlocks T) W 1 ![A]`. Introduce `W hW1 hPW`.

Take `⟨hdeg, K', iF, iN, iA, v, hv, hline⟩` from `hPt K i F T b hb II hII W hW1 hPW`. Establish `hlt` using `hne K' iF iN iA v hv`. Rewrite `hlt` using `[hline]`. Establish `hd : (0 : ℝ) < degC W` using `by exact_mod_cast hdeg`. Establish `h1 : e < II Unit (dualBlocks T) W 1 ![A] / degC W`.

Rewrite `hlt` using `[neg_div]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `((lt_div_iff₀ hd).mp h1).le`. Establish `hV : IsArithVar (dualIdeal b) (i - 1 + 1)`. Rewrite using `[Nat.sub_add_cancel hi]`.

Conclude with `hArith K i F T b hi`. Establish `hZ` using `hZ1 Unit (dualBlocks T) (dualIdeal b) ⊥ (i - 1) A e II hII hV bot_le (hSemi K i F T b hb) (hNef _ _ _ _ fun _ => zero_le_one) (hConj K i F T b hb) hW`. Rewrite `hZ` using `[Nat.sub_add_cancel hi]`. Establish `hT` using `hTop hZ2 K i F T b hb II hi hII`. Establish `hG` using `hPos K i F T b hb hi`.

Establish `hi' : (0 : ℝ) < i` using `by exact_mod_cast hi`. Establish `key : (i : ℝ) * e * geomDeg (dualIdeal b) A (i - 1) ≤ (i : ℝ) * (-F.slope + 1 / 2 * Real.log i) * geomDeg (dualIdeal b) A (i - 1)` using `hZ.trans hT`. Establish `: (i : ℝ) * ε * geomDeg (dualIdeal b) A (i - 1) ≤ 0`. Rewrite `key` using `[he]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `: 0 < (i : ℝ) * ε * geomDeg (dualIdeal b) A (i - 1)` using `mul_pos (mul_pos hi' hε) hG`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem LineOfLargeDegreeFromZ.proofDual (hBasis : DualLatticeBasisExists.Statement)
    (hBij : DualEmbBijective.Statement) (hArith : DualArithVar.Statement)
    (hSemi : DualLineSemipositive.Statement) (hNef : NefOfNonneg.Statement)
    (hConj : DualLineConj.Statement) (hPt : DualPointLineDegree.Statement)
    (hTop : DualTopBound.Statement) (hPos : DualGeomDegPos.Statement) :
    LineOfLargeDegreeFromZ.Statement := by
  intro hZ1 hZ2 hEx K _ _ i hi F ε hε
  obtain ⟨II, hII⟩ := hEx
  obtain ⟨T, _, _, ⟨b⟩⟩ := hBasis K i F
  have hb := hBij K i F T b
  set A := dualLine F b hb with hA
  set e : ℝ := -F.slope + 1 / 2 * Real.log i + ε with he
  by_contra hne
  push Not at hne
  have hW : ∀ W : Ideal (MRing (dualBlocks T)), IsArithVar W 1 → dualIdeal b ≤ W →
      e * degC W ≤ II Unit (dualBlocks T) W 1 ![A] := by
    intro W hW1 hPW
    obtain ⟨hdeg, K', iF, iN, iA, v, hv, hline⟩ := hPt K i F T b hb II hII W hW1 hPW
    have hlt := hne K' iF iN iA v hv
    rw [hline] at hlt
    have hd : (0 : ℝ) < degC W := by exact_mod_cast hdeg
    have h1 : e < II Unit (dualBlocks T) W 1 ![A] / degC W := by
      rw [neg_div] at hlt
      linarith
    exact ((lt_div_iff₀ hd).mp h1).le
  have hV : IsArithVar (dualIdeal b) (i - 1 + 1) := by
    rw [Nat.sub_add_cancel hi]; exact hArith K i F T b hi
  have hZ := hZ1 Unit (dualBlocks T) (dualIdeal b) ⊥ (i - 1) A e II hII hV
    bot_le (hSemi K i F T b hb) (hNef _ _ _ _ fun _ => zero_le_one) (hConj K i F T b hb) hW
  rw [Nat.sub_add_cancel hi] at hZ
  have hT := hTop hZ2 K i F T b hb II hi hII
  have hG := hPos K i F T b hb hi
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have key : (i : ℝ) * e * geomDeg (dualIdeal b) A (i - 1) ≤
      (i : ℝ) * (-F.slope + 1 / 2 * Real.log i) * geomDeg (dualIdeal b) A (i - 1) := hZ.trans hT
  have : (i : ℝ) * ε * geomDeg (dualIdeal b) A (i - 1) ≤ 0 := by
    rw [he] at key
    nlinarith
  have : 0 < (i : ℝ) * ε * geomDeg (dualIdeal b) A (i - 1) :=
    mul_pos (mul_pos hi' hε) hG
  linarith

end GroundTheory.Heights₂.Heights
