import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG

noncomputable section

namespace Formalism.MainNotions.NearParameterGap

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.OnePlaceEstimates

def Cg0 : ℝ := 1000

/- English proof (translation)
Establish `hN1 : (1 : ℝ) ≤ N` using `by linarith`. Establish `hN3 : (0 : ℝ) ≤ N ^ 3` using `by positivity`. Establish `hm2' : (4 : ℝ) ≤ m ^ 2` using `by nlinarith`. Establish `hm4e : m ^ 4 = m ^ 2 * m ^ 2` using `by ring`. Establish `hm4 : (16 : ℝ) ≤ m ^ 4` using `by rw [hm4e]; nlinarith`.

Establish `hm4' : 4 * m ^ 2 ≤ m ^ 4` using `by rw [hm4e]; nlinarith`. Establish `hCg0 : (0 : ℝ) ≤ Cg` using `by linarith`. Prove the components needed by the constructor for the conclusion. Establish `a : (16 : ℝ) ≤ m ^ 4 * s` using `le_trans hm4 (le_mul_of_one_le_right (by positivity) hs)`. Establish `b : (16000 : ℝ) ≤ Cg * (m ^ 4 * s)` using `by nlinarith`.

Establish `c : 16000 * N ^ 3 ≤ Cg * (m ^ 4 * s) * P` using `le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `b : 4000 * m ^ 2 ≤ Cg * m ^ 4` using `by nlinarith`. Establish `c : 4000 * m ^ 2 * N ^ 3 ≤ Cg * m ^ 4 * P` using `le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sizes (Cg m N P s : ℝ) (hCg : 1000 ≤ Cg) (hm2 : 2 ≤ m) (hmN : m ≤ N) (hPN : N ^ 3 ≤ P) (hs : 1 ≤ s) :
    120 * N ^ 3 ≤ Cg * (m ^ 4 * s) * P / 4 ∧ 125 * m ^ 2 * N ^ 3 ≤ Cg * m ^ 4 * P / 32 := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN3 : (0 : ℝ) ≤ N ^ 3 := by positivity
  have hm2' : (4 : ℝ) ≤ m ^ 2 := by nlinarith
  have hm4e : m ^ 4 = m ^ 2 * m ^ 2 := by ring
  have hm4 : (16 : ℝ) ≤ m ^ 4 := by rw [hm4e]; nlinarith
  have hm4' : 4 * m ^ 2 ≤ m ^ 4 := by rw [hm4e]; nlinarith
  have hCg0 : (0 : ℝ) ≤ Cg := by linarith
  constructor
  · have a : (16 : ℝ) ≤ m ^ 4 * s := le_trans hm4 (le_mul_of_one_le_right (by positivity) hs)
    have b : (16000 : ℝ) ≤ Cg * (m ^ 4 * s) := by nlinarith
    have c : 16000 * N ^ 3 ≤ Cg * (m ^ 4 * s) * P :=
      le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))
    linarith
  · have b : 4000 * m ^ 2 ≤ Cg * m ^ 4 := by nlinarith
    have c : 4000 * m ^ 2 * N ^ 3 ≤ Cg * m ^ 4 * P :=
      le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))
    linarith

/- English proof (translation)
Establish `hr0 : (0 : ℝ) ≤ r` using `Nat.cast_nonneg _`. Establish `hk1 : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Use `set N : ℝ := 2 * (r : ℝ) + k + 1 with hN`. Establish `hN1 : (1 : ℝ) ≤ N` using `by linarith`. Establish `hN2 : N ^ 2 ≤ N ^ 3` using `by nlinarith`.

Establish `hdN : Formalism.FourierDecayAlt.ThreeDimData.dN k r ≤ 2 * N ^ 2` using `by unfold Formalism.FourierDecayAlt.ThreeDimData.dN; rw [hN]; nlinarith`. Establish `hdN0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.dN k r` using `by unfold Formalism.FourierDecayAlt.ThreeDimData.dN; nlinarith`. Establish `hnk : ((2 * r + k : ℕ) : ℝ) ≤ N` using `by rw [hN]; push_cast; linarith`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `Formalism.FourierDecayAlt.ThreeDimData.Mexp`.

Use the polynomial consequences of the given equalities and inequalities. Unfold `Formalism.FourierDecayAlt.ThreeDimData.Mexp`. Check the signs of the components of the expression. Unfold `Formalism.FourierDecayAlt.ThreeDimData.AS`. Establish `: ((2 * r + k : ℕ) : ℝ) * Formalism.FourierDecayAlt.ThreeDimData.dN k r ≤ N * (2 * N ^ 2)` using `mul_le_mul hnk hdN hdN0 (by linarith)`.

Use the polynomial consequences of the given equalities and inequalities. Unfold `Formalism.FourierDecayAlt.ThreeDimData.AS`. Check the signs of the components of the expression. Unfold `Formalism.FourierDecayAlt.ThreeDimData.AG`. Establish `e1 : ((k : ℝ) + r) ≤ N` using `by rw [hN]; linarith`.

Establish `e2 : ((r : ℝ) + 1) ≤ N` using `by rw [hN]; linarith`. Establish `e3 : ((k : ℝ) + r) * ((r : ℝ) + 1) ≤ N * N` using `mul_le_mul e1 e2 (by linarith) (by linarith)`. Use the polynomial consequences of the given equalities and inequalities. Unfold `Formalism.FourierDecayAlt.ThreeDimData.AG`. Check the signs of the components of the expression.
-/
theorem consts (k r : ℕ) (hk : 1 ≤ k) :
    Formalism.FourierDecayAlt.ThreeDimData.Mexp r ≤ (2 * (r : ℝ) + 2) ^ 2 / 2 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.Mexp r ∧
    Formalism.FourierDecayAlt.ThreeDimData.AS k r ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 3 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AS k r ∧
    Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 4 * (2 * (r : ℝ) + k + 1) ^ 3 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set N : ℝ := 2 * (r : ℝ) + k + 1 with hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN2 : N ^ 2 ≤ N ^ 3 := by nlinarith
  have hdN : Formalism.FourierDecayAlt.ThreeDimData.dN k r ≤ 2 * N ^ 2 := by unfold Formalism.FourierDecayAlt.ThreeDimData.dN; rw [hN]; nlinarith
  have hdN0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.dN k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.dN; nlinarith
  have hnk : ((2 * r + k : ℕ) : ℝ) ≤ N := by rw [hN]; push_cast; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; positivity
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AS
    have : ((2 * r + k : ℕ) : ℝ) * Formalism.FourierDecayAlt.ThreeDimData.dN k r ≤ N * (2 * N ^ 2) :=
      mul_le_mul hnk hdN hdN0 (by linarith)
    nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AS; positivity
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AG
    have e1 : ((k : ℝ) + r) ≤ N := by rw [hN]; linarith
    have e2 : ((r : ℝ) + 1) ≤ N := by rw [hN]; linarith
    have e3 : ((k : ℝ) + r) * ((r : ℝ) + 1) ≤ N * N := mul_le_mul e1 e2 (by linarith) (by linarith)
    nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity

end Formalism.MainNotions.NearParameterGap
