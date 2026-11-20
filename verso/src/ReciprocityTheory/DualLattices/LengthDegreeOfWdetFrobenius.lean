import ReciprocityTheory.DualLattices.KilledGen
import ReciprocityTheory.DualLattices.IdemGen
import ReciprocityTheory.DualLattices.LenEx
import ReciprocityTheory.DualLattices.CokernelLengthComparisonOf

namespace ReciprocityTheory.PGsh.Up

/- English proof (translation)
The claim follows from `cokernelLowerBound_of hU6 hU7 lenEx killedGen idemGen`.
-/
theorem lengthDegree_of_wdet_frobenius (hU6 : CokernelLengthComparisonStatement) (hU7 : UnramifiedCokernelLengthStatement) : CokernelLowerBoundStatement :=
  cokernelLowerBound_of hU6 hU7 lenEx killedGen idemGen

/- English proof (translation)
Use `lengthDegree_of_wdet_frobenius ?_ hU7` and prove the remaining obligations. Introduce `p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H m e π he hσ h1 h2 h3 h4 w hw cw cwb hcw hcwb`. Take `⟨d, X, hd, hX, hXc⟩` from `hW1 p g C v R O σ cp hS H m e π he hσ h1 h2 h3 h4 w hw cw cwb hcw hcwb`. Establish `hle` using `hW2 p g C v R O σ cp hS H m e π he hσ h1 h2 h3 h4 w hw d X hd hX`. Establish `hcp : v (algebraMap R C cp) ≠ 0`.

Introduce `h0`. Establish `h5` using `hS.cp_val`. Rewrite `h5` using `[h0, zero_pow (by have := (Fact.out : Nat.Prime p).two_le; omega)]`. Conclude with `hS.p_ne h5.symm`. Establish `hpos : 0 < v (algebraMap R C cp) ^ d` using `pow_pos (pos_iff_ne_zero.mpr hcp) d`.

Establish `h6 : v (algebraMap R C cp) ^ d * cwb ≤ v (algebraMap R C cp) ^ d * cw`. Rewrite using `[← hXc]`. Conclude with `mul_le_mul_of_nonneg_right hle zero_le`. Conclude with `le_of_mul_le_mul_left h6 hpos`.
-/
theorem lengthDegree_of_wdet_parts (hW1 : WdetLenStatement) (hW2 : WdetDegStatement) (hU7 : UnramifiedCokernelLengthStatement) :
    CokernelLowerBoundStatement := by
  refine lengthDegree_of_wdet_frobenius ?_ hU7
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H m e π he hσ h1 h2 h3 h4 w hw cw cwb hcw hcwb
  obtain ⟨d, X, hd, hX, hXc⟩ :=
    hW1 p g C v R O σ cp hS H m e π he hσ h1 h2 h3 h4 w hw cw cwb hcw hcwb
  have hle := hW2 p g C v R O σ cp hS H m e π he hσ h1 h2 h3 h4 w hw d X hd hX
  have hcp : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    have h5 := hS.cp_val
    rw [h0, zero_pow (by have := (Fact.out : Nat.Prime p).two_le; omega)] at h5
    exact hS.p_ne h5.symm
  have hpos : 0 < v (algebraMap R C cp) ^ d := pow_pos (pos_iff_ne_zero.mpr hcp) d
  have h6 : v (algebraMap R C cp) ^ d * cwb ≤ v (algebraMap R C cp) ^ d * cw := by
    rw [← hXc]
    exact mul_le_mul_of_nonneg_right hle zero_le
  exact le_of_mul_le_mul_left h6 hpos

end ReciprocityTheory.PGsh.Up
