import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplShortPrim

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[intVec]`.
-/
lemma intVec_smul {ι : Type} (m : ℤ) (w : ι → ℤ) : intVec (m • w) = (m : ℝ) • intVec w := by
  funext i
  simp [intVec]

/- English proof (translation)
Simplify using `only [qf, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma qf_smul {ι : Type} [Fintype ι] (Y : Matrix ι ι ℝ) (c : ℝ) (x : ι → ℝ) :
    qf Y (c • x) = c ^ 2 * qf Y x := by
  simp only [qf, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

end PSymplShortPrim

open PSymplShortPrim in

/- English proof (translation)
Introduce `ι _ _ G hG v w m hvw hv hmin`. Establish `hm : m ≠ 0`. Introduce and unpack `rfl`. Conclude with `hv (by simp [hvw])`. Establish `hw : w ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hv (by simp [hvw])`. Establish `hwR : intVec w ≠ 0`. Introduce `h`. Apply `hw` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Use `congrFun h i` as an intermediate fact. Simplify `this` using `[intVec]`. Establish `hq : 0 < qf G (intVec w)`. Use `hG.dotProduct_mulVec_pos hwR` as an intermediate fact.

Simplify `this` using `[qf]`. Establish `hle` using `hmin w hw`. Rewrite `hle` using `[hvw, intVec_smul, qf_smul]`. Establish `hm2 : ((m : ℝ)) ^ 2 ≤ 1`. Assume the negation of the conclusion as `h`.

Rewrite `h` using `[not_le]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hm2' : m ^ 2 ≤ 1` using `by exact_mod_cast hm2`. Establish `habs : |m| ≤ 1` using `(sq_le_one_iff_abs_le_one m).mp hm2'`. Rewrite `habs` using `[abs_le]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem SymplShortPrim.proof : SymplShortPrim.Statement := by
  intro ι _ _ G hG v w m hvw hv hmin
  have hm : m ≠ 0 := by
    rintro rfl
    exact hv (by simp [hvw])
  have hw : w ≠ 0 := by
    rintro rfl
    exact hv (by simp [hvw])
  have hwR : intVec w ≠ 0 := by
    intro h
    apply hw
    funext i
    have := congrFun h i
    simpa [intVec] using this
  have hq : 0 < qf G (intVec w) := by
    have := hG.dotProduct_mulVec_pos hwR
    simpa [qf] using this
  have hle := hmin w hw
  rw [hvw, intVec_smul, qf_smul] at hle
  have hm2 : ((m : ℝ)) ^ 2 ≤ 1 := by
    by_contra h
    rw [not_le] at h
    nlinarith
  have hm2' : m ^ 2 ≤ 1 := by exact_mod_cast hm2
  have habs : |m| ≤ 1 := (sq_le_one_iff_abs_le_one m).mp hm2'
  rw [abs_le] at habs
  omega

end GroundTheory.Heights₂.Heights
