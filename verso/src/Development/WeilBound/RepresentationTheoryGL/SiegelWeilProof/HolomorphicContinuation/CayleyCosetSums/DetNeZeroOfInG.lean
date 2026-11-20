import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolomorphicScalarSection
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact

noncomputable section

open Matrix Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Unfold `InG at *`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inG_mul {x y : M2 n} (hx : InG x) (hy : InG y) : InG (x * y) := by
  unfold InG at *
  rw [Matrix.conjTranspose_mul]
  calc yᴴ * xᴴ * JJ n * (x * y) = yᴴ * (xᴴ * JJ n * x) * y := by simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [hx, hy]

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrArg Matrix.det hx`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, h, mul_zero]`. Establish `h2 : (JJ n).det ≠ 0`. Use `congrArg Matrix.det (JJ_mul_JJ (n := n))` as an intermediate fact.

Rewrite `this` using `[Matrix.det_mul, Matrix.det_neg]`. Introduce `h3`. Rewrite `this` using `[h3, zero_mul]`. Simplify using `at this`. Conclude with `h2 h1.symm`.
-/
theorem det_ne_zero_of_inG {x : M2 n} (hx : InG x) : x.det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det hx
  rw [Matrix.det_mul, Matrix.det_mul, h, mul_zero] at h1
  have h2 : (JJ n).det ≠ 0 := by
    have := congrArg Matrix.det (JJ_mul_JJ (n := n))
    rw [Matrix.det_mul, Matrix.det_neg] at this
    intro h3
    rw [h3, zero_mul] at this
    simp at this
  exact h2 h1.symm

def toGR (x : M2 n) (hx : InG x) : GR n := ⟨(Matrix.isUnit_iff_isUnit_det _ |>.2 (isUnit_iff_ne_zero.2
  (det_ne_zero_of_inG hx))).unit, hx⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_toGR (x : M2 n) (hx : InG x) : mR (toGR x hx) = x := rfl

end PositivityTheory.Rg.Sw.HSt.CR
