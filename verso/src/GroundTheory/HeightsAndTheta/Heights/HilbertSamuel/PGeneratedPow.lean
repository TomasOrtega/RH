import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedPow
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

/- English proof (translation)
Introduce `S _ K _ _ ι _ _ V n t hn`. Proceed by induction on `t with`. Consider the case `zero`. Establish `h0` using `GenTwistGenerated.generated_diag (S := S) (ι := ι) (V := V) 0`. Establish `e : (fun _ : K => ((0 : ℕ) : ℤ)) = (0 • n : K → ℤ)`.

Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Rewrite using `[← e]`. Conclude with `h0`. Consider the case `succ t ih`.

Rewrite using `[succ_nsmul']`. Conclude with `GenTwistGenerated.generated_add hn ih`.
-/
theorem GeneratedPow.proof : GeneratedPow.Statement := by
  intro S _ K _ _ ι _ _ V n t hn
  induction t with
  | zero =>
    have h0 := GenTwistGenerated.generated_diag (S := S) (ι := ι) (V := V) 0
    have e : (fun _ : K => ((0 : ℕ) : ℤ)) = (0 • n : K → ℤ) := by
      funext k
      simp
    rw [← e]
    exact h0
  | succ t ih =>
    rw [succ_nsmul']
    exact GenTwistGenerated.generated_add hn ih

end GroundTheory.Heights₂.Heights.HilbertSamuel
