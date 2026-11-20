import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAmpleOfGenTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

/- English proof (translation)
Introduce `S _ K _ _ ι _ _ V α p q hV hα hp`. Use `⟨1, le_rfl, ?_, fun e => ?_⟩` and prove the remaining obligations. Rewrite using `[one_smul]`. Conclude with `hGen S K ι V α q p hα`. Take `⟨c₀, hc₀⟩` from `hVan S K ι V α hV hα e`.

Use `⟨c₀, fun c hc => ?_⟩` and prove the remaining obligations. Establish `hN : e + (c * 1) • ((q : ℤ) • α + fun _ => (p : ℤ)) = e + ((c * q : ℕ) : ℤ) • α + fun _ => ((c * p : ℕ) : ℤ)`. Use function extensionality and compare the values at `k`. Express the relevant statement in the definitionally equal form `e k + (c * 1) • ((q : ℤ) • α k + (p : ℤ)) = e k + ((c * q : ℕ) : ℤ) • α k + ((c * p : ℕ) : ℤ)`. Simplify using `only [nsmul_eq_mul, smul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hN]`. Conclude with `hc₀ (c * q) (c * p) (le_trans hc (Nat.le_mul_of_pos_right c hp))`.
-/
theorem AmpleOfGenTwist.proof (hGen : GenTwistGenerated.Statement) (hVan : GenTwistVanish.Statement) :
    AmpleOfGenTwist.Statement := by
  intro S _ K _ _ ι _ _ V α p q hV hα hp
  refine ⟨1, le_rfl, ?_, fun e => ?_⟩
  · rw [one_smul]
    exact hGen S K ι V α q p hα
  · obtain ⟨c₀, hc₀⟩ := hVan S K ι V α hV hα e
    refine ⟨c₀, fun c hc => ?_⟩
    have hN : e + (c * 1) • ((q : ℤ) • α + fun _ => (p : ℤ)) =
        e + ((c * q : ℕ) : ℤ) • α + fun _ => ((c * p : ℕ) : ℤ) := by
      funext k
      change e k + (c * 1) • ((q : ℤ) • α k + (p : ℤ)) = e k + ((c * q : ℕ) : ℤ) • α k + ((c * p : ℕ) : ℤ)
      simp only [nsmul_eq_mul, smul_eq_mul]
      push_cast
      ring
    rw [hN]
    exact hc₀ (c * q) (c * p) (le_trans hc (Nat.le_mul_of_pos_right c hp))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
