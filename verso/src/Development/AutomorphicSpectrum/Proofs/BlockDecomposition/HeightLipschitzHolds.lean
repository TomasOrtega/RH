import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

namespace GlobalTheory.CompanionTheory.RgEis

open PositivityTheory.RgEis

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem htLip : PositivityTheory.RgEis.HtLip := by
  intro G _ _ _ Γ K P η hK hI hη C hC
  obtain ⟨M, hM⟩ := (hK.mul hC).exists_bound_of_continuousOn hη.cont.continuousOn
  refine ⟨M, fun g u hu => ?_⟩
  obtain ⟨p, hp, k, hk, rfl⟩ := hI g
  have h1 : η (p * k * u) = η p + η (k * u) := by
    rw [mul_assoc]; exact hη.left p hp _
  have h2 : η (p * k) = η p + η k := hη.left p hp k
  have h3 : η (1 : G) = 0 := by
    have := hη.left 1 P.one_mem 1
    simp only [mul_one] at this
    linarith
  have h4 : η k = 0 := by
    have := hη.right 1 k hk
    rw [one_mul] at this
    rw [this, h3]
  have h5 := hM (k * u) (Set.mul_mem_mul hk hu)
  rw [Real.norm_eq_abs] at h5
  rw [h1, h2, h4]
  simpa using h5

end GlobalTheory.CompanionTheory.RgEis
