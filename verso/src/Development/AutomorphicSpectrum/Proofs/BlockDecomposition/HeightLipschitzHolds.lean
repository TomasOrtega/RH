import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

namespace GlobalTheory.CompanionTheory.RgEis

open PositivityTheory.RgEis

/- English proof (translation)
Introduce `G _ _ _ Γ K P η hK hI hη C hC`. Take `⟨M, hM⟩` from `(hK.mul hC).exists_bound_of_continuousOn hη.cont.continuousOn`. Use `⟨M, fun g u hu => ?_⟩` and prove the remaining obligations. Take `⟨p, hp, k, hk, rfl⟩` from `hI g`. Establish `h1 : η (p * k * u) = η p + η (k * u)`.

Rewrite using `[mul_assoc]`. Conclude with `hη.left p hp _`. Establish `h2 : η (p * k) = η p + η k` using `hη.left p hp k`. Establish `h3 : η (1 : G) = 0`. Use `hη.left 1 P.one_mem 1` as an intermediate fact.

Simplify using `only [mul_one] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : η k = 0`. Use `hη.right 1 k hk` as an intermediate fact. Rewrite `this` using `[one_mul]`.

Rewrite using `[this, h3]`. Establish `h5` using `hM (k * u) (Set.mul_mem_mul hk hu)`. Rewrite `h5` using `[Real.norm_eq_abs]`. Rewrite using `[h1, h2, h4]`. Simplify using `using h5`.
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
