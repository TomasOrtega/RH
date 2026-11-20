import Mathlib
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Establish `hx : 1 < s.x` using `s.one_lt_alt`. Establish `hL : 0 ≤ s.L`. Unfold `Scale.L`. Conclude with `Real.rpow_nonneg (by linarith) _`. Establish `hb : 1 ≤ s.b`.

Unfold `Scale.b`. Conclude with `Real.one_le_exp hL`. Unfold `Scale.a`. Conclude with `one_le_mul_of_one_le_of_one_le hx.le hb`.
-/
theorem scale_one_le_a (s : Scale) : 1 ≤ s.a := by
  have hx : 1 < s.x := s.one_lt_alt
  have hL : 0 ≤ s.L := by
    unfold Scale.L
    exact Real.rpow_nonneg (by linarith) _
  have hb : 1 ≤ s.b := by
    unfold Scale.b
    exact Real.one_le_exp hL
  unfold Scale.a
  exact one_le_mul_of_one_le_of_one_le hx.le hb

/- English proof (translation)
Introduce `eps Fm x hx i`. Take `⟨-, -, -, -, -, -, hQD, -⟩` from `Fm.sizes x hx i`. Take `⟨-, -, -, -, -, -, hrd, -⟩` from `hQD`. Unfold `SizeData₂.La`. Conclude with `Real.log_nonneg (one_le_mul_of_one_le_of_one_le (scale_one_le_a _) hrd)`.
-/
theorem famP_La_nonneg : ∀ (eps : ℝ) (Fm : FamP eps), ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x,
    0 ≤ (Fm.L x i).La := by
  intro eps Fm x hx i
  obtain ⟨-, -, -, -, -, -, hQD, -⟩ := Fm.sizes x hx i
  obtain ⟨-, -, -, -, -, -, hrd, -⟩ := hQD
  unfold SizeData₂.La
  exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le (scale_one_le_a _) hrd)

end GlobalTheory
