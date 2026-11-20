import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

namespace GlobalTheory.CompanionTheory.WaveFc

open PositivityTheory.RgBcC.Fc

/- English proof (translation)
Introduce `c N t y`. Establish `hsq : ((y : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = y`. Rewrite using `[← Complex.cpow_nat_mul]`. Evaluate the numerical expressions. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `h2 : Even 2` using `⟨1, rfl⟩`. Establish `h0 : Even 0` using `⟨0, rfl⟩`. Simplify using `only [PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj, h2, h0, if_true, hsq, pow_zero, one_mul]`. Use `first`. Consider the case `ring`.

Consider the case `(simp [hsq]; ring_nf)`. Consider the case `simp [hsq]`. Simplify using `[PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj]`. Simplify using `[PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj]`. Introduce `j`.

Simplify using `only [PositivityTheory.RgBcC.Fc.wv]`. Rewrite using `[pow_succ (1 + y ^ 2) N, mul_inv]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wvAlg : WvAlg := by
  intro c N t y
  have hsq : ((y : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = y := by
    rw [← Complex.cpow_nat_mul]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h2 : Even 2 := ⟨1, rfl⟩
    have h0 : Even 0 := ⟨0, rfl⟩
    simp only [PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj, h2, h0, if_true, hsq, pow_zero, one_mul]
    first
      | ring
      | (simp [hsq]; ring_nf)
      | simp [hsq]
  · simp [PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj]
  · simp [PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj]
  · intro j
    simp only [PositivityTheory.RgBcC.Fc.wv]
    rw [pow_succ (1 + y ^ 2) N, mul_inv]
    push_cast
    ring

end GlobalTheory.CompanionTheory.WaveFc
