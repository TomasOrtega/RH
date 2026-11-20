import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap

namespace GlobalTheory.BK

open PowerSeries Filter Topology

/- English proof (translation)
Rewrite using `[mem_nonZeroDivisors_iff_right]`. Introduce `x hx`. Use `AdicCompletion.ext_evalₐ fun n => ?_` and prove the remaining obligations. Take `⟨r, hr⟩` from `Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {s}) (n + 1) x)`. Establish `h1` using `congrArg (AdicCompletion.evalₐ (Ideal.span {s}) (n + 1)) hx`.

Rewrite `h1` using `[map_mul, map_zero, AlgHom.commutes, ← hr, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨c, hc⟩` from `h1`. Establish `h2 : (r - s ^ n * c) * s = 0` using `by rw [sub_mul, hc]; ring`. Establish `h3` using `(mem_nonZeroDivisors_iff_right.1 hs) _ h2`. Rewrite using `[evalₐ_of_succ _ hr.symm, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.

Conclude with `⟨c, sub_eq_zero.1 h3⟩`.
-/
theorem algebraMap_mem_nonZeroDivisors_adicCompletion {B : Type} [CommRing B] {s : B}
    (hs : s ∈ nonZeroDivisors B) :
    algebraMap B (AdicCompletion (Ideal.span {s}) B) s ∈
      nonZeroDivisors (AdicCompletion (Ideal.span {s}) B) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {s}) (n + 1) x)
  have h1 := congrArg (AdicCompletion.evalₐ (Ideal.span {s}) (n + 1)) hx
  rw [map_mul, map_zero, AlgHom.commutes, ← hr, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 : (r - s ^ n * c) * s = 0 := by rw [sub_mul, hc]; ring
  have h3 := (mem_nonZeroDivisors_iff_right.1 hs) _ h2
  rw [evalₐ_of_succ _ hr.symm, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  exact ⟨c, sub_eq_zero.1 h3⟩

/- English proof (translation)
The claim follows from `algebraMap_mem_nonZeroDivisors_adicCompletion (mem_nonZeroDivisors_of_ne_zero fun h => (isUnit_E (K := K) l e).ne_zero (congrArg Subtype.val h))`.
-/
theorem Ehat_mem_nonZeroDivisors (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] : Ehat O K l e ∈ nonZeroDivisors (Ahat O K l e) :=
  algebraMap_mem_nonZeroDivisors_adicCompletion (mem_nonZeroDivisors_of_ne_zero fun h =>
    (isUnit_E (K := K) l e).ne_zero (congrArg Subtype.val h))

end GlobalTheory.BK
