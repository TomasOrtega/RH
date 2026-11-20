import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds

attribute [local instance] Formalism.MainNotions.S.starE

/- English proof (translation)
Introduce `D Λ h v`. Take `⟨⟨t, ht⟩, hv⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors (NumberField.RingOfIntegers D.host.E)) D.host.E (Λ : Set (Formalism.MainNotions.S.VS D).V) v (h.span_eq_top ▸ Submodule.mem_top)`. Take `⟨n, hn, c, hc⟩` from `(Algebra.IsAlgebraic.isAlgebraic (R := ℤ) t).exists_nonzero_dvd ht`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Establish `hc' : (n : NumberField.RingOfIntegers D.host.E) = c * t` using `by rw [mul_comm]; simpa using hc`.

Establish `e : (n : D.host.E) • v = c • t • v`. Rewrite using `[smul_smul, ← hc', ← algebraMap_smul D.host.E (n : NumberField.RingOfIntegers D.host.E) v, map_intCast]`. Rewrite `hv` using `[Submodule.span_eq]`. Conclude with `e ▸ Λ.smul_mem c hv`.
-/
theorem UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult :
    ∀ (D : Formalism.BasicNotions.D7)
    {Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Formalism.MainNotions.S.VS D).V},
    Submodule.IsLattice D.host.E Λ →
      ∀ (v : (Formalism.MainNotions.S.VS D).V),
        ∃ (n : ℤ),
          n ≠ (0 : ℤ) ∧
            (↑n : D.host.E) • v ∈
              Λ := by
  intro D Λ h v
  obtain ⟨⟨t, ht⟩, hv⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.host.E)) D.host.E (Λ : Set (Formalism.MainNotions.S.VS D).V) v
    (h.span_eq_top ▸ Submodule.mem_top)
  obtain ⟨n, hn, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) t).exists_nonzero_dvd ht
  refine ⟨n, hn, ?_⟩
  have hc' : (n : NumberField.RingOfIntegers D.host.E) = c * t := by rw [mul_comm]; simpa using hc
  have e : (n : D.host.E) • v = c • t • v := by
    rw [smul_smul, ← hc', ← algebraMap_smul D.host.E (n : NumberField.RingOfIntegers D.host.E) v, map_intCast]
  rw [Submodule.span_eq] at hv
  exact e ▸ Λ.smul_mem c hv
