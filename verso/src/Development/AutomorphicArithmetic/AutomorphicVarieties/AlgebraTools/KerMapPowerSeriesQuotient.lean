import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `f hf`. Rewrite `hf` using `[RingHom.mem_ker]`. Take `⟨s, rfl⟩` from `ha`. Establish `hc : ∀ n, PowerSeries.coeff n f ∈ Ideal.span (s : Set R)`.

Introduce `n`. Use `congrArg (PowerSeries.coeff n) hf` as an intermediate fact. Rewrite `this` using `[PowerSeries.coeff_map, map_zero]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 this`. Establish `hc' : ∀ n, ∃ c : R → R, ∑ x ∈ s, c x * x = PowerSeries.coeff n f`.

Introduce `n`. Take `⟨c, -, hc⟩` from `Submodule.mem_span_finset.1 (hc n)`. Conclude with `⟨c, by simpa [smul_eq_mul] using hc⟩`. Use `choose c hc' using hc'`. Establish `: f = ∑ x ∈ s, PowerSeries.mk (fun n => c n x) * PowerSeries.C x`.

Use extensionality with `n`. Rewrite using `[map_sum, ← hc' n]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[PowerSeries.coeff_mul_C, PowerSeries.coeff_mk]`. Rewrite using `[this]`.

Use `Ideal.sum_mem _ fun x hx => Ideal.mul_mem_left _ _ ?_` and prove the remaining obligations. Conclude with `Ideal.mem_map_of_mem _ (Ideal.subset_span hx)`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, PowerSeries.map_C, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]`.
-/
private theorem ker_map_power_series_quotient (R : Type) [CommRing R] (a : Ideal R) (ha : a.FG) :
    RingHom.ker (PowerSeries.map (Ideal.Quotient.mk a)) = a.map (PowerSeries.C : R →+* PowerSeries R) := by
  classical
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    obtain ⟨s, rfl⟩ := ha
    have hc : ∀ n, PowerSeries.coeff n f ∈ Ideal.span (s : Set R) := by
      intro n
      have := congrArg (PowerSeries.coeff n) hf
      rw [PowerSeries.coeff_map, map_zero] at this
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
    have hc' : ∀ n, ∃ c : R → R, ∑ x ∈ s, c x * x = PowerSeries.coeff n f := by
      intro n
      obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 (hc n)
      exact ⟨c, by simpa [smul_eq_mul] using hc⟩
    choose c hc' using hc'
    have : f = ∑ x ∈ s, PowerSeries.mk (fun n => c n x) * PowerSeries.C x := by
      ext n
      rw [map_sum, ← hc' n]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_mk]
    rw [this]
    refine Ideal.sum_mem _ fun x hx => Ideal.mul_mem_left _ _ ?_
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span hx)
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, PowerSeries.map_C, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]

/- English proof (translation)
Introduce `R _ a ha`. Establish `hk` using `ker_map_power_series_quotient R a ha`. Use `⟨hk, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g choose c hc using fun n => Ideal.Quotient.mk_surjective (I := a) (PowerSeries.coeff n g)`. Use `⟨PowerSeries.mk c, ?_⟩` and prove the remaining obligations.

Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_map, PowerSeries.coeff_mk, hc]`. Introduce `hp`. Rewrite using `[← hk]`. Conclude with `RingHom.ker_isPrime _`.

Rewrite using `[← hk]`. Use extensionality with `x`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, PowerSeries.map_C, ← Ideal.Quotient.eq_zero_iff_mem]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `PowerSeries.C_injective (by rw [h, map_zero])`. Introduce `h`. Rewrite using `[h, map_zero]`.
-/
theorem UpperTheory.V.AlgebraTools.powerSeries_ker_map :
    ∀ (R : Type) [CommRing R] (a : Ideal R), a.FG →
      RingHom.ker (PowerSeries.map (Ideal.Quotient.mk a)) = a.map (PowerSeries.C : R →+* PowerSeries R) ∧
      Function.Surjective (PowerSeries.map (Ideal.Quotient.mk a)) ∧
      (a.IsPrime → (a.map (PowerSeries.C : R →+* PowerSeries R)).IsPrime) ∧
      (a.map (PowerSeries.C : R →+* PowerSeries R)).comap (PowerSeries.C : R →+* PowerSeries R) = a := by
  intro R _ a ha
  have hk := ker_map_power_series_quotient R a ha
  refine ⟨hk, ?_, ?_, ?_⟩
  · intro g
    choose c hc using fun n => Ideal.Quotient.mk_surjective (I := a) (PowerSeries.coeff n g)
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, hc]
  · intro hp
    rw [← hk]
    exact RingHom.ker_isPrime _
  · rw [← hk]
    ext x
    rw [Ideal.mem_comap, RingHom.mem_ker, PowerSeries.map_C, ← Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro h
      exact PowerSeries.C_injective (by rw [h, map_zero])
    · intro h
      rw [h, map_zero]
