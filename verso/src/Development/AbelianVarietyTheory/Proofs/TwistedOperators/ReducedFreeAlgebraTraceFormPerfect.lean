import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS

namespace GlobalTheory.RegSS

/- English proof (translation)
Establish `: IsArtinianRing L` using `IsArtinianRing.of_finite F L`. Establish `: IsSemisimpleRing L` using `IsArtinianRing.isSemisimpleRing_of_isReduced L`. Take `⟨e, he, hI⟩` from `IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span {x})`. Establish `hem : e ∈ Ideal.span {x}` using `hI ▸ Ideal.mem_span_singleton_self e`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 hem`.

Establish `htr : LinearMap.trace F L (Algebra.lmul F L e) = 0`. Rewrite using `[← Algebra.trace_apply, ← ha, mul_comm]`. Conclude with `hx a`. Establish `hidem : IsIdempotentElem (Algebra.lmul F L e)` using `he.map (Algebra.lmul F L)`. Establish `h0 : Algebra.lmul F L e = 0` using `LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hidem htr`.

Establish `he0 : e = 0`. Use `congrArg (fun f => f 1) h0` as an intermediate fact. Simplify using `using this`. Rewrite `hI` using `[he0]`. Conclude with `Ideal.span_singleton_eq_bot.1 (hI.trans (Ideal.span_singleton_eq_bot.2 rfl))`.
-/
theorem eq_zero_of_trace_mul_eq_zero {F L : Type} [Field F] [CharZero F] [CommRing L]
    [Algebra F L] [Module.Finite F L] [IsReduced L] (x : L)
    (hx : ∀ y : L, Algebra.trace F L (x * y) = 0) : x = 0 := by
  have : IsArtinianRing L := IsArtinianRing.of_finite F L
  have : IsSemisimpleRing L := IsArtinianRing.isSemisimpleRing_of_isReduced L

  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span {x})
  have hem : e ∈ Ideal.span {x} := hI ▸ Ideal.mem_span_singleton_self e
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hem

  have htr : LinearMap.trace F L (Algebra.lmul F L e) = 0 := by
    rw [← Algebra.trace_apply, ← ha, mul_comm]
    exact hx a
  have hidem : IsIdempotentElem (Algebra.lmul F L e) := he.map (Algebra.lmul F L)
  have h0 : Algebra.lmul F L e = 0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hidem htr
  have he0 : e = 0 := by
    have := congrArg (fun f => f 1) h0
    simpa using this
  rw [he0] at hI
  exact Ideal.span_singleton_eq_bot.1 (hI.trans (Ideal.span_singleton_eq_bot.2 rfl))

end GlobalTheory.RegSS

namespace GlobalTheory.RegSS

/- English proof (translation)
Unfold `TracePerfect`. Introduce `F E L _ _ _ _ _ _ _ _ _ _ _ _`. Establish `: Module.Finite F L` using `Module.Finite.trans E L`. Establish `: IsArtinianRing E` using `IsArtinianRing.of_finite F E`. Establish `inj : Function.Injective (Algebra.traceForm E L)`.

Introduce `x y hxy`. Establish `h : ∀ z : L, Algebra.trace F L ((x - y) * z) = 0`. Introduce `z`. Establish `hz` using `LinearMap.congr_fun hxy z`. Rewrite `hz` using `[Algebra.traceForm_apply, Algebra.traceForm_apply]`.

Rewrite using `[← Algebra.trace_trace (S := E), sub_mul, map_sub, hz, sub_self, map_zero]`. Conclude with `sub_eq_zero.1 (eq_zero_of_trace_mul_eq_zero (F := F) _ h)`. Set `b` to `Module.Free.chooseBasis E L`. Set `g : L →ₗ[E] L` to `b.toDualEquiv.symm.toLinearMap ∘ₗ Algebra.traceForm E L`. Establish `ginj : Function.Injective g` using `b.toDualEquiv.symm.injective.comp inj`.

Use `⟨inj, fun f => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `(IsArtinian.bijective_of_injective_endomorphism g ginj).2 (b.toDualEquiv.symm f)`. Conclude with `⟨x, b.toDualEquiv.symm.injective hx⟩`.
-/
theorem tracePerfect : TracePerfect := by
  unfold TracePerfect
  intro F E L _ _ _ _ _ _ _ _ _ _ _ _
  have : Module.Finite F L := Module.Finite.trans E L
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  have inj : Function.Injective (Algebra.traceForm E L) := by
    intro x y hxy

    have h : ∀ z : L, Algebra.trace F L ((x - y) * z) = 0 := by
      intro z
      have hz := LinearMap.congr_fun hxy z
      rw [Algebra.traceForm_apply, Algebra.traceForm_apply] at hz
      rw [← Algebra.trace_trace (S := E), sub_mul, map_sub, hz, sub_self, map_zero]
    exact sub_eq_zero.1 (eq_zero_of_trace_mul_eq_zero (F := F) _ h)
  let b := Module.Free.chooseBasis E L
  let g : L →ₗ[E] L := b.toDualEquiv.symm.toLinearMap ∘ₗ Algebra.traceForm E L
  have ginj : Function.Injective g := b.toDualEquiv.symm.injective.comp inj
  refine ⟨inj, fun f => ?_⟩
  obtain ⟨x, hx⟩ := (IsArtinian.bijective_of_injective_endomorphism g ginj).2
    (b.toDualEquiv.symm f)
  exact ⟨x, b.toDualEquiv.symm.injective hx⟩

end GlobalTheory.RegSS
