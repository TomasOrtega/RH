import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGS

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(Valuation.integer.integers _).mem_of_integral h`. Introduce `h`. Establish `e : a = algebraMap 𝒪[F] F ⟨a, h⟩` using `rfl`.

Rewrite using `[e]`. Conclude with `isIntegral_algebraMap`.
-/
theorem isIntegral_iff_mem_integer (F : Type) [Field F] [ValuativeRel F] (a : F) :
    IsIntegral 𝒪[F] a ↔ a ∈ 𝒪[F] := by
  constructor
  · intro h
    exact (Valuation.integer.integers _).mem_of_integral h
  · intro h
    have e : a = algebraMap 𝒪[F] F ⟨a, h⟩ := rfl
    rw [e]
    exact isIntegral_algebraMap

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ L _ e x`. Rewrite using `[L.O_def]`. Establish `key : IsIntegral 𝒪[F] x ↔ IsIntegral 𝒪[F] (e x)`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `h.map ((e : E →ₐ[F] F × F).restrictScalars 𝒪[F])`. Introduce `h`. Establish `h'` using `h.map ((e.symm : F × F →ₐ[F] E).restrictScalars 𝒪[F])`. Simplify using `using h'`. Rewrite using `[key]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨(isIntegral_iff_mem_integer F _).1 (h.map (AlgHom.fst 𝒪[F] F F)), (isIntegral_iff_mem_integer F _).1 (h.map (AlgHom.snd 𝒪[F] F F))⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `IsIntegral.pair ((isIntegral_iff_mem_integer F _).2 h1) ((isIntegral_iff_mem_integer F _).2 h2)`.
-/
theorem integral_split_count : OSplit := by
  intro F E _ _ _ _ _ _ L _ e x
  rw [L.O_def]
  have key : IsIntegral 𝒪[F] x ↔ IsIntegral 𝒪[F] (e x) := by
    constructor
    · intro h
      exact h.map ((e : E →ₐ[F] F × F).restrictScalars 𝒪[F])
    · intro h
      have h' := h.map ((e.symm : F × F →ₐ[F] E).restrictScalars 𝒪[F])
      simpa using h'
  rw [key]
  constructor
  · intro h
    exact ⟨(isIntegral_iff_mem_integer F _).1 (h.map (AlgHom.fst 𝒪[F] F F)),
      (isIntegral_iff_mem_integer F _).1 (h.map (AlgHom.snd 𝒪[F] F F))⟩
  · rintro ⟨h1, h2⟩
    exact IsIntegral.pair ((isIntegral_iff_mem_integer F _).2 h1) ((isIntegral_iff_mem_integer F _).2 h2)

end PI.UnitaryGroupMassFormula.CntFormula
