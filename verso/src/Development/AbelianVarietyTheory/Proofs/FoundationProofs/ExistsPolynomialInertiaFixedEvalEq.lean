import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsDirichletCharacterSmoothed
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace GlobalTheory

/- English proof (translation)
Set `T : IntermediateField F Ω` to `IntermediateField.fixedField H.toSubgroup`. Establish `hT : T.fixingSubgroup = H.toSubgroup` using `InfiniteGalois.fixingSubgroup_fixedField H`. Set `E : IntermediateField F Ω` to `(IntermediateField.adjoin T ({ζ} : Set Ω)).restrictScalars F`. Establish `hu : u ∈ E`. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]`.

Introduce `s hs`. Rewrite `hs` using `[IntermediateField.mem_fixingSubgroup_iff]`. Use `h s ?_ (hs ζ (IntermediateField.mem_adjoin_simple_self T ζ))` and prove the remaining obligations. Establish `: s ∈ T.fixingSubgroup`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`.

Introduce `x hx`. Conclude with `hs x ((IntermediateField.adjoin T ({ζ} : Set Ω)).algebraMap_mem ⟨x, hx⟩)`. Rewrite `this` using `[hT]`. Conclude with `this`. Establish `hint : IsIntegral T ζ` using `(Algebra.IsAlgebraic.isAlgebraic (R := F) ζ).isIntegral.tower_top`.

Establish `hu' : u ∈ (IntermediateField.adjoin T ({ζ} : Set Ω)).toSubalgebra` using `hu`. Rewrite `hu'` using `[IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨Q, hQ⟩` from `hu'`. Use `⟨Q.map (algebraMap T Ω), ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs d`.

Rewrite using `[Polynomial.coeff_map]`. Conclude with `(IntermediateField.mem_fixedField_iff H.toSubgroup _).1 (Q.coeff d).2 s hs`. Rewrite using `[Polynomial.eval_map_algebraMap]`. Conclude with `hQ`.
-/
theorem exists_polynomial_closedSubgroup_fixed_eval_eq {F Ω : Type*} [Field F] [Field Ω]
    [Algebra F Ω] [IsGalois F Ω] (H : ClosedSubgroup (Ω ≃ₐ[F] Ω)) (ζ u : Ω)
    (h : ∀ s ∈ H.toSubgroup, s ζ = ζ → s u = u) :
    ∃ P : Polynomial Ω, (∀ s ∈ H.toSubgroup, ∀ d, s (P.coeff d) = P.coeff d) ∧
      P.eval ζ = u := by
  classical
  let T : IntermediateField F Ω := IntermediateField.fixedField H.toSubgroup
  have hT : T.fixingSubgroup = H.toSubgroup := InfiniteGalois.fixingSubgroup_fixedField H
  let E : IntermediateField F Ω :=
    (IntermediateField.adjoin T ({ζ} : Set Ω)).restrictScalars F
  have hu : u ∈ E := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro s hs
    rw [IntermediateField.mem_fixingSubgroup_iff] at hs
    refine h s ?_ (hs ζ (IntermediateField.mem_adjoin_simple_self T ζ))
    have : s ∈ T.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact hs x ((IntermediateField.adjoin T ({ζ} : Set Ω)).algebraMap_mem ⟨x, hx⟩)
    rw [hT] at this
    exact this
  have hint : IsIntegral T ζ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := F) ζ).isIntegral.tower_top
  have hu' : u ∈ (IntermediateField.adjoin T ({ζ} : Set Ω)).toSubalgebra := hu
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hu'
  obtain ⟨Q, hQ⟩ := hu'
  refine ⟨Q.map (algebraMap T Ω), ?_, ?_⟩
  · intro s hs d
    rw [Polynomial.coeff_map]
    exact (IntermediateField.mem_fixedField_iff H.toSubgroup _).1 (Q.coeff d).2 s hs
  · rw [Polynomial.eval_map_algebraMap]
    exact hQ

/- English proof (translation)
The claim follows from `haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω exists_polynomial_closedSubgroup_fixed_eval_eq ⟨Ine (F := ℚ) A, isClosed_Ine (F := ℚ) A⟩ ζ u h`.
-/
theorem exists_polynomial_inertia_fixed_eval_eq (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (ζ u : Ω)
    (h : ∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s u = u) :
    ∃ P : Polynomial Ω, (∀ s ∈ Ine (F := ℚ) A, ∀ d, s (P.coeff d) = P.coeff d) ∧
      P.eval ζ = u :=
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  exists_polynomial_closedSubgroup_fixed_eval_eq
    ⟨Ine (F := ℚ) A, isClosed_Ine (F := ℚ) A⟩ ζ u h

end GlobalTheory
