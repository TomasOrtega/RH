import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGF

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S Polynomial
open ValuativeRel

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fl_cj_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.9] at hx ⊢
  exact hx.map ((L.1 : E →ₐ[F] E).restrictScalars 𝒪[F])

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem fl_mem_int {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {a : F} (ha : algebraMap F E a ∈ L.O) : a ∈ 𝒪[F] := by
  have h1 : IsIntegral 𝒪[F] (algebraMap F E a) := (L.9 _).1 ha
  have h2 : IsIntegral 𝒪[F] a := (isIntegral_algebraMap_iff hinj).1 h1
  exact (Valuation.integer.integers _).mem_of_integral h2

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem fl_int_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (a : 𝒪[F]) : algebraMap F E a ∈ L.O := by
  rw [L.9]
  have h : IsIntegral 𝒪[F] (algebraMap 𝒪[F] E a) := isIntegral_algebraMap
  rwa [IsScalarTower.algebraMap_apply 𝒪[F] F E] at h

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem fl_fix_int {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {y : E} (hy : y ∈ L.O) (hc : L.cj y = y) : ∃ a : 𝒪[F], algebraMap F E a = y := by
  obtain ⟨a, ha⟩ := (L.3 y).1 hc
  have haO : a ∈ 𝒪[F] := fl_mem_int L hinj (ha ▸ hy)
  exact ⟨⟨a, haO⟩, ha⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem fl_norm {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {x : E} (hx : x ∈ L.O) : ∃ n : 𝒪[F], algebraMap F E n = x * L.cj x := by
  refine fl_fix_int L hinj (L.O.mul_mem hx (fl_cj_mem L hx)) ?_
  rw [map_mul, L.2, mul_comm]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem fl_trace {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {x : E} (hx : x ∈ L.O) : ∃ t : 𝒪[F], algebraMap F E t = x + L.cj x := by
  refine fl_fix_int L hinj (L.O.add_mem hx (fl_cj_mem L hx)) ?_
  rw [map_add, L.2, add_comm]

/- English proof (translation)
Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem fl_den_F {F : Type} [Field F] [ValuativeRel F] (a : F) :
    ∃ c : 𝒪[F], c ≠ 0 ∧ (c : F) * a ∈ 𝒪[F] := by
  by_cases ha : a ∈ 𝒪[F]
  · exact ⟨1, one_ne_zero, by simpa using ha⟩
  · have ha0 : a ≠ 0 := by
      rintro rfl
      exact ha (zero_mem _)
    have hv : 1 < ValuativeRel.valuation F a := by
      rw [Valuation.mem_integer_iff, not_le] at ha
      exact ha
    have hmem : a⁻¹ ∈ 𝒪[F] := by
      rw [Valuation.mem_integer_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ hv.le
    refine ⟨⟨a⁻¹, hmem⟩, ?_, ?_⟩
    · intro h
      have h' := congrArg Subtype.val h
      simp [ha0] at h'
    · simp [ha0]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem fl_den {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (x : E) :
    ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ L.O := by
  obtain ⟨t, ht⟩ := (L.3 (x + L.cj x)).1 (by rw [map_add, L.2, add_comm])
  obtain ⟨m, hm⟩ := (L.3 (x * L.cj x)).1 (by rw [map_mul, L.2, mul_comm])
  obtain ⟨c1, hc1, ht1⟩ := fl_den_F t
  obtain ⟨c2, hc2, hm2⟩ := fl_den_F m
  refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
  rw [L.9]
  have key : ∀ z : 𝒪[F], algebraMap 𝒪[F] E z = algebraMap F E (z : F) :=
    fun z => IsScalarTower.algebraMap_apply 𝒪[F] F E z
  have hx2 : x * x = algebraMap F E t * x - algebraMap F E m := by rw [ht, hm]; ring
  refine ⟨X ^ 2 - C (c2 * ⟨(c1 : F) * t, ht1⟩) * X + C (c1 ^ 2 * c2 * ⟨(c2 : F) * m, hm2⟩), by monicity!, ?_⟩
  simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X, key]
  push_cast
  try simp only [map_mul, map_pow]
  linear_combination (algebraMap F E c1 * algebraMap F E c2) ^ 2 * hx2

end PI.UnitaryGroupMassFormula.CntFormula
