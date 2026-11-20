import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGF

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S Polynomial
open ValuativeRel

/- English proof (translation)
Rewrite `hx`, the goal using `[L.9]`. Conclude with `hx.map ((L.1 : E →ₐ[F] E).restrictScalars 𝒪[F])`.
-/
theorem fl_cj_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.9] at hx ⊢
  exact hx.map ((L.1 : E →ₐ[F] E).restrictScalars 𝒪[F])

/- English proof (translation)
Establish `h1 : IsIntegral 𝒪[F] (algebraMap F E a)` using `(L.9 _).1 ha`. Establish `h2 : IsIntegral 𝒪[F] a` using `(isIntegral_algebraMap_iff hinj).1 h1`. Conclude with `(Valuation.integer.integers _).mem_of_integral h2`.
-/
theorem fl_mem_int {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {a : F} (ha : algebraMap F E a ∈ L.O) : a ∈ 𝒪[F] := by
  have h1 : IsIntegral 𝒪[F] (algebraMap F E a) := (L.9 _).1 ha
  have h2 : IsIntegral 𝒪[F] a := (isIntegral_algebraMap_iff hinj).1 h1
  exact (Valuation.integer.integers _).mem_of_integral h2

/- English proof (translation)
Rewrite using `[L.9]`. Establish `h : IsIntegral 𝒪[F] (algebraMap 𝒪[F] E a)` using `isIntegral_algebraMap`. Rewrite `h` using `[IsScalarTower.algebraMap_apply 𝒪[F] F E]`. Then use the resulting hypothesis.
-/
theorem fl_int_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (a : 𝒪[F]) : algebraMap F E a ∈ L.O := by
  rw [L.9]
  have h : IsIntegral 𝒪[F] (algebraMap 𝒪[F] E a) := isIntegral_algebraMap
  rwa [IsScalarTower.algebraMap_apply 𝒪[F] F E] at h

/- English proof (translation)
Take `⟨a, ha⟩` from `(L.3 y).1 hc`. Establish `haO : a ∈ 𝒪[F]` using `fl_mem_int L hinj (ha ▸ hy)`. Conclude with `⟨⟨a, haO⟩, ha⟩`.
-/
theorem fl_fix_int {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {y : E} (hy : y ∈ L.O) (hc : L.cj y = y) : ∃ a : 𝒪[F], algebraMap F E a = y := by
  obtain ⟨a, ha⟩ := (L.3 y).1 hc
  have haO : a ∈ 𝒪[F] := fl_mem_int L hinj (ha ▸ hy)
  exact ⟨⟨a, haO⟩, ha⟩

/- English proof (translation)
Use `fl_fix_int L hinj (L.O.mul_mem hx (fl_cj_mem L hx)) ?_` and prove the remaining obligations. Rewrite using `[map_mul, L.2, mul_comm]`.
-/
theorem fl_norm {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {x : E} (hx : x ∈ L.O) : ∃ n : 𝒪[F], algebraMap F E n = x * L.cj x := by
  refine fl_fix_int L hinj (L.O.mul_mem hx (fl_cj_mem L hx)) ?_
  rw [map_mul, L.2, mul_comm]

/- English proof (translation)
Use `fl_fix_int L hinj (L.O.add_mem hx (fl_cj_mem L hx)) ?_` and prove the remaining obligations. Rewrite using `[map_add, L.2, add_comm]`.
-/
theorem fl_trace {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {x : E} (hx : x ∈ L.O) : ∃ t : 𝒪[F], algebraMap F E t = x + L.cj x := by
  refine fl_fix_int L hinj (L.O.add_mem hx (fl_cj_mem L hx)) ?_
  rw [map_add, L.2, add_comm]

/- English proof (translation)
Distinguish the cases in `ha : a ∈ 𝒪[F]`. Conclude with `⟨1, one_ne_zero, by simpa using ha⟩`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `ha (zero_mem _)`.

Establish `hv : 1 < ValuativeRel.valuation F a`. Rewrite `ha` using `[Valuation.mem_integer_iff, not_le]`. Conclude with `ha`. Establish `hmem : a⁻¹ ∈ 𝒪[F]`. Rewrite using `[Valuation.mem_integer_iff, map_inv₀]`.

Conclude with `inv_le_one_of_one_le₀ hv.le`. Use `⟨⟨a⁻¹, hmem⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `h'` using `congrArg Subtype.val h`. Simplify using `[ha0] at h'`.

Simplify using `[ha0]`.
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
Take `⟨t, ht⟩` from `(L.3 (x + L.cj x)).1 (by rw [map_add, L.2, add_comm])`. Take `⟨m, hm⟩` from `(L.3 (x * L.cj x)).1 (by rw [map_mul, L.2, mul_comm])`. Take `⟨c1, hc1, ht1⟩` from `fl_den_F t`. Take `⟨c2, hc2, hm2⟩` from `fl_den_F m`. Use `⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩` and prove the remaining obligations.

Rewrite using `[L.9]`. Establish `key : ∀ z : 𝒪[F], algebraMap 𝒪[F] E z = algebraMap F E (z : F)` using `fun z => IsScalarTower.algebraMap_apply 𝒪[F] F E z`. Establish `hx2 : x * x = algebraMap F E t * x - algebraMap F E m` using `by rw [ht, hm]; ring`. Use `⟨X ^ 2 - C (c2 * ⟨(c1 : F) * t, ht1⟩) * X + C (c1 ^ 2 * c2 * ⟨(c2 : F) * m, hm2⟩), by monicity!, ?_⟩` and prove the remaining obligations. Simplify using `only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X, key]`.

Use `push_cast`. Apply the tactic sequence `try simp only [map_mul, map_pow]`. Take the linear combination `(algebraMap F E c1 * algebraMap F E c2) ^ 2 * hx2`.
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
