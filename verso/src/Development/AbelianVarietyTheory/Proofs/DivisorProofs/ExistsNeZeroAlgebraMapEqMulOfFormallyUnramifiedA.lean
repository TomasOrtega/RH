import Mathlib

open Algebra

namespace GlobalTheory

/- English proof (translation)
Introduce `P D _ _ _ _ _ _ _ f hf`. Distinguish the cases in `hinj : Function.Injective (algebraMap P D)`. Use `swap`. Rewrite `hinj` using `[injective_iff_map_eq_zero] at hinj push_neg`. Take `⟨Q, hQ, hQ0⟩` from `hinj`.

Conclude with `⟨Q, hQ0, 0, by rw [hQ, mul_zero]⟩`. Set `M` to `nonZeroDivisors P`. Set `K` to `FractionRing P`. Set `S` to `Algebra.algebraMapSubmonoid D M`. Set `L` to `Localization S`.

Use `letI : Algebra K L := localizationAlgebra M D`. Use `haveI : IsScalarTower P K L := inferInstance`. Establish `hS : S ≤ nonZeroDivisors D`. Introduce `x hx`. Take `⟨q, hq, rfl⟩` from `hx`.

Conclude with `mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hq))`. Use `haveI : IsDomain L := IsLocalization.isDomain_localization hS`. Establish `hDL : Function.Injective (algebraMap D L)` using `IsLocalization.injective L hS`. Use `haveI : IsLocalization (M.map (algebraMap P D)) L := inferInstanceAs (IsLocalization S L)`. Use `haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.localization_map M (S := D)`.

Use `haveI : Algebra.EssFiniteType D L := Algebra.EssFiniteType.of_isLocalization L S`. Use `haveI : Algebra.EssFiniteType P L := Algebra.EssFiniteType.comp P D L`. Use `haveI : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_comp P K L`. Use `haveI : Module.Finite K L := Algebra.FormallyUnramified.finite_of_free K L`. Establish `hint : IsIntegral K (algebraMap D L f)` using `Algebra.IsIntegral.isIntegral _`.

Establish `hne : algebraMap D L f ≠ 0` using `(map_ne_zero_iff _ hDL).2 hf`. Take `⟨u, hu⟩` from `hint.isUnit hne`. Establish `hy : algebraMap D L f * ↑u⁻¹ = 1` using `by rw [← hu]; exact u.mul_inv`. Take `⟨⟨d, s⟩, hds⟩` from `IsLocalization.surj S (↑u⁻¹ : L)`. Take `⟨q, hq, hqs⟩` from `s.2`.

Use `⟨q, nonZeroDivisors.ne_zero hq, d, ?_⟩` and prove the remaining obligations. Apply `hDL` to reduce the goal to its premises. Simplify using `only at hds`. Rewrite using `[map_mul, ← hds, ← mul_assoc, hy, one_mul, hqs]`.
-/
theorem exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified :
    ∀ (P D : Type) [CommRing P] [IsDomain P] [CommRing D] [IsDomain D] [Algebra P D]
      [Algebra.FiniteType P D] [Algebra.FormallyUnramified P D] (f : D), f ≠ 0 →
      ∃ Q : P, Q ≠ 0 ∧ ∃ d : D, algebraMap P D Q = f * d := by
  intro P D _ _ _ _ _ _ _ f hf
  by_cases hinj : Function.Injective (algebraMap P D)
  swap
  · rw [injective_iff_map_eq_zero] at hinj
    push_neg at hinj
    obtain ⟨Q, hQ, hQ0⟩ := hinj
    exact ⟨Q, hQ0, 0, by rw [hQ, mul_zero]⟩
  let M := nonZeroDivisors P
  let K := FractionRing P
  let S := Algebra.algebraMapSubmonoid D M
  let L := Localization S
  letI : Algebra K L := localizationAlgebra M D
  haveI : IsScalarTower P K L := inferInstance
  have hS : S ≤ nonZeroDivisors D := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hq))
  haveI : IsDomain L := IsLocalization.isDomain_localization hS
  have hDL : Function.Injective (algebraMap D L) := IsLocalization.injective L hS
  haveI : IsLocalization (M.map (algebraMap P D)) L := inferInstanceAs (IsLocalization S L)
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.localization_map M (S := D)
  haveI : Algebra.EssFiniteType D L := Algebra.EssFiniteType.of_isLocalization L S
  haveI : Algebra.EssFiniteType P L := Algebra.EssFiniteType.comp P D L
  haveI : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_comp P K L
  haveI : Module.Finite K L := Algebra.FormallyUnramified.finite_of_free K L
  have hint : IsIntegral K (algebraMap D L f) := Algebra.IsIntegral.isIntegral _
  have hne : algebraMap D L f ≠ 0 := (map_ne_zero_iff _ hDL).2 hf
  obtain ⟨u, hu⟩ := hint.isUnit hne
  have hy : algebraMap D L f * ↑u⁻¹ = 1 := by rw [← hu]; exact u.mul_inv
  obtain ⟨⟨d, s⟩, hds⟩ := IsLocalization.surj S (↑u⁻¹ : L)
  obtain ⟨q, hq, hqs⟩ := s.2
  refine ⟨q, nonZeroDivisors.ne_zero hq, d, ?_⟩
  apply hDL
  simp only at hds
  rw [map_mul, ← hds, ← mul_assoc, hy, one_mul, hqs]

end GlobalTheory
