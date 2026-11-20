import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Use `((HeightOneSpectrum.Support.finite (𝓞 F) (x : F)).union (HeightOneSpectrum.Support.finite (𝓞 F) ((x : F)⁻¹))).subset ?_` and prove the remaining obligations. Introduce `v hv`. Establish `hv' : v.valuation F (x : F) ≠ 1` using `hv`. Establish `h0 : v.valuation F (x : F) ≠ 0`. Rewrite using `[Ne, map_eq_zero]`.

Conclude with `x.ne_zero`. Break down `lt_or_gt_of_ne hv' with h | h` into its components or cases. Use `right show 1 < v.valuation F ((x : F)⁻¹)`. Rewrite using `[map_inv₀]`. Conclude with `one_lt_inv₀ (zero_lt_iff.mpr h0) |>.mpr h`.

Use `left`. Conclude with `h`.
-/
theorem finite_valuation_ne_one (F : Type) [Field F] [NumberField F] (x : Fˣ) :
    {v : HeightOneSpectrum (𝓞 F) | v.valuation F (x : F) ≠ 1}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) (x : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((x : F)⁻¹))).subset ?_
  intro v hv
  have hv' : v.valuation F (x : F) ≠ 1 := hv
  have h0 : v.valuation F (x : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact x.ne_zero
  rcases lt_or_gt_of_ne hv' with h | h
  · right
    show 1 < v.valuation F ((x : F)⁻¹)
    rw [map_inv₀]
    exact one_lt_inv₀ (zero_lt_iff.mpr h0) |>.mpr h
  · left
    exact h

/- English proof (translation)
Introduce `F _ _ X S₀`. Establish `hT : (⋃ x ∈ X, {v : HeightOneSpectrum (𝓞 F) | v.valuation F (x : F) ≠ 1}).Finite` using `X.finite_toSet.biUnion fun x _ => finite_valuation_ne_one F x`. Use `⟨S₀ ∪ hT.toFinset, Finset.subset_union_left, ?_⟩` and prove the remaining obligations. Introduce `S' hS' x hx`. Rewrite using `[mem_sUnits]`.

Introduce `v hv`. Assume the negation of the conclusion as `h`. Apply `hv` to reduce the goal to its premises. Apply `hS'` to reduce the goal to its premises. Apply `Finset.mem_union_right` to reduce the goal to its premises.

Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `Set.mem_biUnion hx h`.
-/
theorem exists_superset_mem_sUnits :
    ∀ (F : Type) [Field F] [NumberField F] (X : Finset Fˣ)
      (S₀ : Finset (HeightOneSpectrum (𝓞 F))),
      ∃ S, S₀ ⊆ S ∧ ∀ S', S ⊆ S' → ∀ x ∈ X, x ∈ sUnits F S' := by
  intro F _ _ X S₀
  classical
  have hT : (⋃ x ∈ X, {v : HeightOneSpectrum (𝓞 F) | v.valuation F (x : F) ≠ 1}).Finite :=
    X.finite_toSet.biUnion fun x _ => finite_valuation_ne_one F x
  refine ⟨S₀ ∪ hT.toFinset, Finset.subset_union_left, ?_⟩
  intro S' hS' x hx
  rw [mem_sUnits]
  intro v hv
  by_contra h
  apply hv
  apply hS'
  apply Finset.mem_union_right
  rw [Set.Finite.mem_toFinset]
  exact Set.mem_biUnion hx h

end GlobalTheory.QNorm
