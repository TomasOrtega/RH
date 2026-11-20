import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F] {d : ℕ}

/- English proof (translation)
Introduce `_ _ h` and use `Units.ext (Matrix.toLin'.injective h)`.
-/
theorem extZero_toLin_injective :
    Function.Injective fun x : GL (Fin d) F => Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) := fun _ _ h => Units.ext (Matrix.toLin'.injective h)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨u, hu⟩` from `LinearMap.isUnit_toMatrix'_iff.mpr h`. Conclude with `⟨u, by rw [hu, Matrix.toLin'_toMatrix']⟩`. Introduce and unpack `⟨x, rfl⟩`.

Conclude with `Matrix.isUnit_toLin'_iff.mpr x.isUnit`.
-/
theorem extZero_isUnit_iff (g : Module.End F (Fin d → F)) :
    IsUnit g ↔ ∃ x : GL (Fin d) F, Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) = g := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := LinearMap.isUnit_toMatrix'_iff.mpr h
    exact ⟨u, by rw [hu, Matrix.toLin'_toMatrix']⟩
  · rintro ⟨x, rfl⟩
    exact Matrix.isUnit_toLin'_iff.mpr x.isUnit

/- English proof (translation)
Unfold `extZero`. Establish `hs : {y : GL (Fin d) F | Matrix.toLin' (y : Matrix (Fin d) (Fin d) F) = Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)} = {x}`. Use extensionality with `y`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_singleton_iff]`. Conclude with `extZero_toLin_injective.eq_iff`.

Rewrite using `[hs, finsum_mem_singleton]`.
-/
theorem extZero_toLin (χ : GL (Fin d) F → ℂ) (x : GL (Fin d) F) :
    extZero χ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) = χ x := by
  unfold extZero
  have hs : {y : GL (Fin d) F | Matrix.toLin' (y : Matrix (Fin d) (Fin d) F) =
      Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)} = {x} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact extZero_toLin_injective.eq_iff
  rw [hs, finsum_mem_singleton]

/- English proof (translation)
Unfold `extZero`. Establish `hs : {x : GL (Fin d) F | Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) = g} = ∅`. Use extensionality with `x`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `rfl`.

Conclude with `hg ((extZero_isUnit_iff _).mpr ⟨x, rfl⟩)`. Rewrite using `[hs, finsum_mem_empty]`.
-/
theorem extZero_of_not_isUnit (χ : GL (Fin d) F → ℂ) (g : Module.End F (Fin d → F))
    (hg : ¬ IsUnit g) : extZero χ g = 0 := by
  unfold extZero
  have hs : {x : GL (Fin d) F | Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) = g} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro rfl
    exact hg ((extZero_isUnit_iff _).mpr ⟨x, rfl⟩)
  rw [hs, finsum_mem_empty]

/- English proof (translation)
Unfold `ipGL`. Establish `hs : {g : Module.End F (Fin d → F) | IsUnit g} = Set.range fun x : GL (Fin d) F => Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)`. Use extensionality with `g`. Conclude with `extZero_isUnit_iff g`. Rewrite using `[hs, finsum_mem_range extZero_toLin_injective]`.
-/
theorem ipGL_eq_finsum_GL (φ φ' : Module.End F (Fin d → F) → ℂ) :
    ipGL φ φ' = ∑ᶠ x : GL (Fin d) F, φ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) *
      star (φ' (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))) := by
  unfold ipGL
  have hs : {g : Module.End F (Fin d → F) | IsUnit g} =
      Set.range fun x : GL (Fin d) F => Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) := by
    ext g
    exact extZero_isUnit_iff g
  rw [hs, finsum_mem_range extZero_toLin_injective]

/- English proof (translation)
Introduce `e g`. Set `Φ : GL (Fin d) F ≃* (Module.End F (Fin d → F))ˣ` to `Units.mapEquiv (Matrix.toLinAlgEquiv' (R := F) (n := Fin d)).toMulEquiv`. Establish `hcoe : ∀ x : GL (Fin d) F, ((Φ x : (Module.End F (Fin d → F))ˣ) : Module.End F (Fin d → F)) = Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)`. Introduce `x`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Matrix.toLinAlgEquiv' (x : Matrix (Fin d) (Fin d) F) v = _`. Rewrite using `[Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]`. Set `E : (Module.End F (Fin d → F))ˣ` to `⟨e.toLinearMap, e.symm.toLinearMap, LinearMap.ext fun v => e.apply_symm_apply v, LinearMap.ext fun v => e.symm_apply_apply v⟩`. Establish `hconj : ∀ f : Module.End F (Fin d → F), e.conj f = (E : Module.End F (Fin d → F)) * f * ((E⁻¹ : (Module.End F (Fin d → F))ˣ) : Module.End F (Fin d → F))`. Introduce `f`.

Conclude with `LinearMap.ext fun v => rfl`. Distinguish the cases in `hg : IsUnit g`. Take `⟨y, rfl⟩` from `(extZero_isUnit_iff g).mp hg`. Establish `hy : e.conj (Matrix.toLin' (y : Matrix (Fin d) (Fin d) F)) = Matrix.toLin' ((Φ.symm E * y * (Φ.symm E)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)`. Rewrite using `[← hcoe (Φ.symm E * y * (Φ.symm E)⁻¹), map_mul, map_mul, map_inv, Φ.apply_symm_apply, Units.val_mul, Units.val_mul, hcoe y, hconj]`.

Rewrite using `[hy, extZero_toLin, extZero_toLin]`. Simplify using `using hχ y (Φ.symm E)⁻¹`. Establish `hg' : ¬ IsUnit (e.conj g)`. Rewrite using `[hconj, Units.isUnit_mul_units, Units.isUnit_units_mul]`. Conclude with `hg`.

Rewrite using `[extZero_of_not_isUnit χ _ hg', extZero_of_not_isUnit χ _ hg]`.
-/
theorem isClassFn_extZero (χ : GL (Fin d) F → ℂ)
    (hχ : ∀ g x : GL (Fin d) F, χ (x⁻¹ * g * x) = χ g) : IsClassFn (extZero χ) := by
  intro e g

  let Φ : GL (Fin d) F ≃* (Module.End F (Fin d → F))ˣ :=
    Units.mapEquiv (Matrix.toLinAlgEquiv' (R := F) (n := Fin d)).toMulEquiv
  have hcoe : ∀ x : GL (Fin d) F, ((Φ x : (Module.End F (Fin d → F))ˣ) : Module.End F (Fin d → F)) =
      Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) := by
    intro x
    refine LinearMap.ext fun v => ?_
    change Matrix.toLinAlgEquiv' (x : Matrix (Fin d) (Fin d) F) v = _
    rw [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]

  let E : (Module.End F (Fin d → F))ˣ :=
    ⟨e.toLinearMap, e.symm.toLinearMap, LinearMap.ext fun v => e.apply_symm_apply v,
      LinearMap.ext fun v => e.symm_apply_apply v⟩
  have hconj : ∀ f : Module.End F (Fin d → F),
      e.conj f = (E : Module.End F (Fin d → F)) * f * ((E⁻¹ : (Module.End F (Fin d → F))ˣ) :
        Module.End F (Fin d → F)) := by
    intro f
    exact LinearMap.ext fun v => rfl
  by_cases hg : IsUnit g
  · obtain ⟨y, rfl⟩ := (extZero_isUnit_iff g).mp hg
    have hy : e.conj (Matrix.toLin' (y : Matrix (Fin d) (Fin d) F)) =
        Matrix.toLin' ((Φ.symm E * y * (Φ.symm E)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
      rw [← hcoe (Φ.symm E * y * (Φ.symm E)⁻¹), map_mul, map_mul, map_inv, Φ.apply_symm_apply, Units.val_mul, Units.val_mul,
        hcoe y, hconj]
    rw [hy, extZero_toLin, extZero_toLin]
    simpa using hχ y (Φ.symm E)⁻¹
  · have hg' : ¬ IsUnit (e.conj g) := by
      rw [hconj, Units.isUnit_mul_units, Units.isUnit_units_mul]
      exact hg
    rw [extZero_of_not_isUnit χ _ hg', extZero_of_not_isUnit χ _ hg]

/- English proof (translation)
Introduce `F _ _ d χ`. Conclude with `⟨fun x => extZero_toLin χ x, fun g hg => extZero_of_not_isUnit χ g hg, fun φ φ' => ipGL_eq_finsum_GL φ φ', fun h => isClassFn_extZero χ h⟩`.
-/
theorem extZero_spec : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ), (∀ x : GL (Fin d) F, extZero χ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) = χ x) ∧ (∀ g, ¬ IsUnit g → extZero χ g = 0) ∧ (∀ φ φ' : Module.End F (Fin d → F) → ℂ, ipGL φ φ' = ∑ᶠ x : GL (Fin d) F, φ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) * star (φ' (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)))) ∧ ((∀ g x : GL (Fin d) F, χ (x⁻¹ * g * x) = χ g) → IsClassFn (extZero χ)) := by
  intro F _ _ d χ
  exact ⟨fun x => extZero_toLin χ x, fun g hg => extZero_of_not_isUnit χ g hg,
    fun φ φ' => ipGL_eq_finsum_GL φ φ', fun h => isClassFn_extZero χ h⟩

end GlobalTheory.CuspGL
