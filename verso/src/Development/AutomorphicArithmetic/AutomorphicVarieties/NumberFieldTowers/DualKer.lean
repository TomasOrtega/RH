import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.QzInj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

/- English proof (translation)
Introduce `l _ M _ _ M' _ _ T`. Establish `hI` using `PropA.qzInj l`. Use `⟨?_, fun p g => ?_⟩` and prove the remaining obligations. Use extensionality with `f`. Rewrite using `[LinearMap.mem_range, LinearMap.mem_ker]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`. Use extensionality with `⟨x, hx⟩`. Simplify using `only [LinearMap.lcomp_apply, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply]`. Rewrite using `[LinearMap.mem_ker.mp hx, map_zero]`.

Introduce `hf`. Establish `hle : LinearMap.ker T ≤ LinearMap.ker f`. Introduce `x hx`. Use `LinearMap.congr_fun hf ⟨x, hx⟩` as an intermediate fact. Simplify using `using this`.

Set `g0 : LinearMap.range T →ₗ[ℤ_[l]] QZ l` to `((LinearMap.ker T).liftQ f hle).comp (LinearMap.quotKerEquivRange T).symm.toLinearMap`. Take `⟨h, hh⟩` from `hI.out (LinearMap.range T).subtype Subtype.val_injective g0`. Use `⟨h, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [LinearMap.lcomp_apply, LinearMap.comp_apply]`.

Use `hh ⟨T x, LinearMap.mem_range_self T x⟩` as an intermediate fact. Simplify using `only [Submodule.subtype_apply] at this`. Rewrite using `[this]`. Simplify using `[g0, LinearMap.quotKerEquivRange_symm_apply_image]`. Take `⟨h, hh⟩` from `hI.out p.subtype Subtype.val_injective g`.

Use `⟨h, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Simplify using `using hh x`.
-/
theorem UpperTheory.V.Tower.dualKer :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (M' : Type) [AddCommGroup M'] [Module ℤ_[l] M'] (T : M →ₗ[ℤ_[l]] M'),
        LinearMap.range (LinearMap.lcomp ℤ_[l] (QZ l) T) = LinearMap.ker (LinearMap.lcomp ℤ_[l] (QZ l) (LinearMap.ker T).subtype) ∧
        ∀ p : Submodule ℤ_[l] M, Function.Surjective (LinearMap.lcomp ℤ_[l] (QZ l) p.subtype) := by
  intro l _ M _ _ M' _ _ T
  have hI := PropA.qzInj l
  refine ⟨?_, fun p g => ?_⟩
  · ext f
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨g, rfl⟩
      ext ⟨x, hx⟩
      simp only [LinearMap.lcomp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearMap.zero_apply]
      rw [LinearMap.mem_ker.mp hx, map_zero]
    · intro hf
      have hle : LinearMap.ker T ≤ LinearMap.ker f := by
        intro x hx
        have := LinearMap.congr_fun hf ⟨x, hx⟩
        simpa using this
      let g0 : LinearMap.range T →ₗ[ℤ_[l]] QZ l :=
        ((LinearMap.ker T).liftQ f hle).comp (LinearMap.quotKerEquivRange T).symm.toLinearMap
      obtain ⟨h, hh⟩ := hI.out (LinearMap.range T).subtype Subtype.val_injective g0
      refine ⟨h, ?_⟩
      ext x
      simp only [LinearMap.lcomp_apply, LinearMap.comp_apply]
      have := hh ⟨T x, LinearMap.mem_range_self T x⟩
      simp only [Submodule.subtype_apply] at this
      rw [this]
      simp [g0, LinearMap.quotKerEquivRange_symm_apply_image]
  · obtain ⟨h, hh⟩ := hI.out p.subtype Subtype.val_injective g
    refine ⟨h, ?_⟩
    ext x
    simpa using hh x
