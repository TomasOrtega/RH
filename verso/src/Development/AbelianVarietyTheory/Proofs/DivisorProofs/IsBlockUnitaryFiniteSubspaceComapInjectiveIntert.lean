import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

/- English proof (translation)
Establish `key : ∀ U' : Submodule ℂ M', UnitOn s F' U' → UnitOn s F (U'.comap f)`. Introduce and unpack `U' ⟨hfin, hst, ip', hs, hp, hadj⟩`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hinj : Function.Injective (f.restrict (p` using `U'.comap f) (q := U') (fun x hx => hx)) := by`. Introduce `x y hxy`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `hf` to reduce the goal to its premises. Use `congrArg Subtype.val hxy` as an intermediate fact. Simplify using `using this`. Conclude with `Module.Finite.of_injective _ hinj`.

Introduce `a b hab u hu show f (F a b u) ∈ U'`. Rewrite using `[hF a b hab]`. Conclude with `hst a b hab (f u) hu`. Use `⟨(ip'.comp f).compl₂ f, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx y hy`.

Simplify using `using hs (f x) hx (f y) hy`. Introduce `x hx hx0`. Establish `: f x ≠ 0` using `fun h => hx0 (hf (by rw [h, map_zero]))`. Simplify using `using hp (f x) hx this`. Introduce `a b hab x hx y hy`.

Establish `hba : s b = s a` using `hab.symm`. Simplify using `only [LinearMap.compl₂_apply, LinearMap.comp_apply]`. Rewrite using `[hF a b hab, hF b a hba]`. Conclude with `hadj a b hab (f x) hx (f y) hy`. Use `⟨key, ?_⟩` and prove the remaining obligations.

Introduce `hL t`. Take `⟨U', ht, hU'⟩` from `hL (t.image f)`. Use `⟨U'.comap f, ?_, key U' hU'⟩` and prove the remaining obligations. Introduce `x hx`. Conclude with `ht (f x) (Finset.mem_image_of_mem f hx)`.
-/
theorem unitOn_comap_locU (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M) (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M')
    (f : M →ₗ[ℂ] M') (hf : Function.Injective f) (hF : ∀ a b, s a = s b → ∀ x, f (F a b x) = F' a b (f x)) :
    (∀ U' : Submodule ℂ M', UnitOn s F' U' → UnitOn s F (U'.comap f)) ∧ (LocU s F' → LocU s F) := by
  have key : ∀ U' : Submodule ℂ M', UnitOn s F' U' → UnitOn s F (U'.comap f) := by
    rintro U' ⟨hfin, hst, ip', hs, hp, hadj⟩
    refine ⟨?_, ?_, ?_⟩
    · have hinj : Function.Injective (f.restrict (p := U'.comap f) (q := U') (fun x hx => hx)) := by
        intro x y hxy
        apply Subtype.ext
        apply hf
        have := congrArg Subtype.val hxy
        simpa using this
      exact Module.Finite.of_injective _ hinj
    · intro a b hab u hu
      show f (F a b u) ∈ U'
      rw [hF a b hab]
      exact hst a b hab (f u) hu
    · refine ⟨(ip'.comp f).compl₂ f, ?_, ?_, ?_⟩
      · intro x hx y hy
        simpa using hs (f x) hx (f y) hy
      · intro x hx hx0
        have : f x ≠ 0 := fun h => hx0 (hf (by rw [h, map_zero]))
        simpa using hp (f x) hx this
      · intro a b hab x hx y hy
        have hba : s b = s a := hab.symm
        simp only [LinearMap.compl₂_apply, LinearMap.comp_apply]
        rw [hF a b hab, hF b a hba]
        exact hadj a b hab (f x) hx (f y) hy
  refine ⟨key, ?_⟩
  intro hL t
  classical
  obtain ⟨U', ht, hU'⟩ := hL (t.image f)
  refine ⟨U'.comap f, ?_, key U' hU'⟩
  intro x hx
  exact ht (f x) (Finset.mem_image_of_mem f hx)

end GlobalTheory.HoweR
