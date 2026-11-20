import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

namespace GlobalTheory.AntiInvFrac

/- English proof (translation)
Introduce `E _ _ _ M ξ hξ hbξ hM hU`. Set `f : FR E →ₗ[OF E] E` to `{ toFun := fun a ↦ (a : E) * ξ map_add' := fun a b ↦ by push_cast; ring map_smul' := fun r a ↦ by`. Simplify using `only [RingHom.id_apply, Algebra.smul_def]`. Rewrite using `[IsScalarTower.algebraMap_apply (OF E) (FR E) E]`. Rewrite using `[show ∀ x : FR E, algebraMap (FR E) E x = (x : E) from fun _ ↦ rfl]`.

Use `push_cast`. Use `ring }`. Establish `hf : Function.Injective f` using `fun a b h ↦ by`. Establish `h' : (a : E) * ξ = (b : E) * ξ` using `h`. Conclude with `Subtype.ext (mul_right_cancel₀ hξ h')`.

Set `S : Submodule (OF E) (FR E)` to `M.comap f`. Establish `hle : M ≤ LinearMap.range f` using `fun m hm ↦ by`. Establish `hfix : bar (m / ξ) = m / ξ`. Simplify using `only [bar, map_div₀] at hbξ ⊢`. Rewrite using `[show IsCMField.complexConj E m = -m from hM m hm, hbξ, neg_div_neg_eq]`.

Use `⟨⟨m / ξ, (IsCMField.complexConj_eq_self_iff E _).1 hfix⟩, ?_⟩` and prove the remaining obligations. Use `show (m / ξ) * ξ = m`. Conclude with `div_mul_cancel₀ m hξ`. Establish `hmap : S.map f = M`. Rewrite using `[Submodule.map_comap_eq, inf_eq_right.2 hle]`.

Establish `hMfg : M.FG` using `Submodule.fg_of_isUnit hU`. Establish `hSfg : S.FG` using `Submodule.fg_of_fg_map_injective f hf (hmap ▸ hMfg)`. Establish `hM0 : M ≠ ⊥`. Introduce `h`. Establish `: IsUnit (0 : Submodule (OF E) E)` using `by rw [← Submodule.zero_eq_bot] at h; rw [← h]; exact hU`.

Conclude with `not_isUnit_zero this`. Establish `hS0 : S ≠ ⊥`. Introduce `h`. Apply `hM0` to reduce the goal to its premises. Rewrite using `[← hmap, h, Submodule.map_bot]`.

Set `I : FractionalIdeal (nonZeroDivisors (𝓞 (FR E))) (FR E)` to `⟨S, FractionalIdeal.isFractional_of_fg hSfg⟩`. Establish `hI : I ≠ 0`. Introduce `h`. Apply `hS0` to reduce the goal to its premises. Use `congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 (FR E))) (FR E) ↦ (J : Submodule (𝓞 (FR E)) (FR E))) h` as an intermediate fact.

Simplify `this` using `[I]`. Use `⟨Units.mk0 I hI, fun a ↦ ?_⟩` and prove the remaining obligations. Use `show a ∈ S ↔ _`. Both sides reduce to the same expression.
-/
theorem fracId_of_antiInv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : Submodule (OF E) E) (ξ : E), ξ ≠ 0 → bar ξ = -ξ →
    (∀ m ∈ M, bar m = -m) → IsUnit M → ∃ 𝔠 : FracId (FR E), ∀ a : FR E, a ∈ 𝔠.elt ↔ (a : E) * ξ ∈ M := by
  intro E _ _ _ M ξ hξ hbξ hM hU
  let f : FR E →ₗ[OF E] E :=
    { toFun := fun a ↦ (a : E) * ξ
      map_add' := fun a b ↦ by push_cast; ring
      map_smul' := fun r a ↦ by
        simp only [RingHom.id_apply, Algebra.smul_def]
        rw [IsScalarTower.algebraMap_apply (OF E) (FR E) E]
        rw [show ∀ x : FR E, algebraMap (FR E) E x = (x : E) from fun _ ↦ rfl]
        push_cast; ring }
  have hf : Function.Injective f := fun a b h ↦ by
    have h' : (a : E) * ξ = (b : E) * ξ := h
    exact Subtype.ext (mul_right_cancel₀ hξ h')
  let S : Submodule (OF E) (FR E) := M.comap f
  have hle : M ≤ LinearMap.range f := fun m hm ↦ by
    have hfix : bar (m / ξ) = m / ξ := by
      simp only [bar, map_div₀] at hbξ ⊢
      rw [show IsCMField.complexConj E m = -m from hM m hm, hbξ, neg_div_neg_eq]
    refine ⟨⟨m / ξ, (IsCMField.complexConj_eq_self_iff E _).1 hfix⟩, ?_⟩
    show (m / ξ) * ξ = m
    exact div_mul_cancel₀ m hξ
  have hmap : S.map f = M := by
    rw [Submodule.map_comap_eq, inf_eq_right.2 hle]
  have hMfg : M.FG := Submodule.fg_of_isUnit hU
  have hSfg : S.FG := Submodule.fg_of_fg_map_injective f hf (hmap ▸ hMfg)
  have hM0 : M ≠ ⊥ := by
    intro h
    have : IsUnit (0 : Submodule (OF E) E) := by rw [← Submodule.zero_eq_bot] at h; rw [← h]; exact hU
    exact not_isUnit_zero this
  have hS0 : S ≠ ⊥ := by
    intro h
    apply hM0
    rw [← hmap, h, Submodule.map_bot]
  let I : FractionalIdeal (nonZeroDivisors (𝓞 (FR E))) (FR E) := ⟨S, FractionalIdeal.isFractional_of_fg hSfg⟩
  have hI : I ≠ 0 := by
    intro h
    apply hS0
    have := congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 (FR E))) (FR E) ↦ (J : Submodule (𝓞 (FR E)) (FR E))) h
    simpa [I] using this
  refine ⟨Units.mk0 I hI, fun a ↦ ?_⟩
  show a ∈ S ↔ _
  rfl

end GlobalTheory.AntiInvFrac
