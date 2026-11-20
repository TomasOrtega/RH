import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

noncomputable def twistAlg {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ) :
    MonoidAlgebra K H →ₐ[K] MonoidAlgebra K H :=
  MonoidAlgebra.lift K (MonoidAlgebra K H) H
    { toFun := fun h => MonoidAlgebra.single h (((χ (h : Γ))⁻¹ : Kˣ) : K)
      map_one' := by simp [MonoidAlgebra.one_def]
      map_mul' := by
        intro a b
        simp [MonoidAlgebra.single_mul_single, mul_comm] }

/- English proof (translation)
Simplify using `[twistAlg, MonoidAlgebra.lift_single, MonoidAlgebra.smul_single]`.
-/
theorem twistAlg_single {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ) (h : H) (c : K) :
    twistAlg H χ (MonoidAlgebra.single h c) = MonoidAlgebra.single h (c * (((χ (h : Γ))⁻¹ : Kˣ) : K)) := by
  simp [twistAlg, MonoidAlgebra.lift_single, MonoidAlgebra.smul_single]

/- English proof (translation)
Proceed by induction on `x using MonoidAlgebra.induction_on with`. Consider the case `of m`. Simplify using `only [MonoidAlgebra.of_apply, twistAlg_single]`. Use `congr 1`. Simplify using the standard rewrite rules.

Consider the case `add x y hx hy => simp [map_add, hx, hy]`. Consider the case `smul r x hx => simp [map_smul, hx]`.
-/
theorem twistAlg_inv_twistAlg {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ)
    (x : MonoidAlgebra K H) : twistAlg H χ⁻¹ (twistAlg H χ x) = x := by
  induction x using MonoidAlgebra.induction_on with
  | of m =>
    simp only [MonoidAlgebra.of_apply, twistAlg_single]
    congr 1
    simp
  | add x y hx hy => simp [map_add, hx, hy]
  | smul r x hx => simp [map_smul, hx]

/- English proof (translation)
Introduce `x y hxy` and use `by rw [← twistAlg_inv_twistAlg H χ x, ← twistAlg_inv_twistAlg H χ y, hxy]`.
-/
theorem twistAlg_injective {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ) :
    Function.Injective (twistAlg H χ) := fun x y hxy => by
  rw [← twistAlg_inv_twistAlg H χ x, ← twistAlg_inv_twistAlg H χ y, hxy]

/- English proof (translation)
Introduce `K Γ V _ _ _ _ ρ ρ' χ hρ H n ⟨j, hj, hjeq⟩`. Use `⟨LinearMap.pi fun i => (twistAlg H χ).toLinearMap.comp ((LinearMap.proj i).comp j), ?_, ?_⟩` and prove the remaining obligations. Introduce `v w hvw`. Apply `hj` to reduce the goal to its premises. Use function extensionality and compare the values at `i`.

Use `congrFun hvw i` as an intermediate fact. Simplify using `only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.coe_proj, Function.eval, AlgHom.toLinearMap_apply] at this`. Conclude with `twistAlg_injective H χ this`. Introduce `h v i`. Simplify using `only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.coe_proj, Function.eval, AlgHom.toLinearMap_apply]`.

Rewrite using `[hρ, map_smul, Pi.smul_apply, hjeq, map_smul, map_mul, twistAlg_single, ← smul_mul_assoc, MonoidAlgebra.smul_single]`. Use `congr 2`. Simplify using the standard rewrite rules.
-/
theorem embReg_twist : ∀ (K Γ V : Type) [Field K] [Group Γ] [AddCommGroup V] [Module K V] (ρ ρ' : Representation K Γ V)
    (χ : Γ →* Kˣ), (∀ g v, ρ' g v = ((χ g : Kˣ) : K) • ρ g v) → ∀ (H : Subgroup Γ) (n : ℕ), EmbReg ρ H n → EmbReg ρ' H n := by
  intro K Γ V _ _ _ _ ρ ρ' χ hρ H n ⟨j, hj, hjeq⟩
  refine ⟨LinearMap.pi fun i => (twistAlg H χ).toLinearMap.comp ((LinearMap.proj i).comp j), ?_, ?_⟩
  · intro v w hvw
    apply hj
    funext i
    have := congrFun hvw i
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.coe_proj, Function.eval,
      AlgHom.toLinearMap_apply] at this
    exact twistAlg_injective H χ this
  · intro h v i
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.coe_proj, Function.eval,
      AlgHom.toLinearMap_apply]
    rw [hρ, map_smul, Pi.smul_apply, hjeq, map_smul, map_mul, twistAlg_single, ← smul_mul_assoc,
      MonoidAlgebra.smul_single]
    congr 2
    simp

end GlobalTheory.BadCount
