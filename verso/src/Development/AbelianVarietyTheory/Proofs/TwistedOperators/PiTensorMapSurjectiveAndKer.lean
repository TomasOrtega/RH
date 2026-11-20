import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.TensorKernel

/- English proof (translation)
Introduce `ι _ _ A B _ _ _ _ π hπ`. Establish `hsec : ∀ τ, ∃ g : B τ →ₗ[ℂ] A τ, π τ ∘ₗ g = LinearMap.id` using `fun τ => (π τ).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr (hπ τ))`. Use `choose s hs using hsec`. Establish `hπs : ∀ τ b, π τ (s τ b) = b` using `fun τ b => by`. Simplify using `using LinearMap.congr_fun (hs τ) b`.

Establish `back : ∀ b, PiTensorProduct.map π (PiTensorProduct.map s b) = b`. Introduce `b`. Proceed by induction on `b using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r f => simp [PiTensorProduct.map_tprod, hπs]`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq]`.

Use `⟨fun b => ⟨_, back b⟩, ?_⟩` and prove the remaining obligations. Introduce `l hl`. Establish `key : ∀ x : ∀ σ, A σ, l (PiTensorProduct.tprod ℂ x) = l (PiTensorProduct.tprod ℂ (fun σ => s σ (π σ (x σ))))`. Introduce `x`. Establish `step : ∀ S : Finset ι, l (PiTensorProduct.tprod ℂ x) = l (PiTensorProduct.tprod ℂ (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ))`.

Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a S ha ih`. Rewrite using `[ih]`.

Establish `h1 : (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ) = Function.update (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ) a (x a)`. Use function extensionality and compare the values at `σ`. Distinguish the cases in `h : σ = a`. Substitute `h` using the available equality. Simplify using `[ha]`.

Rewrite using `[Function.update_of_ne h]`. Establish `h2 : (fun σ => if σ ∈ insert a S then s σ (π σ (x σ)) else x σ) = Function.update (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ) a (s a (π a (x a)))`. Use function extensionality and compare the values at `σ`. Distinguish the cases in `h : σ = a`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne h]`. Simplify using `[Finset.mem_insert, h]`. Establish `h4` using `hl a (Function.update (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ) a (x a - s a (π a (x a)))) (by simp [hπs])`. Rewrite `h4` using `[MultilinearMap.map_update_sub, map_sub, sub_eq_zero, ← h1]`.

Rewrite using `[h2, h4]`. Simplify using `using step Finset.univ`. Establish `hall : ∀ z, l z = l (PiTensorProduct.map s (PiTensorProduct.map π z))`. Introduce `z`. Proceed by induction on `z using PiTensorProduct.induction_on with`.

Consider the case `smul_tprod r f => simp [PiTensorProduct.map_tprod, key f]`. Consider the case `add p q hp hq => rw [map_add, map_add, map_add, map_add, ← hp, ← hq]`. Introduce `z hz`. Rewrite using `[hall z, hz, map_zero, map_zero]`.
-/
theorem piTensor_map_surjective_and_ker :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A B : ι → Type) [∀ τ, AddCommGroup (A τ)] [∀ τ, Module ℂ (A τ)] [∀ τ, AddCommGroup (B τ)] [∀ τ, Module ℂ (B τ)] (π : ∀ τ, A τ →ₗ[ℂ] B τ), (∀ τ, Function.Surjective (π τ)) → Function.Surjective (PiTensorProduct.map π) ∧ ∀ l : Module.Dual ℂ (⨂[ℂ] τ, A τ), (∀ (τ : ι) (x : ∀ σ, A σ), π τ (x τ) = 0 → l (PiTensorProduct.tprod ℂ x) = 0) → ∀ z, PiTensorProduct.map π z = 0 → l z = 0 := by
  intro ι _ _ A B _ _ _ _ π hπ

  have hsec : ∀ τ, ∃ g : B τ →ₗ[ℂ] A τ, π τ ∘ₗ g = LinearMap.id := fun τ =>
    (π τ).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr (hπ τ))
  choose s hs using hsec
  have hπs : ∀ τ b, π τ (s τ b) = b := fun τ b => by
    simpa using LinearMap.congr_fun (hs τ) b

  have back : ∀ b, PiTensorProduct.map π (PiTensorProduct.map s b) = b := by
    intro b
    induction b using PiTensorProduct.induction_on with
    | smul_tprod r f => simp [PiTensorProduct.map_tprod, hπs]
    | add p q hp hq => rw [map_add, map_add, hp, hq]
  refine ⟨fun b => ⟨_, back b⟩, ?_⟩
  intro l hl

  have key : ∀ x : ∀ σ, A σ, l (PiTensorProduct.tprod ℂ x) =
      l (PiTensorProduct.tprod ℂ (fun σ => s σ (π σ (x σ)))) := by
    intro x
    have step : ∀ S : Finset ι, l (PiTensorProduct.tprod ℂ x) =
        l (PiTensorProduct.tprod ℂ (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ)) := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | insert a S ha ih =>
        rw [ih]
        have h1 : (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ) =
            Function.update (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ) a (x a) := by
          funext σ
          by_cases h : σ = a
          · subst h; simp [ha]
          · rw [Function.update_of_ne h]
        have h2 : (fun σ => if σ ∈ insert a S then s σ (π σ (x σ)) else x σ) =
            Function.update (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ) a
              (s a (π a (x a))) := by
          funext σ
          by_cases h : σ = a
          · subst h; simp
          · rw [Function.update_of_ne h]; simp [Finset.mem_insert, h]
        have h4 := hl a (Function.update (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ) a
          (x a - s a (π a (x a)))) (by simp [hπs])
        rw [MultilinearMap.map_update_sub, map_sub, sub_eq_zero, ← h1] at h4
        rw [h2, h4]
    simpa using step Finset.univ
  have hall : ∀ z, l z = l (PiTensorProduct.map s (PiTensorProduct.map π z)) := by
    intro z
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r f => simp [PiTensorProduct.map_tprod, key f]
    | add p q hp hq => rw [map_add, map_add, map_add, map_add, ← hp, ← hq]
  intro z hz
  rw [hall z, hz, map_zero, map_zero]

end GlobalTheory.TensorKernel
