import Mathlib

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Introduce `k F Ω _ _ _ _ _ R _ θ hθ ev r hr`. Set `S : Subalgebra R F` to `Algebra.adjoin R {θ}`. Set `e : AdjoinRoot (minpoly R θ) ≃ₐ[R] S` to `minpoly.equivAdjoin hθ`. Set `φ : S →+* Ω` to `(AdjoinRoot.lift (ev : R →+* Ω) r hr).comp (e.symm : S →+* AdjoinRoot (minpoly R θ))`. Establish `hφ : ∀ (x : F) (hx : x ∈ R) (hxS : x ∈ S), φ ⟨x, hxS⟩ = ev ⟨x, hx⟩`.

Introduce `x hx hxS`. Establish `h1 : (⟨x, hxS⟩ : S) = algebraMap R S ⟨x, hx⟩` using `rfl`. Simplify using `only [φ, RingHom.comp_apply, h1]`. Rewrite using `[show (e.symm : S →+* AdjoinRoot (minpoly R θ)) (algebraMap R S ⟨x, hx⟩) = AdjoinRoot.of (minpoly R θ) ⟨x, hx⟩ from e.symm.commutes _]`. Conclude with `AdjoinRoot.lift_of hr`.

Establish `hle : Algebra.adjoin k (insert θ (R : Set F)) ≤ S.restrictScalars k`. Rewrite using `[Algebra.adjoin_le_iff, Set.insert_subset_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show θ ∈ S`. Conclude with `Algebra.subset_adjoin (Set.mem_singleton _)`.

Introduce `y hy show y ∈ S`. Conclude with `S.algebraMap_mem (⟨y, hy⟩ : R)`. Establish `hmem : ∀ z : Algebra.adjoin k (insert θ (R : Set F)), (z : F) ∈ S` using `fun z => hle z.2`. Set `ψ₀ : Algebra.adjoin k (insert θ (R : Set F)) →+* Ω` to `{ toFun := fun z => φ ⟨z.1, hmem z⟩ map_one' := φ.map_one map_mul' := fun a b => φ.map_mul ⟨a.1, hmem a⟩ ⟨b.1, hmem b⟩ map_zero' := φ.map_zero map_add' := fun a b => φ.map_add ⟨a.1, hmem a⟩ ⟨b.1, hmem b⟩ }`. Use `⟨{ ψ₀ with commutes' := fun c => ?_ }, fun x hx hx' => hφ x hx (hle hx')⟩` and prove the remaining obligations.

Conclude with `(hφ (algebraMap k F c) (R.algebraMap_mem c) _).trans (ev.commutes c)`.
-/
theorem extend_alg_hom_adjoin_integral_root :
    ∀ (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω] [Algebra k Ω]
    (R : Subalgebra k F) [IsIntegrallyClosed R] (θ : F), IsIntegral R θ →
    ∀ (ev : R →ₐ[k] Ω) (r : Ω), Polynomial.eval₂ (ev : R →+* Ω) r (minpoly R θ) = 0 →
    ∃ ψ : Algebra.adjoin k (insert θ (R : Set F)) →ₐ[k] Ω,
      ∀ (x : F) (hx : x ∈ R) (hx' : x ∈ Algebra.adjoin k (insert θ (R : Set F))),
        ψ ⟨x, hx'⟩ = ev ⟨x, hx⟩ := by
  intro k F Ω _ _ _ _ _ R _ θ hθ ev r hr
  let S : Subalgebra R F := Algebra.adjoin R {θ}
  let e : AdjoinRoot (minpoly R θ) ≃ₐ[R] S := minpoly.equivAdjoin hθ
  let φ : S →+* Ω := (AdjoinRoot.lift (ev : R →+* Ω) r hr).comp (e.symm : S →+* AdjoinRoot (minpoly R θ))
  have hφ : ∀ (x : F) (hx : x ∈ R) (hxS : x ∈ S), φ ⟨x, hxS⟩ = ev ⟨x, hx⟩ := by
    intro x hx hxS
    have h1 : (⟨x, hxS⟩ : S) = algebraMap R S ⟨x, hx⟩ := rfl
    simp only [φ, RingHom.comp_apply, h1]
    rw [show (e.symm : S →+* AdjoinRoot (minpoly R θ)) (algebraMap R S ⟨x, hx⟩)
        = AdjoinRoot.of (minpoly R θ) ⟨x, hx⟩ from e.symm.commutes _]
    exact AdjoinRoot.lift_of hr
  have hle : Algebra.adjoin k (insert θ (R : Set F)) ≤ S.restrictScalars k := by
    rw [Algebra.adjoin_le_iff, Set.insert_subset_iff]
    refine ⟨?_, ?_⟩
    · show θ ∈ S
      exact Algebra.subset_adjoin (Set.mem_singleton _)
    · intro y hy
      show y ∈ S
      exact S.algebraMap_mem (⟨y, hy⟩ : R)
  have hmem : ∀ z : Algebra.adjoin k (insert θ (R : Set F)), (z : F) ∈ S := fun z => hle z.2
  let ψ₀ : Algebra.adjoin k (insert θ (R : Set F)) →+* Ω :=
    { toFun := fun z => φ ⟨z.1, hmem z⟩
      map_one' := φ.map_one
      map_mul' := fun a b => φ.map_mul ⟨a.1, hmem a⟩ ⟨b.1, hmem b⟩
      map_zero' := φ.map_zero
      map_add' := fun a b => φ.map_add ⟨a.1, hmem a⟩ ⟨b.1, hmem b⟩ }
  refine ⟨{ ψ₀ with commutes' := fun c => ?_ }, fun x hx hx' => hφ x hx (hle hx')⟩
  exact (hφ (algebraMap k F c) (R.algebraMap_mem c) _).trans (ev.commutes c)

end GlobalTheory
