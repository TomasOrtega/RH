import Mathlib

namespace GlobalTheory

open Module

/- English proof (translation)
Rewrite using `[← LinearMap.range_eq_top]`. Establish `hco : (LinearMap.range b).dualCoannihilator = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `u hu`. Rewrite `hu` using `[Submodule.mem_dualCoannihilator]`.

Assume the negation of the conclusion as `h0`. Take `⟨v, hv⟩` from `hb u h0`. Conclude with `hv (hu _ ⟨v, rfl⟩)`. Rewrite using `[← Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range b), hco, Submodule.dualAnnihilator_bot]`.
-/
theorem pairing_surjective_of_separating {M N : Type} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N] (b : M →ₗ[ℂ] N →ₗ[ℂ] ℂ)
    (hb : ∀ u, u ≠ 0 → ∃ v, b v u ≠ 0) : Function.Surjective b := by
  rw [← LinearMap.range_eq_top]
  have hco : (LinearMap.range b).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Submodule.mem_dualCoannihilator] at hu
    by_contra h0
    obtain ⟨v, hv⟩ := hb u h0
    exact hv (hu _ ⟨v, rfl⟩)
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range b), hco,
    Submodule.dualAnnihilator_bot]

/- English proof (translation)
Introduce `ι _ _ M N _ _ _ _ _ b hb`. Use `⟨(PiTensorProduct.dualDistrib (R := ℂ) (M := N)).compMultilinearMap ((PiTensorProduct.tprod ℂ).compLinearMap b), ?_, ?_⟩` and prove the remaining obligations. Introduce `v x`. Simplify using `[PiTensorProduct.dualDistrib_apply]`. Introduce `u hu`.

Set `e : ∀ τ, Basis (Fin (finrank ℂ (N τ))) ℂ (N τ)` to `fun τ => Module.finBasis ℂ (N τ)`. Set `E` to `Basis.piTensorProduct e`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, E.repr u k ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hu (E.repr.injective (by ext k; simp [h k]))`. Establish `hs : ∀ τ, ∃ v, b τ v = (e τ).coord (k τ)` using `fun τ => pairing_surjective_of_separating (b τ) (hb τ) _`. Use `choose v hv using hs`. Use `⟨v, ?_⟩` and prove the remaining obligations. Establish `key : (PiTensorProduct.dualDistrib (R` using `ℂ) (M := N)) (PiTensorProduct.tprod ℂ fun τ => b τ (v τ)) = E.coord k := by`.

Apply `E.ext` to reduce the goal to its premises. Introduce `j`. Simplify using `only [hv, E, Basis.piTensorProduct_apply, PiTensorProduct.dualDistrib_apply, Basis.coord_apply, Basis.repr_self]`. Rewrite using `[← Basis.piTensorProduct_apply, Basis.repr_self]`. Simplify using `only [Finsupp.single_apply]`.

Distinguish the cases in `hjk : j = k`. Substitute `hjk` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hjk]`. Choose the witnesses or unpack the hypotheses as in `⟨τ, hτ⟩ : ∃ τ, j τ ≠ k τ := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hjk (funext h)`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ)`. Simplify `hk` using `[key]`.
-/
theorem tensor_pairing_separating : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M N : ι → Type)
    [∀ τ, AddCommGroup (M τ)] [∀ τ, Module ℂ (M τ)] [∀ τ, AddCommGroup (N τ)]
    [∀ τ, Module ℂ (N τ)] [∀ τ, FiniteDimensional ℂ (N τ)] (b : ∀ τ, M τ →ₗ[ℂ] N τ →ₗ[ℂ] ℂ),
    (∀ τ u, u ≠ 0 → ∃ v, b τ v u ≠ 0) →
    ∃ B : MultilinearMap ℂ M (Module.Dual ℂ (PiTensorProduct ℂ N)),
      (∀ v x, B v (PiTensorProduct.tprod ℂ x) = ∏ τ, b τ (v τ) (x τ)) ∧
      ∀ u, u ≠ 0 → ∃ v, B v u ≠ 0 := by
  intro ι _ _ M N _ _ _ _ _ b hb
  refine ⟨(PiTensorProduct.dualDistrib (R := ℂ) (M := N)).compMultilinearMap
    ((PiTensorProduct.tprod ℂ).compLinearMap b), ?_, ?_⟩
  · intro v x
    simp [PiTensorProduct.dualDistrib_apply]
  · intro u hu
    let e : ∀ τ, Basis (Fin (finrank ℂ (N τ))) ℂ (N τ) := fun τ => Module.finBasis ℂ (N τ)
    let E := Basis.piTensorProduct e
    obtain ⟨k, hk⟩ : ∃ k, E.repr u k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hu (E.repr.injective (by ext k; simp [h k]))
    have hs : ∀ τ, ∃ v, b τ v = (e τ).coord (k τ) := fun τ =>
      pairing_surjective_of_separating (b τ) (hb τ) _
    choose v hv using hs
    refine ⟨v, ?_⟩
    have key : (PiTensorProduct.dualDistrib (R := ℂ) (M := N))
        (PiTensorProduct.tprod ℂ fun τ => b τ (v τ)) = E.coord k := by
      apply E.ext
      intro j
      simp only [hv, E, Basis.piTensorProduct_apply, PiTensorProduct.dualDistrib_apply,
        Basis.coord_apply, Basis.repr_self]
      rw [← Basis.piTensorProduct_apply, Basis.repr_self]
      simp only [Finsupp.single_apply]
      by_cases hjk : j = k
      · subst hjk; simp
      · rw [if_neg hjk]
        obtain ⟨τ, hτ⟩ : ∃ τ, j τ ≠ k τ := by
          by_contra h; push_neg at h; exact hjk (funext h)
        exact Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ)
    simpa [key] using hk

end GlobalTheory
