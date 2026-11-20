import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `hX`. Use `set f : (Fin h → A) →ₗ[A] (Fin h → A) := Matrix.toLin' X with hfdef`. Establish `hff : ∀ v, f (f v) = f v`. Introduce `v`. Establish `: Matrix.toLin' (X * X) v = Matrix.toLin' X v` using `by rw [hX]`.

Simplify `this` using `[Matrix.toLin'_mul, hfdef]`. Use `set M := LinearMap.range f`. Establish `hsplit : f.rangeRestrict ∘ₗ M.subtype = LinearMap.id`. Use extensionality with `⟨w, hw⟩`. Take `⟨v, rfl⟩` from `hw`.

Simplify using `[hff]`. Use `haveI : Module.Projective A M := Module.Projective.of_split M.subtype f.rangeRestrict hsplit`. Use `haveI : Module.Free A M := Module.free_of_flat_of_isLocalRing`. Set `b` to `Module.finBasis A M`. Establish `hqi : LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict) * LinearMap.toMatrix' (M.subtype ∘ₗ b.equivFun.symm.toLinearMap) = 1`.

Rewrite using `[← LinearMap.toMatrix'_comp]`. Establish `: (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict) ∘ₗ (M.subtype ∘ₗ b.equivFun.symm.toLinearMap) = LinearMap.id`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Establish `h1 : f.rangeRestrict (M.subtype (b.equivFun.symm v)) = b.equivFun.symm v` using `LinearMap.congr_fun hsplit _`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h1, LinearEquiv.apply_symm_apply, LinearMap.id_apply]`.

Rewrite using `[this, LinearMap.toMatrix'_id]`. Establish `hiq : LinearMap.toMatrix' (M.subtype ∘ₗ b.equivFun.symm.toLinearMap) * LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict) = X`. Rewrite using `[← LinearMap.toMatrix'_comp]`. Establish `: (M.subtype ∘ₗ b.equivFun.symm.toLinearMap) ∘ₗ (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict) = f`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Simplify using `only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`. Both sides reduce to the same expression. Rewrite using `[this, hfdef, LinearMap.toMatrix'_toLin']`. Use `⟨Module.finrank A M, LinearMap.toMatrix' (M.subtype ∘ₗ b.equivFun.symm.toLinearMap), LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict), hqi, hiq, ?_⟩` and prove the remaining obligations. Rewrite using `[← hiq, Matrix.trace_mul_comm, hqi, Matrix.trace_one, Fintype.card_fin]`.
-/
theorem idempotent_matrix_split_of_isLocalRing (A : Type) [CommRing A] [IsLocalRing A] (h : ℕ)
    (X : Matrix (Fin h) (Fin h) A) : X * X = X → ∃ (n : ℕ) (i : Matrix (Fin h) (Fin n) A)
      (q : Matrix (Fin n) (Fin h) A), q * i = 1 ∧ i * q = X ∧ X.trace = n := by
  classical
  intro hX
  set f : (Fin h → A) →ₗ[A] (Fin h → A) := Matrix.toLin' X with hfdef
  have hff : ∀ v, f (f v) = f v := by
    intro v
    have : Matrix.toLin' (X * X) v = Matrix.toLin' X v := by rw [hX]
    simpa [Matrix.toLin'_mul, hfdef] using this
  set M := LinearMap.range f
  have hsplit : f.rangeRestrict ∘ₗ M.subtype = LinearMap.id := by
    ext ⟨w, hw⟩
    obtain ⟨v, rfl⟩ := hw
    simp [hff]
  haveI : Module.Projective A M := Module.Projective.of_split M.subtype f.rangeRestrict hsplit
  haveI : Module.Free A M := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis A M
  have hqi : LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict) *
      LinearMap.toMatrix' (M.subtype ∘ₗ b.equivFun.symm.toLinearMap) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict) ∘ₗ (M.subtype ∘ₗ b.equivFun.symm.toLinearMap)
        = LinearMap.id := by
      refine LinearMap.ext fun v => ?_
      have h1 : f.rangeRestrict (M.subtype (b.equivFun.symm v)) = b.equivFun.symm v :=
        LinearMap.congr_fun hsplit _
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h1,
        LinearEquiv.apply_symm_apply, LinearMap.id_apply]
    rw [this, LinearMap.toMatrix'_id]
  have hiq : LinearMap.toMatrix' (M.subtype ∘ₗ b.equivFun.symm.toLinearMap) *
      LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict) = X := by
    rw [← LinearMap.toMatrix'_comp]
    have : (M.subtype ∘ₗ b.equivFun.symm.toLinearMap) ∘ₗ (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict)
        = f := by
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      rfl
    rw [this, hfdef, LinearMap.toMatrix'_toLin']
  refine ⟨Module.finrank A M, LinearMap.toMatrix' (M.subtype ∘ₗ b.equivFun.symm.toLinearMap),
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict), hqi, hiq, ?_⟩
  rw [← hiq, Matrix.trace_mul_comm, hqi, Matrix.trace_one, Fintype.card_fin]

end GlobalTheory
