import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver

open scoped TensorProduct

noncomputable section
namespace GlobalTheory.GoodEtale

variable {R C O G : Type} [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O] [Group G]

def galMap (act : G →* (C ≃ₐ[R] C)) (σ : C →ₐ[R] O) : O ⊗[R] C →ₐ[O] (G → O) :=
  Pi.algHom O (fun _ => O) fun g =>
    Algebra.TensorProduct.lift (AlgHom.id O O) (σ.comp (act g).toAlgHom) (fun _ _ => Commute.all _ _)

/- English proof (translation)
Simplify using `[galMap]`.
-/
@[simp] theorem galMap_tmul (act : G →* (C ≃ₐ[R] C)) (σ : C →ₐ[R] O) (o : O) (c : C) (g : G) :
    galMap act σ (o ⊗ₜ c) g = o * σ (act g c) := by
  simp [galMap]

def galElt (act : G →* (C ≃ₐ[R] C)) (σ : C →ₐ[R] O) {n : ℕ} (x y : Fin n → C) (h : G) : O ⊗[R] C :=
  ∑ i, σ (x i) ⊗ₜ act h⁻¹ (y i)

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [galElt, map_sum, Finset.sum_apply, galMap_tmul]`. Establish `: ∀ i, σ (x i) * σ (act g (act h⁻¹ (y i))) = σ (x i * act (g * h⁻¹) (y i))`. Introduce `i`. Simplify using `[map_mul]`.

Repeatedly rewrite using `[this, ← map_sum, hxy]`. Distinguish the cases in `hg : g = h`. Substitute `hg` using the available equality. Simplify using the standard rewrite rules. Establish `: g * h⁻¹ ≠ 1` using `fun e => hg (mul_inv_eq_one.mp e)`.

Simplify using `[this, hg]`.
-/
theorem galMap_galElt [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (σ : C →ₐ[R] O) {n : ℕ} (x y : Fin n → C)
    (b : R) (hxy : ∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C b else 0) (h : G) :
    galMap act σ (galElt act σ x y h) = Pi.single h (algebraMap R O b) := by
  funext g
  simp only [galElt, map_sum, Finset.sum_apply, galMap_tmul]
  have : ∀ i, σ (x i) * σ (act g (act h⁻¹ (y i))) = σ (x i * act (g * h⁻¹) (y i)) := by
    intro i; simp [map_mul]
  simp_rw [this, ← map_sum, hxy]
  by_cases hg : g = h
  · subst hg; simp
  · have : g * h⁻¹ ≠ 1 := fun e => hg (mul_inv_eq_one.mp e)
    simp [this, hg]

end GlobalTheory.GoodEtale

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
example (R : Type) [CommRing R] (o r : R) :
    GlobalTheory.GoodEtale.galMap (G := Unit) 1 (AlgHom.id R R) (o ⊗ₜ r) () = o * r := by
  simp
