import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

namespace GlobalTheory.RatUnit

/- English proof (translation)
Simplify using `only [dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp, mul_assoc]`.
-/
theorem sum_eq_dot {R : Type} [CommRing R] {r : ℕ} (σ : R → R) (G : Matrix (Fin r) (Fin r) R)
    (x y : Fin r → R) : ∑ a, ∑ b, x a * G a b * σ (y b) = x ⬝ᵥ (G *ᵥ (σ ∘ y)) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp, mul_assoc]

/- English proof (translation)
Establish `h : σ ∘ (γ *ᵥ y) = γ.map σ *ᵥ (σ ∘ y)`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec σ γ y i`. Rewrite using `[h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x γᵀ, Matrix.vecMul_transpose]`.
-/
theorem dot_mulVec {R : Type} [CommRing R] {r : ℕ} (σ : R →+* R) (G γ : Matrix (Fin r) (Fin r) R)
    (x y : Fin r → R) :
    (γ *ᵥ x) ⬝ᵥ (G *ᵥ (σ ∘ (γ *ᵥ y))) = x ⬝ᵥ ((γᵀ * G * γ.map σ) *ᵥ (σ ∘ y)) := by
  have h : σ ∘ (γ *ᵥ y) = γ.map σ *ᵥ (σ ∘ y) := by
    funext i; exact RingHom.map_mulVec σ γ y i
  rw [h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x γᵀ,
    Matrix.vecMul_transpose]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in

/- English proof (translation)
Introduce `E _ _ _ r G γ hdet hinv`. Establish `hmat : ∀ i j, ∑ a, ∑ b, γ a i * G a b * IsCMField.complexConj E (γ b j) = G i j`. Introduce `i j`. Establish `h` using `hinv (Pi.single i 1) (Pi.single j 1)`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc at h`.

Simplify `h` using `[mulVec, dotProduct, Pi.single_apply, apply_ite]`. Set `A` to `FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)`. Set `φ : E →+* _root_.GlobalTheory.AdLat.RA (maximalRealSubfield E) E` to `(Algebra.TensorProduct.includeRight : E →ₐ[maximalRealSubfield E] A ⊗[maximalRealSubfield E] E).toRingHom`. Establish `hφ : ∀ e : E, φ e = (1 : A) ⊗ₜ[maximalRealSubfield E] e` using `fun _ => rfl`. Establish `hg : _root_.GlobalTheory.UCls.ratM (maximalRealSubfield E) γ = γ.map φ` using `rfl`.

Set `τ` to `_root_.GlobalTheory.AdLat.sg A (IsCMField.complexConj E)`. Establish `hτ : ∀ e : E, τ (φ e) = φ (IsCMField.complexConj E e)`. Introduce `e`. Simplify using `[τ, hφ, _root_.GlobalTheory.AdLat.sg]`. Unfold `_root_.GlobalTheory.UCls.IsUA`.

Rewrite using `[hg]`. Use `⟨?_, fun x y => ?_⟩` and prove the remaining obligations. Establish `h` using `RingHom.map_det φ γ`. Rewrite `h` using `[RingHom.mapMatrix_apply]`. Rewrite using `[← h]`.

Conclude with `(isUnit_iff_ne_zero.mpr hdet).map φ`. Unfold `_root_.GlobalTheory.AdLat.hermA`. Express the relevant statement in the definitionally equal form `∑ a, ∑ b, (γ.map φ *ᵥ x) a * φ (G a b) * τ ((γ.map φ *ᵥ y) b) = ∑ a, ∑ b, x a * φ (G a b) * τ (y b)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mulVec, dotProduct, map_apply, map_sum, map_mul, hτ, Finset.sum_mul, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∑ a, ∑ i, ∑ b, ∑ j, x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) := Finset.sum_congr rfl fun a _ => Finset.sum_comm`.

Use `_ = ∑ i, ∑ a, ∑ b, ∑ j, x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) := Finset.sum_comm`. Use `_ = ∑ i, ∑ a, ∑ j, ∑ b, x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm`. Use `_ = ∑ i, ∑ j, ∑ a, ∑ b, x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) := Finset.sum_congr rfl fun i _ => Finset.sum_comm`. Use `_ = ∑ i, ∑ j, x i * φ (G i j) * τ (y j) := by`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← hmat i j, map_sum, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [map_mul]`.
-/
theorem _root_.GlobalTheory.RatUnit.isUA_ratM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E), γ.det ≠ 0 → (∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (γ *ᵥ x) (γ *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y) → _root_.GlobalTheory.UCls.IsUA (IsCMField.complexConj E) G (_root_.GlobalTheory.UCls.ratM (maximalRealSubfield E) γ) := by
  intro E _ _ _ r G γ hdet hinv
  have hmat : ∀ i j, ∑ a, ∑ b, γ a i * G a b * IsCMField.complexConj E (γ b j) = G i j := by
    intro i j
    have h := hinv (Pi.single i 1) (Pi.single j 1)
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc at h
    simpa [mulVec, dotProduct, Pi.single_apply, apply_ite] using h
  let A := FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
  let φ : E →+* _root_.GlobalTheory.AdLat.RA (maximalRealSubfield E) E :=
    (Algebra.TensorProduct.includeRight :
      E →ₐ[maximalRealSubfield E] A ⊗[maximalRealSubfield E] E).toRingHom
  have hφ : ∀ e : E, φ e = (1 : A) ⊗ₜ[maximalRealSubfield E] e := fun _ => rfl
  have hg : _root_.GlobalTheory.UCls.ratM (maximalRealSubfield E) γ = γ.map φ := rfl
  let τ := _root_.GlobalTheory.AdLat.sg A (IsCMField.complexConj E)
  have hτ : ∀ e : E, τ (φ e) = φ (IsCMField.complexConj E e) := by
    intro e
    simp [τ, hφ, _root_.GlobalTheory.AdLat.sg]
  unfold _root_.GlobalTheory.UCls.IsUA
  rw [hg]
  refine ⟨?_, fun x y => ?_⟩
  · have h := RingHom.map_det φ γ
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]
    exact (isUnit_iff_ne_zero.mpr hdet).map φ
  · unfold _root_.GlobalTheory.AdLat.hermA
    change ∑ a, ∑ b, (γ.map φ *ᵥ x) a * φ (G a b) * τ ((γ.map φ *ᵥ y) b) =
      ∑ a, ∑ b, x a * φ (G a b) * τ (y b)
    calc _ = ∑ a, ∑ b, ∑ i, ∑ j,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) := by
          simp only [mulVec, dotProduct, map_apply, map_sum, map_mul, hτ, Finset.sum_mul,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = ∑ a, ∑ i, ∑ b, ∑ j,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b, ∑ j,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) :=
          Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ j, ∑ b,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ a, ∑ b,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ j, x i * φ (G i j) * τ (y j) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [← hmat i j, map_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [map_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => ?_
          simp only [map_mul]

end GlobalTheory.RatUnit
