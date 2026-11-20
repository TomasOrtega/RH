import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

open GlobalTheory.RegSS GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

/- English proof (translation)
Establish `hδ : f (b 1) * f (b 1) = algebraMap F L d` using `by rw [← map_mul, hsq, AlgHom.commutes]`. Establish `hinv : algebraMap F L d⁻¹ * (f (b 1) * f (b 1)) = 1`. Rewrite using `[hδ, ← map_mul, inv_mul_cancel₀ hd, map_one]`. Establish `h2 : algebraMap F L 2⁻¹ * 2 = 1`. Rewrite using `[← map_ofNat (algebraMap F L) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]`.

Establish `hval : ∀ a c : P, Algebra.TensorProduct.productMap P.val f (a ⊗ₜ[F] 1 + c ⊗ₜ[F] b 1) = (a : L) + (c : L) * f (b 1)` using `fun a c => by`. Simplify using `[Algebra.TensorProduct.productMap_apply_tmul]`. Prove the components needed by the constructor for the conclusion. Establish `hrep : ∀ x : P ⊗[F] E, ∃ a c : P, x = a ⊗ₜ[F] 1 + c ⊗ₜ[F] b 1`. Introduce `x`.

Proceed by induction on `x with`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `tmul p e`. Use `⟨b.repr e 0 • p, b.repr e 1 • p, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← b.sum_repr e, Fin.sum_univ_two, h0]`.

Rewrite using `[TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul]`. Consider the case `add x y hx hy`. Take `⟨a, c, rfl⟩` from `hx`. Take `⟨a', c', rfl⟩` from `hy`. Conclude with `⟨a + a', c + c', by rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel⟩`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨a, c, rfl⟩` from `hrep x`. Rewrite `hx` using `[hval]`. Establish `hx'` using `congrArg τ hx`.

Rewrite `hx'` using `[map_add, map_mul, map_zero, (hP _).1 a.2, (hP _).1 c.2, h1]`. Establish `ha : (a : L) = 0`. Take the linear combination `(algebraMap F L 2⁻¹) * (hx + hx') - (a : L) * h2`. Establish `hc : (c : L) = 0`. Take the linear combination `(algebraMap F L d⁻¹ * f (b 1)) * (hx - ha) - (c : L) * hinv`.

Rewrite using `[show a = 0 from Subtype.ext ha, show c = 0 from Subtype.ext hc]`. Simplify using the standard rewrite rules. Introduce `l`. Use `⟨(⟨algebraMap F L 2⁻¹ * (l + τ l), (hP _).2 ?_⟩ : P) ⊗ₜ[F] 1 + (⟨algebraMap F L 2⁻¹ * algebraMap F L d⁻¹ * f (b 1) * (l - τ l), (hP _).2 ?_⟩ : P) ⊗ₜ[F] b 1, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_add, hτ, AlgEquiv.commutes, add_comm]`.

Rewrite using `[map_mul, map_mul, map_mul, map_sub, hτ, AlgEquiv.commutes, AlgEquiv.commutes, h1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hval] dsimp only`. Take the linear combination `l * h2 + algebraMap F L 2⁻¹ * (l - τ l) * hinv`.
-/
theorem productMap_bijective_of_involution {F E L : Type} [Field F] [CharZero F] [CommRing E]
    [Algebra F E] [CommRing L] [Algebra F L] (f : E →ₐ[F] L) (τ : L ≃ₐ[F] L)
    (hτ : ∀ l, τ (τ l) = l) (P : Subalgebra F L) (hP : ∀ l, l ∈ P ↔ τ l = l)
    (b : Module.Basis (Fin 2) F E) (d : F) (h0 : b 0 = 1) (h1 : τ (f (b 1)) = - f (b 1))
    (hd : d ≠ 0) (hsq : b 1 * b 1 = algebraMap F E d) :
    Function.Bijective (Algebra.TensorProduct.productMap P.val f) := by
  have hδ : f (b 1) * f (b 1) = algebraMap F L d := by rw [← map_mul, hsq, AlgHom.commutes]
  have hinv : algebraMap F L d⁻¹ * (f (b 1) * f (b 1)) = 1 := by
    rw [hδ, ← map_mul, inv_mul_cancel₀ hd, map_one]
  have h2 : algebraMap F L 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap F L) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hval : ∀ a c : P, Algebra.TensorProduct.productMap P.val f (a ⊗ₜ[F] 1 + c ⊗ₜ[F] b 1) =
      (a : L) + (c : L) * f (b 1) := fun a c => by
    simp [Algebra.TensorProduct.productMap_apply_tmul]
  constructor
  · have hrep : ∀ x : P ⊗[F] E, ∃ a c : P, x = a ⊗ₜ[F] 1 + c ⊗ₜ[F] b 1 := by
      intro x
      induction x with
      | zero => exact ⟨0, 0, by simp⟩
      | tmul p e =>
        refine ⟨b.repr e 0 • p, b.repr e 1 • p, ?_⟩
        conv_lhs => rw [← b.sum_repr e, Fin.sum_univ_two, h0]
        rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul]
      | add x y hx hy =>
        obtain ⟨a, c, rfl⟩ := hx
        obtain ⟨a', c', rfl⟩ := hy
        exact ⟨a + a', c + c', by rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel⟩
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, c, rfl⟩ := hrep x
    rw [hval] at hx
    have hx' := congrArg τ hx
    rw [map_add, map_mul, map_zero, (hP _).1 a.2, (hP _).1 c.2, h1] at hx'
    have ha : (a : L) = 0 := by
      linear_combination (algebraMap F L 2⁻¹) * (hx + hx') - (a : L) * h2
    have hc : (c : L) = 0 := by
      linear_combination (algebraMap F L d⁻¹ * f (b 1)) * (hx - ha) - (c : L) * hinv
    rw [show a = 0 from Subtype.ext ha, show c = 0 from Subtype.ext hc]
    simp
  · intro l
    refine ⟨(⟨algebraMap F L 2⁻¹ * (l + τ l), (hP _).2 ?_⟩ : P) ⊗ₜ[F] 1 +
      (⟨algebraMap F L 2⁻¹ * algebraMap F L d⁻¹ * f (b 1) * (l - τ l), (hP _).2 ?_⟩ : P) ⊗ₜ[F] b 1,
      ?_⟩
    · rw [map_mul, map_add, hτ, AlgEquiv.commutes, add_comm]
    · rw [map_mul, map_mul, map_mul, map_sub, hτ, AlgEquiv.commutes, AlgEquiv.commutes, h1]
      ring
    · rw [hval]
      dsimp only
      linear_combination l * h2 + algebraMap F L 2⁻¹ * (l - τ l) * hinv

/- English proof (translation)
Introduce `F E _ _ _ _ n _ _ σ J γ h hA`. Take `⟨τ, -, hτ, hE, hP⟩` from `exists_adjEquiv h hA`. Take `⟨b, d, h0, h1, hd, hsq⟩` from `quad_exists_basis h.quad`. Use `productMap_bijective_of_involution _ τ hτ _ hP b d h0 ?_ hd hsq` and prove the remaining obligations. Rewrite using `[IsScalarTower.toAlgHom_apply, hE, h1, map_neg]`.
-/
theorem plusTensorBijective : PlusTensorBijective := by
  intro F E _ _ _ _ n _ _ σ J γ h hA
  obtain ⟨τ, -, hτ, hE, hP⟩ := exists_adjEquiv h hA
  obtain ⟨b, d, h0, h1, hd, hsq⟩ := quad_exists_basis h.quad
  refine productMap_bijective_of_involution _ τ hτ _ hP b d h0 ?_ hd hsq
  rw [IsScalarTower.toAlgHom_apply, hE, h1, map_neg]

end GlobalTheory.RegSS
