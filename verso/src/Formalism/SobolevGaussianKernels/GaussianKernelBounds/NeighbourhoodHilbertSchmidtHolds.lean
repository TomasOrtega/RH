import Mathlib
import Formalism.SobolevGaussianKernels.StatementFU

noncomputable section

namespace Formalism.SL.P

open Finset Module LinearMap Formalism.CorankShareLayerCake.FR Formalism.SL.FU
open scoped InnerProductSpace ComplexConjugate

/- English proof (translation)
Use extensionality with `x`. Simplify using `[LinearMap.sum_apply]`.
-/
lemma fu_sum_comp {ι M N Q : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid Q]
    [Module ℂ M] [Module ℂ N] [Module ℂ Q] (s : Finset ι) (f : ι → N →ₗ[ℂ] Q) (g : M →ₗ[ℂ] N) :
    (∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, f i ∘ₗ g := by
  ext x
  simp [LinearMap.sum_apply]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[LinearMap.sum_apply, map_sum]`.
-/
lemma fu_comp_sum {ι M N Q : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid Q]
    [Module ℂ M] [Module ℂ N] [Module ℂ Q] (s : Finset ι) (g : N →ₗ[ℂ] Q) (f : ι → M →ₗ[ℂ] N) :
    g ∘ₗ (∑ i ∈ s, f i) = ∑ i ∈ s, g ∘ₗ f i := by
  ext x
  simp [LinearMap.sum_apply, map_sum]

section HS

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

end HS

/- English proof (translation)
Introduce `ι _ V _ _ _ H _ _ _ B c`. Establish `kc : ∀ i j, trace ℂ H (B i ∘ₗ adjoint (B i) ∘ₗ B j ∘ₗ adjoint (B j)) = trace ℂ (V j) (adjoint (adjoint (B i) ∘ₗ B j) ∘ₗ adjoint (B i) ∘ₗ B j)`. Introduce `i j`. Rewrite using `[LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]`. Establish `h` using `LinearMap.trace_comp_comm' (adjoint (B j)) (B i ∘ₗ adjoint (B i) ∘ₗ B j)`.

Simplify using `only [LinearMap.comp_assoc] at h ⊢`. Conclude with `h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[frQ.eq_1]`. Simplify using `only [fu_sum_comp, fu_comp_sum, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.comp_assoc, map_sum, map_smul, smul_eq_mul, kc, Finset.mul_sum, Complex.re_sum, Complex.re_ofReal_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hs2.eq_1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[frQ.eq_1]`.

Simplify using `only [map_sum, map_smul, smul_eq_mul, Complex.re_sum, Complex.re_ofReal_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.trace_comp_comm']`.
-/
theorem frame_gram_holds : FrameGram := by
  intro ι _ V _ _ _ H _ _ _ B c
  have kc : ∀ i j, trace ℂ H (B i ∘ₗ adjoint (B i) ∘ₗ B j ∘ₗ adjoint (B j)) =
      trace ℂ (V j) (adjoint (adjoint (B i) ∘ₗ B j) ∘ₗ adjoint (B i) ∘ₗ B j) := by
    intro i j
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
    have h := LinearMap.trace_comp_comm' (adjoint (B j)) (B i ∘ₗ adjoint (B i) ∘ₗ B j)
    simp only [LinearMap.comp_assoc] at h ⊢
    exact h
  refine ⟨?_, ?_⟩
  · rw [frQ.eq_1]
    simp only [fu_sum_comp, fu_comp_sum, LinearMap.smul_comp, LinearMap.comp_smul,
      LinearMap.comp_assoc, map_sum, map_smul, smul_eq_mul, kc, Finset.mul_sum, Complex.re_sum,
      Complex.re_ofReal_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hs2.eq_1]
    ring
  · rw [frQ.eq_1]
    simp only [map_sum, map_smul, smul_eq_mul, Complex.re_sum, Complex.re_ofReal_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.trace_comp_comm']

section Neb

variable {A : Type} [AddCommGroup A] [Fintype A] {H : Type} [AddCommGroup H] [Module ℂ H]

end Neb

end Formalism.SL.P
