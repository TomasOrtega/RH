import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemSpanRatPolysVanishingOfAutStableStatement

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨p, hp, rfl⟩` from `hx`. Introduce `c`. Establish `hvan : l c • p ∈ vanI Γ` using `by show ∀ g ∈ Γ, ev (l c • p) g = 0`.

Introduce `g hg`. Establish `h0 : ev p g = 0` using `hp g hg`. Simplify using `only [ev] at h0 ⊢`. Rewrite using `[map_smul, h0, smul_zero]`. Use `⟨l c • p, hvan, fun m => ?_⟩` and prove the remaining obligations.

Rewrite using `[MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, mul_comm c, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]`. Consider the case `zero`. Introduce `c`. Establish `hvan : (0 : MvPolynomial (ι × ι) ℚ) ∈ vanI Γ` using `by show ∀ g ∈ Γ, ev (0 : MvPolynomial (ι × ι) ℚ) g = 0`. Introduce `g _`.

Simplify using `[ev]`. Conclude with `⟨0, hvan, fun m => by simp⟩`. Consider the case `add x y _ _ hx hy`. Introduce `c`. Take `⟨a, ha, ha'⟩` from `hx c`.

Take `⟨b, hb, hb'⟩` from `hy c`. Establish `hvan : a + b ∈ vanI Γ` using `by show ∀ g ∈ Γ, ev (a + b) g = 0`. Introduce `g hg`. Establish `h1 : ev a g = 0` using `ha g hg`. Establish `h2 : ev b g = 0` using `hb g hg`.

Simplify using `only [ev] at h1 h2 ⊢`. Rewrite using `[map_add, h1, h2, add_zero]`. Use `⟨a + b, hvan, fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_add, ha', hb', MvPolynomial.coeff_add, mul_add, map_add]`. Consider the case `smul a x _ hx`.

Introduce `c`. Take `⟨f', hf', h'⟩` from `hx (c * a)`. Conclude with `⟨f', hf', fun m => by rw [h', MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc]⟩`.
-/
theorem exists_component_mem_vanI_of_mem_span {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ))
    (l : ℂ →ₗ[ℚ] ℚ) (f : MvPolynomial (ι × ι) ℂ)
    (hf : f ∈ Submodule.span ℂ ((MvPolynomial.map (algebraMap ℚ ℂ)) '' vanI Γ)) :
    ∀ c : ℂ, ∃ f' ∈ vanI Γ, ∀ m, MvPolynomial.coeff m f' = l (c * MvPolynomial.coeff m f) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    intro c
    have hvan : l c • p ∈ vanI Γ := by
      show ∀ g ∈ Γ, ev (l c • p) g = 0
      intro g hg
      have h0 : ev p g = 0 := hp g hg
      simp only [ev] at h0 ⊢
      rw [map_smul, h0, smul_zero]
    refine ⟨l c • p, hvan, fun m => ?_⟩
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, mul_comm c,
      ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  | zero =>
    intro c
    have hvan : (0 : MvPolynomial (ι × ι) ℚ) ∈ vanI Γ := by
      show ∀ g ∈ Γ, ev (0 : MvPolynomial (ι × ι) ℚ) g = 0
      intro g _
      simp [ev]
    exact ⟨0, hvan, fun m => by simp⟩
  | add x y _ _ hx hy =>
    intro c
    obtain ⟨a, ha, ha'⟩ := hx c
    obtain ⟨b, hb, hb'⟩ := hy c
    have hvan : a + b ∈ vanI Γ := by
      show ∀ g ∈ Γ, ev (a + b) g = 0
      intro g hg
      have h1 : ev a g = 0 := ha g hg
      have h2 : ev b g = 0 := hb g hg
      simp only [ev] at h1 h2 ⊢
      rw [map_add, h1, h2, add_zero]
    refine ⟨a + b, hvan, fun m => ?_⟩
    rw [MvPolynomial.coeff_add, ha', hb', MvPolynomial.coeff_add, mul_add, map_add]
  | smul a x _ hx =>
    intro c
    obtain ⟨f', hf', h'⟩ := hx (c * a)
    exact ⟨f', hf', fun m => by rw [h', MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc]⟩

/- English proof (translation)
Introduce `ι _ _ Γ hΓ f hf l f' hf'`. Take `⟨p, hp, hpc⟩` from `exists_component_mem_vanI_of_mem_span Γ l f (GlobalTheory.T.mem_span_ratPolysVanishing_of_autStable ι Γ hΓ f hf) 1`. Establish `hfp : f' = p`. Use extensionality with `m`. Rewrite using `[hf', hpc, one_mul]`.

Conclude with `hfp ▸ hp`.
-/
theorem component_mem_vanI : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → ∀ (l : ℂ →ₗ[ℚ] ℚ) (f' : MvPolynomial (ι × ι) ℚ), (∀ m, MvPolynomial.coeff m f' = l (MvPolynomial.coeff m f)) → f' ∈ vanI Γ := by
  intro ι _ _ Γ hΓ f hf l f' hf'
  obtain ⟨p, hp, hpc⟩ :=
    exists_component_mem_vanI_of_mem_span Γ l f (GlobalTheory.T.mem_span_ratPolysVanishing_of_autStable ι Γ hΓ f hf) 1
  have hfp : f' = p := by
    ext m
    rw [hf', hpc, one_mul]
  exact hfp ▸ hp

end GlobalTheory.ClassFin
