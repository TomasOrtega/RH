import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GaloisStableSubmoduleLeSpanRationalStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Unfold `evC`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p n hp => simp only [map_mul, hp]`.

Simplify using the standard rewrite rules.
-/
theorem evC_map_ringEquiv {ι : Type} (σ : ℂ ≃+* ℂ) (f : MvPolynomial (ι × ι) ℂ) (g : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (σ : ℂ →+* ℂ) f) g = σ (evC f (g.map σ.symm)) := by
  unfold evC
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp]; simp

/- English proof (translation)
Unfold `evC ev`. Rewrite using `[MvPolynomial.eval_map, MvPolynomial.aeval_def]`.
-/
theorem evC_map_rat {ι : Type} (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (algebraMap ℚ ℂ) f) g = ev f g := by
  unfold evC ev
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]

/- English proof (translation)
Introduce `ι _ _ Γ hΓ f hf`. Set `W : Submodule ℂ (MvPolynomial (ι × ι) ℂ)` to `{ carrier := {f | ∀ g ∈ Γ, evC f g = 0} add_mem' := by`. Introduce `a b ha hb g hg`. Establish `h1` using `ha g hg`. Establish `h2` using `hb g hg`.

Unfold `evC at *`. Rewrite using `[map_add, h1, h2, add_zero]`. Use the proof step `zero_mem' := by`. Introduce `g hg`. Simplify using `[evC]`.

Use the proof step `smul_mem' := by`. Introduce `c a ha g hg`. Establish `h1` using `ha g hg`. Unfold `evC at *`. Rewrite using `[MvPolynomial.smul_eval, h1, mul_zero] }`.

Establish `hrepr : ∀ (p : MvPolynomial (ι × ι) ℂ) k, (MvPolynomial.basisMonomials (ι × ι) ℂ).repr p k = MvPolynomial.coeff k p` using `fun p k => rfl`. Establish `key` using `GlobalTheory.T.galoisStable_submodule_le_span_rational _ _ (MvPolynomial.basisMonomials (ι × ι) ℂ) W (by`. Introduce `σ w hw`. Use `⟨MvPolynomial.map (σ : ℂ →+* ℂ) w, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`.

Rewrite using `[evC_map_ringEquiv, hw _ (hΓ σ.symm g hg), map_zero]`. Introduce `k`. Rewrite using `[hrepr, hrepr, MvPolynomial.coeff_map]`. Use the proof step `rfl)`. Use `Submodule.span_mono ?_ (key (show f ∈ W from hf))` and prove the remaining obligations.

Introduce and unpack `w ⟨hw, hq⟩`. Establish `hl : w ∈ Set.range (MvPolynomial.map (σ` using `ι × ι) (algebraMap ℚ ℂ)) := by`. Rewrite using `[MvPolynomial.mem_range_map_iff_coeffs_subset]`. Introduce `c hc`. Simplify using `only [Finset.mem_coe, MvPolynomial.mem_coeffs_iff] at hc`.

Take `⟨k, -, rfl⟩` from `hc`. Take `⟨q, hq⟩` from `hq k`. Conclude with `⟨q, by rw [← hrepr, hq]; rfl⟩`. Take `⟨w₀, rfl⟩` from `hl`. Use `⟨w₀, ?_, rfl⟩` and prove the remaining obligations.

Introduce `g hg`. Rewrite using `[← evC_map_rat]`. Conclude with `hw g hg`.
-/
theorem mem_span_vanI_of_vanish : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → f ∈ Submodule.span ℂ ((MvPolynomial.map (algebraMap ℚ ℂ)) '' vanI Γ) := by
  intro ι _ _ Γ hΓ f hf
  let W : Submodule ℂ (MvPolynomial (ι × ι) ℂ) :=
    { carrier := {f | ∀ g ∈ Γ, evC f g = 0}
      add_mem' := by
        intro a b ha hb g hg
        have h1 := ha g hg
        have h2 := hb g hg
        unfold evC at *
        rw [map_add, h1, h2, add_zero]
      zero_mem' := by
        intro g hg
        simp [evC]
      smul_mem' := by
        intro c a ha g hg
        have h1 := ha g hg
        unfold evC at *
        rw [MvPolynomial.smul_eval, h1, mul_zero] }
  have hrepr : ∀ (p : MvPolynomial (ι × ι) ℂ) k,
      (MvPolynomial.basisMonomials (ι × ι) ℂ).repr p k = MvPolynomial.coeff k p := fun p k => rfl
  have key := GlobalTheory.T.galoisStable_submodule_le_span_rational _ _ (MvPolynomial.basisMonomials (ι × ι) ℂ) W (by
    intro σ w hw
    refine ⟨MvPolynomial.map (σ : ℂ →+* ℂ) w, ?_, ?_⟩
    · intro g hg
      rw [evC_map_ringEquiv, hw _ (hΓ σ.symm g hg), map_zero]
    · intro k
      rw [hrepr, hrepr, MvPolynomial.coeff_map]
      rfl)
  refine Submodule.span_mono ?_ (key (show f ∈ W from hf))
  rintro w ⟨hw, hq⟩
  have hl : w ∈ Set.range (MvPolynomial.map (σ := ι × ι) (algebraMap ℚ ℂ)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    simp only [Finset.mem_coe, MvPolynomial.mem_coeffs_iff] at hc
    obtain ⟨k, -, rfl⟩ := hc
    obtain ⟨q, hq⟩ := hq k
    exact ⟨q, by rw [← hrepr, hq]; rfl⟩
  obtain ⟨w₀, rfl⟩ := hl
  refine ⟨w₀, ?_, rfl⟩
  intro g hg
  rw [← evC_map_rat]
  exact hw g hg

end GlobalTheory.ClassFin
