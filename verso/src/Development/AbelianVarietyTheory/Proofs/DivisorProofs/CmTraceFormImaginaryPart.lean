import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

namespace GlobalTheory.CMTrace

/- English proof (translation)
Establish `hnr : ∀ i, ComplexEmbedding.conjugate (φ i) ≠ φ i` using `fun i h => InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (φ i))) (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h))`. Set `f : I ⊕ I → (E →+* ℂ)` to `Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(i | i) (j | j) h`.

Simplify using `only [f, Sum.elim_inl] at h`. Take `⟨k, _, hk⟩` from `hφ (φ i)`. Rewrite using `[hk i (Or.inl rfl), hk j (Or.inl h)]`. Simplify using `only [f, Sum.elim_inl, Sum.elim_inr] at h`. Take `⟨k, _, hk⟩` from `hφ (φ i)`.

Establish `hi` using `hk i (Or.inl rfl)`. Establish `hj` using `hk j (Or.inr h)`. Substitute `hi` using the available equality. Substitute `hj` using the available equality. Conclude with `absurd h.symm (hnr _)`.

Simplify using `only [f, Sum.elim_inl, Sum.elim_inr] at h`. Take `⟨k, _, hk⟩` from `hφ (φ j)`. Establish `hi` using `hk i (Or.inr h.symm)`. Establish `hj` using `hk j (Or.inl rfl)`. Substitute `hi` using the available equality.

Substitute `hj` using the available equality. Conclude with `absurd h (hnr _)`. Simplify using `only [f, Sum.elim_inr] at h`. Establish `h' : φ i = φ j`. Use `congrArg ComplexEmbedding.conjugate h` as an intermediate fact.

Simplify using `using this`. Take `⟨k, _, hk⟩` from `hφ (φ i)`. Rewrite using `[hk i (Or.inl rfl), hk j (Or.inl h')]`. Introduce `σ`. Take `⟨i, hi, _⟩` from `hφ σ`.

Break down `hi with h | h` into its components or cases. Conclude with `⟨Sum.inl i, h.symm⟩`. Conclude with `⟨Sum.inr i, h.symm⟩`. Rewrite using `[← Fintype.sum_bijective f hf (g ∘ f) g (fun _ => rfl), Fintype.sum_sum_type, ← Finset.sum_add_distrib]`. Both sides reduce to the same expression.
-/
theorem sum_embeddings_cmType {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) (g : (E →+* ℂ) → ℂ) :
    ∑ σ : E →+* ℂ, g σ = ∑ i, (g (φ i) + g (ComplexEmbedding.conjugate (φ i))) := by
  have hnr : ∀ i, ComplexEmbedding.conjugate (φ i) ≠ φ i := fun i h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (φ i)))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h))
  let f : I ⊕ I → (E →+* ℂ) := Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))
  have hf : Function.Bijective f := by
    constructor
    · rintro (i | i) (j | j) h
      · simp only [f, Sum.elim_inl] at h
        obtain ⟨k, _, hk⟩ := hφ (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl h)]
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at h
        obtain ⟨k, _, hk⟩ := hφ (φ i)
        have hi := hk i (Or.inl rfl)
        have hj := hk j (Or.inr h)
        subst hi; subst hj
        exact absurd h.symm (hnr _)
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at h
        obtain ⟨k, _, hk⟩ := hφ (φ j)
        have hi := hk i (Or.inr h.symm)
        have hj := hk j (Or.inl rfl)
        subst hi; subst hj
        exact absurd h (hnr _)
      · simp only [f, Sum.elim_inr] at h
        have h' : φ i = φ j := by
          have := congrArg ComplexEmbedding.conjugate h
          simpa using this
        obtain ⟨k, _, hk⟩ := hφ (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl h')]
    · intro σ
      obtain ⟨i, hi, _⟩ := hφ σ
      rcases hi with h | h
      · exact ⟨Sum.inl i, h.symm⟩
      · exact ⟨Sum.inr i, h.symm⟩
  rw [← Fintype.sum_bijective f hf (g ∘ f) g (fun _ => rfl), Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  rfl

/- English proof (translation)
Establish `h1 : ((Algebra.trace ℚ E w : ℚ) : ℂ) = ∑ σ : E →ₐ[ℚ] ℂ, σ w`. Rewrite using `[← trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ)]`. Simplify using the standard rewrite rules. Establish `h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ w = ∑ σ : E →+* ℂ, σ w` using `(Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun _ => rfl))`. Establish `h3` using `sum_embeddings_cmType φ hφ (fun σ => σ w)`.

Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[Complex.ofReal_ratCast, h1, h2, h3]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trace_eq_sum_re {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) (w : E) :
    ((Algebra.trace ℚ E w : ℚ) : ℝ) = ∑ i, 2 * (φ i w).re := by
  have h1 : ((Algebra.trace ℚ E w : ℚ) : ℂ) = ∑ σ : E →ₐ[ℚ] ℂ, σ w := by
    rw [← trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ)]
    simp
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ w = ∑ σ : E →+* ℂ, σ w :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun _ => rfl))
  have h3 := sum_embeddings_cmType φ hφ (fun σ => σ w)
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, h1, h2, h3]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]
  push_cast; ring

end GlobalTheory.CMTrace

open GlobalTheory.CMTrace in
/- English proof (translation)
Introduce `E _ _ _ I _ φ hφ n e t₁ ρ ht a x y`. Rewrite using `[trace_eq_sum_re φ hφ, Complex.im_sum, Equiv.sum_comp e (fun i => ((φ i (a : E) * (ρ : ℂ)) * φ i x * starRingEnd ℂ (φ i y)).im)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `ha : starRingEnd ℂ (φ i (a : E)) = φ i (a : E)`. Rewrite using `[← IsCMField.complexEmbedding_complexConj]`.

Use `congr 1`. Conclude with `(IsCMField.complexConj E).commutes a`. Establish `hre : φ i (a : E) = ((φ i (a : E)).re : ℂ)` using `(Complex.conj_eq_iff_re.1 ha).symm`. Establish `hb : φ i (bar y) = starRingEnd ℂ (φ i y)` using `IsCMField.complexEmbedding_complexConj E (φ i) y`. Rewrite using `[map_mul, map_mul, map_mul, hb, ht i, hre]`.

Simplify using `only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.trace_riemannForm_eq_im : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (t₁ : E) (ρ : ℝ), (∀ i, φ i t₁ = -Complex.I * ((ρ / 2 : ℝ) : ℂ)) →
    ∀ (a : FR E) (x y : E), ((Algebra.trace ℚ E ((a : E) * t₁ * x * bar y) : ℚ) : ℝ) =
      (∑ j, (φ (e j) (a : E) * (ρ : ℂ)) * φ (e j) x * starRingEnd ℂ (φ (e j) y)).im := by
  intro E _ _ _ I _ φ hφ n e t₁ ρ ht a x y
  rw [trace_eq_sum_re φ hφ, Complex.im_sum, Equiv.sum_comp e (fun i => ((φ i (a : E) * (ρ : ℂ)) * φ i x * starRingEnd ℂ (φ i y)).im)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have ha : starRingEnd ℂ (φ i (a : E)) = φ i (a : E) := by
    rw [← IsCMField.complexEmbedding_complexConj]
    congr 1
    exact (IsCMField.complexConj E).commutes a
  have hre : φ i (a : E) = ((φ i (a : E)).re : ℂ) := (Complex.conj_eq_iff_re.1 ha).symm
  have hb : φ i (bar y) = starRingEnd ℂ (φ i y) := IsCMField.complexEmbedding_complexConj E (φ i) y
  rw [map_mul, map_mul, map_mul, hb, ht i, hre]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring
