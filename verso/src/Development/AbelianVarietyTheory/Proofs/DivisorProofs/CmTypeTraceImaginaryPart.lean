import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
open NumberField GlobalTheory.CMVal
open scoped ComplexConjugate

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ I _ φ hφ h mu hmu i0`. Set `ψ : I ⊕ I → (E →+* ℂ)` to `fun k => Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i)) k`. Establish `hnr : ∀ i, φ i ≠ ComplexEmbedding.conjugate (φ i)`. Introduce `i hi`. Conclude with `IsTotallyComplex.complexEmbedding_not_isReal (φ i) (ComplexEmbedding.isReal_iff.mpr hi.symm)`.

Establish `hinj : Function.Injective ψ`. Apply the tactic sequence `rintro (i | i) (j | j) hij <;> simp only [ψ, Sum.elim_inl, Sum.elim_inr] at hij`. Take `⟨k, -, hk⟩` from `hφ (φ i)`. Rewrite using `[(hk i (Or.inl rfl)).trans (hk j (Or.inl hij)).symm]`. Take `⟨k, -, hk⟩` from `hφ (φ i)`.

Establish `e` using `(hk i (Or.inl rfl)).trans (hk j (Or.inr hij)).symm`. Substitute `e` using the available equality. Conclude with `absurd hij (hnr i)`. Take `⟨k, -, hk⟩` from `hφ (φ j)`. Establish `e` using `(hk j (Or.inl rfl)).trans (hk i (Or.inr hij.symm)).symm`.

Substitute `e` using the available equality. Conclude with `absurd hij.symm (hnr j)`. Take `⟨k, -, hk⟩` from `hφ (ComplexEmbedding.conjugate (φ i))`. Rewrite using `[(hk i (Or.inr rfl)).trans (hk j (Or.inr hij)).symm]`. Establish `hsurj : Function.Surjective ψ`.

Introduce `σ`. Take `⟨k, hk, -⟩` from `hφ σ`. Break down `hk with hk | hk` into its components or cases. Conclude with `⟨Sum.inl k, hk.symm⟩`. Conclude with `⟨Sum.inr k, hk.symm⟩`.

Set `e : I ⊕ I ≃ (E →+* ℂ)` to `Equiv.ofBijective ψ ⟨hinj, hsurj⟩`. Establish `htr : ∀ x : E, ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ k, ψ k x`. Introduce `x`. Establish `h0` using `trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := x)`. Rewrite `h0` using `[eq_ratCast]`.

Rewrite using `[h0, ← Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun σ => σ x) (fun f => f x) (fun _ => by simp [RingHom.equivRatAlgHom_apply])]`. Conclude with `(Fintype.sum_equiv e (fun k => ψ k x) (fun σ => σ x) (fun _ => rfl)).symm`. Set `c : I ⊕ I → ℂ` to `Sum.elim (fun i => φ i mu - (h i : ℂ) / (2 * Complex.I)) (fun i => conj (φ i mu) + (h i : ℂ) / (2 * Complex.I))`. Establish `hz : ∀ z, ∑ k, c k * ψ k z = 0`. Introduce `z`.

Establish `h2 : ((Algebra.trace ℚ E (mu * z) : ℚ) : ℂ) = ∑ i, (h i : ℂ) * ((φ i z - conj (φ i z)) / (2 * Complex.I))`. Establish `h3` using `congrArg (fun r : ℝ => (r : ℂ)) (hmu z)`. Simplify using `only [Complex.ofReal_ratCast, Complex.ofReal_sum, Complex.ofReal_mul] at h3`. Rewrite using `[h3]`. Repeatedly rewrite using `[Complex.im_eq_sub_conj]`.

Rewrite `h2` using `[htr (mu * z)]`. Simplify using `only [Fintype.sum_sum_type, ψ, c, Sum.elim_inl, Sum.elim_inr, map_mul, ComplexEmbedding.conjugate_coe_eq] at h2 ⊢`. Rewrite `h2`, the goal using `[← Finset.sum_add_distrib]`. Rewrite `h2` using `[← sub_eq_zero, ← Finset.sum_sub_distrib]`. Rewrite using `[← h2]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hli : LinearIndependent ℂ (fun k => ((ψ k).toMonoidHom : E → ℂ))`. Use `(linearIndependent_monoidHom E ℂ).comp (fun k => (ψ k).toMonoidHom) ?_` and prove the remaining obligations. Introduce `a b hab`.

Apply `hinj` to reduce the goal to its premises. Use extensionality with `x`. Conclude with `DFunLike.congr_fun hab x`. Establish `hc` using `Fintype.linearIndependent_iff.mp hli c (by`. Use function extensionality and compare the values at `z`.

Simplify `hz z) (Sum.inl i0)` using `[Finset.sum_apply, smul_eq_mul]`. Simplify using `only [c, Sum.elim_inl, sub_eq_zero] at hc`. Establish `h2I : (2 * Complex.I) ≠ 0` using `by simp [Complex.I_ne_zero]`. Rewrite using `[hc, mul_div_cancel₀ _ h2I]`.
-/
theorem cmType_trace_im_coeff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (h : I → ℝ) (mu : E), (∀ z : E, ((Algebra.trace ℚ E (mu * z) : ℚ) : ℝ) = ∑ i, h i * (φ i z).im) →
    ∀ i, 2 * Complex.I * φ i mu = (h i : ℂ) := by
  intro E _ _ _ I _ φ hφ h mu hmu i0
  classical
  let ψ : I ⊕ I → (E →+* ℂ) := fun k => Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i)) k
  have hnr : ∀ i, φ i ≠ ComplexEmbedding.conjugate (φ i) := by
    intro i hi
    exact IsTotallyComplex.complexEmbedding_not_isReal (φ i) (ComplexEmbedding.isReal_iff.mpr hi.symm)
  have hinj : Function.Injective ψ := by
    rintro (i | i) (j | j) hij <;> simp only [ψ, Sum.elim_inl, Sum.elim_inr] at hij
    · obtain ⟨k, -, hk⟩ := hφ (φ i)
      rw [(hk i (Or.inl rfl)).trans (hk j (Or.inl hij)).symm]
    · obtain ⟨k, -, hk⟩ := hφ (φ i)
      have e := (hk i (Or.inl rfl)).trans (hk j (Or.inr hij)).symm
      subst e; exact absurd hij (hnr i)
    · obtain ⟨k, -, hk⟩ := hφ (φ j)
      have e := (hk j (Or.inl rfl)).trans (hk i (Or.inr hij.symm)).symm
      subst e; exact absurd hij.symm (hnr j)
    · obtain ⟨k, -, hk⟩ := hφ (ComplexEmbedding.conjugate (φ i))
      rw [(hk i (Or.inr rfl)).trans (hk j (Or.inr hij)).symm]
  have hsurj : Function.Surjective ψ := by
    intro σ
    obtain ⟨k, hk, -⟩ := hφ σ
    rcases hk with hk | hk
    · exact ⟨Sum.inl k, hk.symm⟩
    · exact ⟨Sum.inr k, hk.symm⟩
  let e : I ⊕ I ≃ (E →+* ℂ) := Equiv.ofBijective ψ ⟨hinj, hsurj⟩
  have htr : ∀ x : E, ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ k, ψ k x := by
    intro x
    have h0 := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := x)
    rw [eq_ratCast] at h0
    rw [h0, ← Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun σ => σ x) (fun f => f x)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply])]
    exact (Fintype.sum_equiv e (fun k => ψ k x) (fun σ => σ x) (fun _ => rfl)).symm
  let c : I ⊕ I → ℂ := Sum.elim (fun i => φ i mu - (h i : ℂ) / (2 * Complex.I))
    (fun i => conj (φ i mu) + (h i : ℂ) / (2 * Complex.I))
  have hz : ∀ z, ∑ k, c k * ψ k z = 0 := by
    intro z
    have h2 : ((Algebra.trace ℚ E (mu * z) : ℚ) : ℂ) =
        ∑ i, (h i : ℂ) * ((φ i z - conj (φ i z)) / (2 * Complex.I)) := by
      have h3 := congrArg (fun r : ℝ => (r : ℂ)) (hmu z)
      simp only [Complex.ofReal_ratCast, Complex.ofReal_sum, Complex.ofReal_mul] at h3
      rw [h3]
      simp_rw [Complex.im_eq_sub_conj]
    rw [htr (mu * z)] at h2
    simp only [Fintype.sum_sum_type, ψ, c, Sum.elim_inl, Sum.elim_inr, map_mul,
      ComplexEmbedding.conjugate_coe_eq] at h2 ⊢
    rw [← Finset.sum_add_distrib] at h2 ⊢
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hli : LinearIndependent ℂ (fun k => ((ψ k).toMonoidHom : E → ℂ)) := by
    refine (linearIndependent_monoidHom E ℂ).comp (fun k => (ψ k).toMonoidHom) ?_
    intro a b hab
    apply hinj
    ext x
    exact DFunLike.congr_fun hab x
  have hc := Fintype.linearIndependent_iff.mp hli c (by
    funext z
    simpa [Finset.sum_apply, smul_eq_mul] using hz z) (Sum.inl i0)
  simp only [c, Sum.elim_inl, sub_eq_zero] at hc
  have h2I : (2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
  rw [hc, mul_div_cancel₀ _ h2I]

end GlobalTheory
