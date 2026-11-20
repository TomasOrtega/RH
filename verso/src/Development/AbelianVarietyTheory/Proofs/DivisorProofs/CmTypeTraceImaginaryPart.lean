import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
open NumberField GlobalTheory.CMVal
open scoped ComplexConjugate

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Apply the first step, then apply the next step to every resulting obligation. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Substitute using the available equality. Extract witnesses or component facts from the available result. Establish an intermediate fact. Substitute using the available equality. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis.

Supply the required witnesses or components. Supply the required witnesses or components. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion repeatedly using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
