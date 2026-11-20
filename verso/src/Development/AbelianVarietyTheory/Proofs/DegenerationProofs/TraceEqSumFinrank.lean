import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceEqFinrankMulSum
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.Ex.Arch

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem exists_types (m : (E →+* ℂ) → ℕ) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)),
    (∀ φ, Nat.card {i // ty i = φ} = m φ) ∧ ∀ a : E, ∑ i, ty i a = ∑ φ : E →+* ℂ, (m φ : ℂ) * φ a := by
  classical
  let e := (Fintype.equivFin (Σ φ : E →+* ℂ, Fin (m φ))).symm
  refine ⟨_, fun i => (e i).1, fun φ => ?_, fun a => ?_⟩
  · rw [Nat.card_congr (e.subtypeEquiv (q := fun k => k.1 = φ) fun _ => Iff.rfl),
      Nat.card_congr (Equiv.sigmaSubtype φ)]
    simp
  · rw [e.sum_comp fun k => k.1 a, Fintype.sum_sigma]
    simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem trace_eq_sum_finrank {g : ℕ} (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (a : 𝓞 E) :
    LinearMap.trace ℂ _ (ρ a) = ∑ φ : E →+* ℂ,
      (Module.finrank ℂ (EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E))) : ℂ) * φ (a : E) := by
  obtain ⟨g', ty, hc, hs⟩ :=
    exists_types fun φ : E →+* ℂ => Module.finrank ℂ (EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E)))
  obtain ⟨h, hh⟩ := PointUnif.exists_equiv_of_finrank_eq (PointUnif.isSplitting_embeddings (E := E))
    (PointUnif.diagRep ty) ρ fun φ => by rw [PointUnif.finrank_eigenSub_diagRep, hc]
  have h1 : ρ a = h.conj (PointUnif.diagRep ty a) := LinearMap.ext fun v => by simp [LinearEquiv.conj_apply, hh]
  have h2 : PointUnif.diagRep ty a = Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E)) :=
    LinearMap.ext fun z => funext fun i => by simp [PointUnif.diagRep_apply, Matrix.mulVec_diagonal]
  rw [h1, LinearMap.trace_conj', h2, ← hs]
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem typeSt : TypeSt := by
  intro E _ _ _ H D
  let _ := H.starRing
  intro B hB
  classical
  obtain ⟨g, ty, hc, hs⟩ := exists_types fun φ : E →+* ℂ => if φ (H.rt : E) = H.rt0 then D.p else D.q
  have hbar : ∀ a : 𝓞 E, ∑ τ : E →+* ℂ, τ (H.bar a : E) = ∑ τ : E →+* ℂ, τ (a : E) := fun a => by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro τ _; exact Finset.mem_univ _
    · intro τ _; exact Finset.mem_univ _
    · intro τ _; ext x; simp
    · intro τ _; ext x; simp
    · intro τ _
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
  have := HomTrace.finite_hom B.X
  obtain ⟨h, hh⟩ := PeriodNonempty.exists_diag B.actV ty fun a => by
    let f : (B.X →+ ℂ) →ₗ[ℂ] (B.X →+ ℂ) := LinearMap.fst ℂ _ _ ∘ₗ B.actV a ∘ₗ LinearMap.inl ℂ _ _
    have h1 : B.actV a = f.prodMap (B.F a) := LinearMap.ext fun v => rfl
    rw [h1, LinearMap.trace_prodMap', HomTrace.trace_eq_finrank_mul_sum E B.X (H.bar a) f fun _ _ => rfl, hbar,
      trace_eq_sum_finrank, hs, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun φ _ => ?_
    have h2 : Module.finrank ℂ (EigenSplit.eigenSub B.F (φ.comp (algebraMap (𝓞 E) E))) + Module.finrank (𝓞 E) B.X =
        if φ (H.rt : E) = H.rt0 then D.p else D.q := by
      have h3 := hB (φ.comp (algebraMap (𝓞 E) E))
      by_cases hφ : φ (H.rt : E) = H.rt0
      · rw [if_pos hφ]; exact h3.trans (if_pos hφ)
      · rw [if_neg hφ]; exact h3.trans (if_neg hφ)
    rw [← h2]
    push_cast
    ring
  exact ⟨g, ty, h, fun φ => ⟨fun hφ => (hc φ).trans (if_pos hφ), fun hφ => (hc φ).trans (if_neg hφ)⟩, hh⟩

end GlobalTheory.Ex.Arch

end
