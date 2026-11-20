import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceEqFinrankMulSum
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.Ex.Arch

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Set `e` to `(Fintype.equivFin (Σ φ : E →+* ℂ, Fin (m φ))).symm`. Use `⟨_, fun i => (e i).1, fun φ => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.card_congr (e.subtypeEquiv (q := fun k => k.1 = φ) fun _ => Iff.rfl), Nat.card_congr (Equiv.sigmaSubtype φ)]`. Simplify using the standard rewrite rules. Rewrite using `[e.sum_comp fun k => k.1 a, Fintype.sum_sigma]`.

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
Take `⟨g', ty, hc, hs⟩` from `exists_types fun φ : E →+* ℂ => Module.finrank ℂ (EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E)))`. Take `⟨h, hh⟩` from `PointUnif.exists_equiv_of_finrank_eq (PointUnif.isSplitting_embeddings (E := E)) (PointUnif.diagRep ty) ρ fun φ => by rw [PointUnif.finrank_eigenSub_diagRep, hc]`. Establish `h1 : ρ a = h.conj (PointUnif.diagRep ty a)` using `LinearMap.ext fun v => by simp [LinearEquiv.conj_apply, hh]`. Establish `h2 : PointUnif.diagRep ty a = Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E))` using `LinearMap.ext fun z => funext fun i => by simp [PointUnif.diagRep_apply, Matrix.mulVec_diagonal]`. Rewrite using `[h1, LinearMap.trace_conj', h2, ← hs]`.

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
Introduce `E _ _ _ H D`. Set `_` to `H.starRing`. Introduce `B hB`. Take `⟨g, ty, hc, hs⟩` from `exists_types fun φ : E →+* ℂ => if φ (H.rt : E) = H.rt0 then D.p else D.q`. Establish `hbar : ∀ a : 𝓞 E, ∑ τ : E →+* ℂ, τ (H.bar a : E) = ∑ τ : E →+* ℂ, τ (a : E)` using `fun a => by`.

Use `Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `τ _`. Conclude with `Finset.mem_univ _`. Introduce `τ _`. Conclude with `Finset.mem_univ _`.

Introduce `τ _`. Use extensionality with `x`. Simplify using the standard rewrite rules. Introduce `τ _`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Introduce `τ _`. Rewrite using `[H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]`. Use `HomTrace.finite_hom B.X` as an intermediate fact. Take `⟨h, hh⟩` from `PeriodNonempty.exists_diag B.actV ty fun a => by`.

Set `f : (B.X →+ ℂ) →ₗ[ℂ] (B.X →+ ℂ)` to `LinearMap.fst ℂ _ _ ∘ₗ B.actV a ∘ₗ LinearMap.inl ℂ _ _`. Establish `h1 : B.actV a = f.prodMap (B.F a)` using `LinearMap.ext fun v => rfl`. Rewrite using `[h1, LinearMap.trace_prodMap', HomTrace.trace_eq_finrank_mul_sum E B.X (H.bar a) f fun _ _ => rfl, hbar, trace_eq_sum_finrank, hs, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun φ _ => ?_` and prove the remaining obligations. Establish `h2 : Module.finrank ℂ (EigenSplit.eigenSub B.F (φ.comp (algebraMap (𝓞 E) E))) + Module.finrank (𝓞 E) B.X = if φ (H.rt : E) = H.rt0 then D.p else D.q`.

Establish `h3` using `hB (φ.comp (algebraMap (𝓞 E) E))`. Distinguish the cases in `hφ : φ (H.rt : E) = H.rt0`. Rewrite using `[if_pos hφ]`. Conclude with `h3.trans (if_pos hφ)`. Rewrite using `[if_neg hφ]`.

Conclude with `h3.trans (if_neg hφ)`. Rewrite using `[← h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨g, ty, h, fun φ => ⟨fun hφ => (hc φ).trans (if_pos hφ), fun hφ => (hc φ).trans (if_neg hφ)⟩, hh⟩`.
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
