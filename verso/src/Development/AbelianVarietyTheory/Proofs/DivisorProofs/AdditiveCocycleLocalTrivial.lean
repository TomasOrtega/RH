import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleHolomorphicCoboundaryLocal
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.RealTranslCob

/- English proof (translation)
By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem per_single_inr {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (i : Fin g) :
    per τ (Pi.single (Sum.inr i) (1 : ℝ)) = Pi.single i 1 := by
  ext k
  by_cases h : k = i
  · subst h; simp [per, Matrix.vecMul, dotProduct]
  · simp [per, Matrix.vecMul, dotProduct, h, Pi.single_apply]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem single_inr_mem_stdLat {g : ℕ} (i : Fin g) :
    Pi.single (Sum.inr i) (1 : ℝ) ∈ stdLat g := by
  refine Submodule.subset_span ⟨Sum.inr i, ?_⟩
  simp [Pi.basisFun_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem exists_cob_real {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap U τ) (H : Fl g → Pt E g → ℂ)
    (hH : ∀ l ∈ stdLat g, DifferentiableOn ℂ (H l) (cov U g))
    (hc : ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ P ∈ cov U g,
      H (l + l') P = H l (transl τ l' P) + H l' P) :
    ∀ b ∈ U, ∃ V : Set E, IsOpen V ∧ b ∈ V ∧ V ⊆ U ∧ ∃ K : Pt E g → ℂ,
      DifferentiableOn ℂ K (cov V g) ∧ ∀ i : Fin g, ∀ P ∈ cov V g,
        H (Pi.single (Sum.inr i) (1 : ℝ)) P =
          K (transl τ (Pi.single (Sum.inr i) (1 : ℝ)) P) - K P := by
  intro b hb
  have htr : ∀ (i : Fin g) (P : Pt E g),
      transl τ (Pi.single (Sum.inr i) (1 : ℝ)) P = (P.1, P.2 + Pi.single i 1) := by
    intro i P
    simp only [transl, per_single_inr]
  obtain ⟨r, hr, hball, ψ, hψ, hψeq⟩ := GlobalTheory.RealPeriodCocycle.main hτ.1
    (fun k => H (Pi.single (Sum.inr k) (1 : ℝ)))
    (fun k => hH _ (single_inr_mem_stdLat k))
    (by
      intro k j P hP
      have h1 := hc _ (single_inr_mem_stdLat k) _ (single_inr_mem_stdLat j) P hP
      have h2 := hc _ (single_inr_mem_stdLat j) _ (single_inr_mem_stdLat k) P hP
      rw [add_comm, h2, htr, htr] at h1
      simpa using h1.symm)
    b hb
  refine ⟨Metric.ball b r, Metric.isOpen_ball, Metric.mem_ball_self hr, hball, ψ, hψ, ?_⟩
  intro i P hP
  rw [htr, hψeq i P hP]
  ring

end GlobalTheory.RealTranslCob

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem GlobalTheory.RealTranslCob.main : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap U τ →
    ∀ H : Fl g → Pt E g → ℂ, (∀ l ∈ stdLat g, DifferentiableOn ℂ (H l) (cov U g)) →
    (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ P ∈ cov U g, H (l + l') P = H l (transl τ l' P) + H l' P) →
    ∀ b ∈ U, ∃ V : Set E, IsOpen V ∧ b ∈ V ∧ V ⊆ U ∧ ∃ K : Pt E g → ℂ,
      DifferentiableOn ℂ K (cov V g) ∧ ∀ i : Fin g, ∀ P ∈ cov V g,
        H (Pi.single (Sum.inr i) (1 : ℝ)) P =
          K (transl τ (Pi.single (Sum.inr i) (1 : ℝ)) P) - K P :=
  fun hτ H hH hc => GlobalTheory.RealTranslCob.exists_cob_real hτ H hH hc
