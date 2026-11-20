import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FunctionalFixedByIdempotentRepresentedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdempotentFiniteRankAdjointCuspidalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConjSelfDualOfInvTransposeIsoCmConjStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepDualIsoOfCommonRepresentedFunctionalStatement

noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CsdBack

/- English proof (translation)
Introduce `o`. Consider the cases of `o with`. Consider the case `fin k => simp only [invTOp]`. Use `congr 1`. Consider the case `cpt k => simp only [invTOp]`.

Use `congr 1`. Use extensionality with `i j`. Simplify using `[barK, Matrix.star_apply]`. Consider the case `lie X`. Simplify using `only [invTOp]`.

Use `congr 1`. Use function extensionality and compare the values at `i j`. Conclude with `neg_neg (X i j)`.
-/
theorem invTOp_involutive {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} :
    Function.Involutive (invTOp : Op E a → Op E a) := by
  intro o
  cases o with
  | fin k => simp only [invTOp]; congr 1
  | cpt k => simp only [invTOp]; congr 1; ext i j; simp [barK, Matrix.star_apply]
  | lie X =>
    simp only [invTOp]; congr 1
    funext i j
    exact neg_neg (X i j)

/- English proof (translation)
Introduce `o`. Consider the cases of `o with`. Consider the case `fin k => simp only [conjOp]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `[GlobalTheory.ThetaPull.cFin_cFin]`. Consider the case `cpt k => simp only [conjOp]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[barK, Matrix.star_apply]`.

Consider the case `lie X => simp only [conjOp]`. Use `congr 1`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem conjOp_involutive {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ} :
    Function.Involutive (conjOp : Op L a → Op L a) := by
  intro o
  cases o with
  | fin k => simp only [conjOp]; congr 1; ext i j; simp [GlobalTheory.ThetaPull.cFin_cFin]
  | cpt k => simp only [conjOp]; congr 1; ext i j; simp [barK, Matrix.star_apply]
  | lie X => simp only [conjOp]; congr 1; ext i j; simp

/- English proof (translation)
Introduce `hP L _ _ _ a π h1 h2`. Take `⟨B₁, l1, r1, f1, c1, x1⟩` from `h1`. Take `⟨B₂, l2, r2, f2, c2, x2⟩` from `h2`. Take `⟨P, hP0, hPP, hfin, hadj⟩` from `GlobalTheory.T.exists_idempotent_finiteRank_adjoint_cuspidal hP L a π`. Take `⟨P₁, e1⟩` from `hadj invTOp (Or.inl rfl) B₁ l1 r1 f1 c1 x1`.

Take `⟨P₂, e2⟩` from `hadj conjOp (Or.inr rfl) B₂ l2 r2 f2 c2 x2`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, P v ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hP0 (LinearMap.ext h)`.

Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g : Module.Dual ℂ π.V, g (P v) ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hv ((Module.forall_dual_apply_eq_zero_iff ℂ (P v)).1 h)`. Establish `hf : (g ∘ₗ P) ∘ₗ P = g ∘ₗ P` using `by rw [LinearMap.comp_assoc, hPP]`.

Take `⟨ψ₁, hψ₁⟩` from `GlobalTheory.T.exists_representing_of_comp_idempotent_of_nondegenerate B₁ l1 r1 P P₁ hPP hfin e1 (g ∘ₗ P) hf`. Take `⟨ψ₂, hψ₂⟩` from `GlobalTheory.T.exists_representing_of_comp_idempotent_of_nondegenerate B₂ l2 r2 P P₂ hPP hfin e2 (g ∘ₗ P) hf`. Establish `hne : ψ₁ ≠ 0`. Introduce and unpack `rfl`. Apply `hg` to reduce the goal to its premises.

Use `hψ₁ v` as an intermediate fact. Simplify using `only [map_zero, LinearMap.comp_apply] at this`. Conclude with `this.symm`. Take `⟨S, hS⟩` from `GlobalTheory.T.cuspRep_dual_iso_of_common_represented_functional L a π invTOp conjOp invTOp_involutive conjOp_involutive B₁ B₂ l1 r1 f1 c1 x1 l2 r2 f2 c2 x2 ψ₁ ψ₂ hne (fun φ => (hψ₁ φ).trans (hψ₂ φ).symm)`. Conclude with `GlobalTheory.T.isConjSelfDual_of_invTranspose_iso_cmConj L a π S hS`.
-/
theorem isCsd_of_paired : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (a : ℕ) (π : CuspSub L a), Paired π π invTOp → DualIsConj π → π.IsCsd := by
  intro hP L _ _ _ a π h1 h2
  obtain ⟨B₁, l1, r1, f1, c1, x1⟩ := h1
  obtain ⟨B₂, l2, r2, f2, c2, x2⟩ := h2
  obtain ⟨P, hP0, hPP, hfin, hadj⟩ := GlobalTheory.T.exists_idempotent_finiteRank_adjoint_cuspidal hP L a π
  obtain ⟨P₁, e1⟩ := hadj invTOp (Or.inl rfl) B₁ l1 r1 f1 c1 x1
  obtain ⟨P₂, e2⟩ := hadj conjOp (Or.inr rfl) B₂ l2 r2 f2 c2 x2
  obtain ⟨v, hv⟩ : ∃ v, P v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP0 (LinearMap.ext h)
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual ℂ π.V, g (P v) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ (P v)).1 h)
  have hf : (g ∘ₗ P) ∘ₗ P = g ∘ₗ P := by rw [LinearMap.comp_assoc, hPP]
  obtain ⟨ψ₁, hψ₁⟩ := GlobalTheory.T.exists_representing_of_comp_idempotent_of_nondegenerate B₁ l1 r1 P P₁ hPP hfin e1 (g ∘ₗ P) hf
  obtain ⟨ψ₂, hψ₂⟩ := GlobalTheory.T.exists_representing_of_comp_idempotent_of_nondegenerate B₂ l2 r2 P P₂ hPP hfin e2 (g ∘ₗ P) hf
  have hne : ψ₁ ≠ 0 := by
    rintro rfl
    apply hg
    have := hψ₁ v
    simp only [map_zero, LinearMap.comp_apply] at this
    exact this.symm
  obtain ⟨S, hS⟩ := GlobalTheory.T.cuspRep_dual_iso_of_common_represented_functional L a π invTOp conjOp invTOp_involutive conjOp_involutive B₁ B₂ l1 r1 f1 c1 x1
    l2 r2 f2 c2 x2 ψ₁ ψ₂ hne (fun φ => (hψ₁ φ).trans (hψ₂ φ).symm)
  exact GlobalTheory.T.isConjSelfDual_of_invTranspose_iso_cmConj L a π S hS

end GlobalTheory.CsdBack

end
