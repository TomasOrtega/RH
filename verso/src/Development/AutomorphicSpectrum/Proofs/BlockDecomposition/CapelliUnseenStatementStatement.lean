import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliAuxiliaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCapelliAuxiliaryStatement.lean&line=164#L164)
-/
theorem _root_.GlobalTheory.T.capelli_restrict_levi : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) (q : Polynomial ℂ) (F : Sm E (r + s)), (∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ m, (Polynomial.aeval (cap (a := r) τ u) q G).1 m = (Polynomial.aeval (capR r s τ u) q F).1 (lev (Ad E) r s (m, 1))) ∧ (∀ G : Sm E s, (∀ m, G.1 m = F.1 (lev (Ad E) r s (1, m))) → ∀ m, (Polynomial.aeval (cap (a := s) τ u) q G).1 m = (Polynomial.aeval (capS r s τ u) q F).1 (lev (Ad E) r s (1, m))) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.capelli_restrict | exact GlobalTheory.CompanionTheory.CTFin.capelli_restrict | (intros; apply GlobalTheory.CompanionTheory.CTFin.capelli_restrict <;> assumption)
