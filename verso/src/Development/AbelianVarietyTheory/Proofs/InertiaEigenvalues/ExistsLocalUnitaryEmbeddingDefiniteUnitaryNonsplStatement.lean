import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalUnitaryEmbeddingDefiniteUnitaryNonspl
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatAtConstOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivLocProdTriv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsLocalUnitaryEmbeddingDefiniteUnitaryNonspl.lean&line=103#L103)
-/
theorem _root_.GlobalTheory.T.exists_localUnitary_embedding_definiteUnitary_nonsplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → (∀ x, Valued.v (s x) = Valued.v x) → ¬ IsSplitAt w → ∃ ι : Formalism.UG.UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) →* UA E n, Continuous ι ∧ (∀ g, ι g ∈ locU n w ∧ cLoc w (ι g) = g.1) ∧ (∀ x ∈ locU n w, cLoc w x = 1 → x = 1) ∧ ∀ x g, cLoc w x = 1 → x * ι g = ι g * x := by
  first | exact @GlobalTheory.UnitaryBC.exists_locUnitary_embedding | exact GlobalTheory.UnitaryBC.exists_locUnitary_embedding | (intros; apply GlobalTheory.UnitaryBC.exists_locUnitary_embedding <;> assumption)
