import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicCharacterOfAdmStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsDictionaryAtEmbeddingOverRealPlaceStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

namespace GlobalTheory.BridgeAdmDict

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem sz_eq (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) :
    AdmissibleParameterJ.sz D (D.nd.j i) ρ = (D.hc ρ).e (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.liftIdx D i) := by
  have := D.nd.j_range i
  unfold AdmissibleParameterJ.sz
  rw [dif_pos (by omega)]
  rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem PPm_eq (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) :
    AdmissibleParameterJ.PPm D (D.nd.j i) ρ = GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.PP D i ρ := by
  unfold AdmissibleParameterJ.PPm GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.PP GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.param GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.run
  rw [sz_eq, Finset.range_val]

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem mem_placesOver (D : D7) (i : D.nd.Loc) (τ₀ : D.host.E →+* Qbar (D.nd.l i))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (h : InducesW D.nd i τ₀ w) :
    w ∈ placesOver D.host.E (D.nd.l i) := by
  have h1 := (h ((D.nd.l i : ℕ) : 𝓞 D.host.E)).1
  show ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
  apply h1
  have e : τ₀ (((D.nd.l i : ℕ) : 𝓞 D.host.E) : D.host.E) = algebraMap ℚ_[D.nd.l i] (PadicAlgCl (D.nd.l i)) (D.nd.l i : ℚ_[D.nd.l i]) := by
    simp
  rw [e, PadicAlgCl.norm_extends]
  simpa using (Padic.norm_p_lt_one (p := D.nd.l i))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Substitute using the available equality.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Substitute using the available equality.

Establish an intermediate fact. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem main : GlobalTheory.TwSys.Cheb → ∀ D : D7, SumRepresentations.adm2 D → WeightParam D → BlockCharParam D → AdmissibleParameterJ.AdmDict D := by
  intro hC D hA hW hB
  have hAC := GlobalTheory.T.algebraic_character_of_adm D hA
  refine ⟨false, ?_⟩
  rintro i τ₀ g ρ ⟨hτ, hP⟩
  obtain ⟨b, hb, hU⟩ : ∃ b : Bool, (D.naut.iotaQC i).toRingHom.comp τ₀ = GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D ρ b ∧
      (AdmissibleParameterJ.TypeU D false g ↔ b = true) := by
    rcases hP with h | h
    · refine ⟨false, ?_, ?_⟩
      · rw [hτ, ← h]; rfl
      · subst h
        simp [AdmissibleParameterJ.TypeU, (D.eTau ρ).2]
    · refine ⟨true, ?_, ?_⟩
      · rw [hτ, ← h, Formalism.L2.Geo.emb_mul_cc_comp]; rfl
      · subst h
        have := (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau ρ).2
        simp [AdmissibleParameterJ.TypeU, this]
  obtain ⟨cτ, h1, h2⟩ := GlobalTheory.T.jumps_dictionary_at_embedding_over_realPlace D hW hB hAC hC i τ₀ ρ b hb
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.sgnOf true b, cτ, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [hU.1 h]; rfl
  · intro h
    cases b
    · rfl
    · exact absurd (hU.2 rfl) h
  · rw [PPm_eq]; exact h1
  · intro w hw
    obtain ⟨h3, h4⟩ := h2 w (mem_placesOver D i τ₀ w hw)
    refine ⟨h3, ?_⟩
    rw [show AdmissibleParameterJ.rankOneCharacterQbar D i = mapRep (iotaOQ D.nd D.naut i) (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.chiGL D i 1) from rfl, h4, sz_eq]
    rfl

end GlobalTheory.BridgeAdmDict
