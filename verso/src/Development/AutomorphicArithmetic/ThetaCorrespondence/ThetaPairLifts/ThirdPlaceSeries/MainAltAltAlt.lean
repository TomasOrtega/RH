import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleDictionaryOfParams
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlgebraicCharacterOfAdm

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary
namespace GlobalTheory.BridgeAdmDict
/- English proof (translation)
Introduce `hC D hA hW hB`. Establish `hAC` using `_root_.GlobalTheory.T.algebraicCharacter_of_adm2 D hA`. Use `⟨false, ?_⟩` and prove the remaining obligations. Introduce and unpack `i τ₀ g ρ ⟨hτ, hP⟩`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb, hU⟩ : ∃ b : Bool, (D.naut.iotaQC i).toRingHom.comp τ₀ = GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D ρ b ∧ (AdmissibleParameterJ.TypeU D false g ↔ b = true) := by`.

Break down `hP with h | h` into its components or cases. Use `⟨false, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hτ, ← h]`. Both sides reduce to the same expression. Substitute `h` using the available equality.

Simplify using `[AdmissibleParameterJ.TypeU, (D.eTau ρ).2]`. Use `⟨true, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hτ, ← h, Formalism.L2.Geo.emb_mul_cc_comp]`. Both sides reduce to the same expression. Substitute `h` using the available equality.

Use `(Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau ρ).2` as an intermediate fact. Simplify using `[AdmissibleParameterJ.TypeU, this]`. Take `⟨cτ, h1, h2⟩` from `GlobalTheory.T.jumps_dictionary_at_embedding_over_realPlace D hW hB hAC hC i τ₀ ρ b hb`. Use `⟨GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.sgnOf true b, cτ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`.

Rewrite using `[hU.1 h]`. Both sides reduce to the same expression. Introduce `h`. Consider the cases of `b`. Both sides reduce to the same expression.

Conclude with `absurd (hU.2 rfl) h`. Rewrite using `[PPm_eq]`. Conclude with `h1`. Introduce `w hw`. Take `⟨h3, h4⟩` from `h2 w (mem_placesOver D i τ₀ w hw)`.

Use `⟨h3, ?_⟩` and prove the remaining obligations. Rewrite using `[show AdmissibleParameterJ.rankOneCharacterQbar D i = mapRep (iotaOQ D.nd D.naut i) (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.chiGL D i 1) from rfl, h4, sz_eq]`. Both sides reduce to the same expression.
-/
theorem main_alt_alt : GlobalTheory.TwSys.Cheb → ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → WeightParam D → BlockCharParam D → AdmissibleParameterJ.AdmDict D := by
  intro hC D hA hW hB
  have hAC := _root_.GlobalTheory.T.algebraicCharacter_of_adm2 D hA
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
end
