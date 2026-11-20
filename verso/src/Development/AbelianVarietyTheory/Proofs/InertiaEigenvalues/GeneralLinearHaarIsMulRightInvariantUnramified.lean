import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantOfModular
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

/- English proof (translation)
Use `haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F`. Use `haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F) := inferInstanceAs (SecondCountableTopology (Fin r → Fin r → F))`. Use `haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) F) := inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → F))`. Use `haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ := (MulOpposite.opHomeomorph (M := Matrix (Fin r) (Fin r) F)).symm.secondCountableTopology`. Conclude with `⟨Units.isClosedEmbedding_embedProduct.locallyCompactSpace, Units.isEmbedding_embedProduct.secondCountableTopology⟩`.
-/
theorem gl_lc_sc (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (r : ℕ) :
    LocallyCompactSpace (GL (Fin r) F) ∧ SecondCountableTopology (GL (Fin r) F) := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → F))
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → F))
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin r) (Fin r) F)).symm.secondCountableTopology
  exact ⟨Units.isClosedEmbedding_embedProduct.locallyCompactSpace,
    Units.isEmbedding_embedProduct.secondCountableTopology⟩

/- English proof (translation)
Introduce `F E _ _ _ _ hU r M`. Use `haveI : LocallyCompactSpace F := hU.lcF`. Take `⟨h1, h2⟩` from `gl_lc_sc F r`. Use `letI := M.mG`. Use `haveI := M.bG`.

Use `haveI := M.haarG`. Use `⟨fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) M.μG) M.μG, ← Measure.modularCharacterFun_eq_haarScalarFactor, GlobalTheory.ParAvg.modularCharacterFun_GL, one_smul]`.
-/
theorem gl_unimodular : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (letI := M.mG; M.μG.IsMulRightInvariant) := by
  intro F E _ _ _ _ hU r M
  haveI : LocallyCompactSpace F := hU.lcF
  obtain ⟨h1, h2⟩ := gl_lc_sc F r
  letI := M.mG
  haveI := M.bG
  haveI := M.haarG
  refine ⟨fun g => ?_⟩
  rw [Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) M.μG) M.μG,
    ← Measure.modularCharacterFun_eq_haarScalarFactor, GlobalTheory.ParAvg.modularCharacterFun_GL, one_smul]

end GlobalTheory.JR
