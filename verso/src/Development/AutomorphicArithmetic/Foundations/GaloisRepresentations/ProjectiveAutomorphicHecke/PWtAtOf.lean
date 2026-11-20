import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitePartAtOwnWeightNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAutomorphicOfWeightOfNonzeroFixedFinPartForm
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

/- English proof (translation)
Introduce `E _ _ _ n _ π`. Use `⟨⟨(AU.mk π).wt, AutSub.finPart_wt_ne_bot E n π⟩, fun W hW τ lam hlam => ?_⟩` and prove the remaining obligations. Take `⟨f, hf, hf0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hW`. Establish `hT` using `GlobalTheory.Cong.ofType_of_finPart_fixed E n π W ⊥ f hf hf0 (by`. Introduce `k hk v g`.

Rewrite using `[Subgroup.mem_bot.1 hk, mul_one])`. Conclude with `hasWeightAt_unique π τ hlam (hT.wt τ)`.
-/
theorem UpperTheory.Gal.CertificateRingHomMap.pWtAt_of :
    UpperTheory.Gal.CertificateRingHomMap.WtAt := by
  intro E _ _ _ n _ π
  refine ⟨⟨(AU.mk π).wt, AutSub.finPart_wt_ne_bot E n π⟩, fun W hW τ lam hlam => ?_⟩
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hT :=
    GlobalTheory.Cong.ofType_of_finPart_fixed E n π W ⊥ f hf hf0 (by
      intro k hk v g
      rw [Subgroup.mem_bot.1 hk, mul_one])
  exact hasWeightAt_unique π τ hlam (hT.wt τ)
