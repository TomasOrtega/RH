import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFinitePointReadsClassicalTranslationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroStandardThetaLineReadAdelicStatement

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormExact.ReadEx

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_nonzero_standardThetaLine_read_adelic`.
-/
theorem exists_vac_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∃ e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d), e0 ≠ 0 ∧ ∃ f₀, Reads ψ θ hS hT cc δ r e0 f₀ := GlobalTheory.T.exists_nonzero_standardThetaLine_read_adelic

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ} {hS : S.rank = a}
  {hT : T.rank = d} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}

/- English proof (translation)
Assemble the required witnesses or components as `⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩`.
-/
theorem reads_zero : Reads ψ θ hS hT cc δ r 0 0 :=
  ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩

/- English proof (translation)
Establish `key : ∀ s : Finset (Fin k), Reads ψ θ hS hT cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i)`. Introduce `s`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `using (reads_zero : Reads ψ θ hS hT cc δ r 0 0)`. Introduce `i s hi ih`.

Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi]`. Conclude with `(h i).add ih`. Conclude with `key Finset.univ`.
-/
theorem reads_sum {k : ℕ} (G : Fin k → VC D a d → ℂ) (f : Fin k → WO S T → ℂ)
    (h : ∀ i, Reads ψ θ hS hT cc δ r (G i) (f i)) : Reads ψ θ hS hT cc δ r (∑ i, G i) (∑ i, f i) := by
  have key : ∀ s : Finset (Fin k), Reads ψ θ hS hT cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using (reads_zero : Reads ψ θ hS hT cc δ r 0 0)
    · intro i s hi ih
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (h i).add ih
  exact key Finset.univ

/- English proof (translation)
Introduce `D ψ θ S T a d hS hT cc δ r hP G hG`. Take `⟨e0, he0, hne, f₀, hf₀⟩` from `exists_vac_reads ψ θ S T hS hT cc δ r hP`. Take `⟨k, c, z, rfl⟩` from `GlobalTheory.ThetaSpan.theta_span D cc δ hP.crv a d e0 he0 hne G hG`. Use `⟨∑ i, c i • (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) • heisO ψ S T (finPt hS hT r (z i)) f₀), reads_sum _ _ fun i => ?_⟩` and prove the remaining obligations. Establish `h` using `((GlobalTheory.T.heisenbergFinitePoint_reads_classicalTranslation ψ θ S T hS hT cc δ r hP e0 f₀ hf₀ (z i)).smul (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)))).smul (c i)`.

Use `h using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `Y`. Simplify using `only [Formalism.MainNotions.StandardLatticesGL3.Wd, Pi.smul_apply, smul_eq_mul]`.
-/
theorem exists_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G ∈ TT D (tor0 D cc δ) a d, ∃ f, Reads ψ θ hS hT cc δ r G f := by
  intro D ψ θ S T a d hS hT cc δ r hP G hG
  obtain ⟨e0, he0, hne, f₀, hf₀⟩ := exists_vac_reads ψ θ S T hS hT cc δ r hP
  obtain ⟨k, c, z, rfl⟩ := GlobalTheory.ThetaSpan.theta_span D cc δ hP.crv a d e0 he0 hne G hG
  refine ⟨∑ i, c i • (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) •
    heisO ψ S T (finPt hS hT r (z i)) f₀), reads_sum _ _ fun i => ?_⟩
  have h := ((GlobalTheory.T.heisenbergFinitePoint_reads_classicalTranslation ψ θ S T hS hT cc δ r hP e0 f₀ hf₀ (z i)).smul
    (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)))).smul (c i)
  convert h using 2
  funext Y
  simp only [Formalism.MainNotions.StandardLatticesGL3.Wd, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.NormExact.ReadEx
