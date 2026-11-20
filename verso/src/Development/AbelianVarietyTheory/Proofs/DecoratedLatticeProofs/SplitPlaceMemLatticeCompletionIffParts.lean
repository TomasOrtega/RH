import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpImageIntegralMatrixMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SplitParts

/- English proof (translation)
Introduce `D k _ _ _ _ q S L y hy`. Establish `he : finPart D q.e ∈ intAE D` using `GlobalTheory.UpMem.finPart_e_int q`. Establish `hce : finPart D (cA D q.e) ∈ intAE D` using `(GlobalTheory.FinPl.FrameLat.cA_int_iff q.e).2 he`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `⟨GlobalTheory.FinPl.LatIndHalf.mul_mem_latV he h, GlobalTheory.FinPl.LatIndHalf.mul_mem_latV hce h⟩`. Introduce and unpack `⟨h1, h2⟩`. Establish `e : y = (fun r => q.e * y r) + (fun r => cA D q.e * y r)`. Use function extensionality and compare the values at `r`. Rewrite using `[Pi.add_apply, ← add_mul, (GlobalTheory.FinPl.FrameLat.idem_iff q (y r)).1 (hy r)]`.

Rewrite using `[e]`. Conclude with `add_mem h1 h2`.
-/
theorem mem_latV_iff_parts : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (y : Fin S.rank → AE D), (∀ r, y r ∈ GlobalTheory.FinPl.idAt D (· = q.v)) → (y ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ (fun r => q.e * y r) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ∧ (fun r => cA D q.e * y r) ∈ GlobalTheory.FinPl.latV S L (· = q.v)) := by
  intro D k _ _ _ _ q S L y hy
  have he : finPart D q.e ∈ intAE D := GlobalTheory.UpMem.finPart_e_int q
  have hce : finPart D (cA D q.e) ∈ intAE D := (GlobalTheory.FinPl.FrameLat.cA_int_iff q.e).2 he
  constructor
  · intro h
    exact ⟨GlobalTheory.FinPl.LatIndHalf.mul_mem_latV he h, GlobalTheory.FinPl.LatIndHalf.mul_mem_latV hce h⟩
  · rintro ⟨h1, h2⟩
    have e : y = (fun r => q.e * y r) + (fun r => cA D q.e * y r) := by
      funext r
      rw [Pi.add_apply, ← add_mul, (GlobalTheory.FinPl.FrameLat.idem_iff q (y r)).1 (hy r)]
    rw [e]
    exact add_mem h1 h2

end GlobalTheory.FinPl.SplitParts
