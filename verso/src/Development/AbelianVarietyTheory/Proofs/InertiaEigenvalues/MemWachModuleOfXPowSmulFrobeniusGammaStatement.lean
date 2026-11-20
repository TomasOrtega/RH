import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachModuleOfXPowSmulFrobeniusGamma
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfFrob
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonOfWachBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapConstantCoeffEqOne
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NL.ExtLattice.mem_N` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMemWachModuleOfXPowSmulFrobeniusGamma.lean&line=259#L259)
-/
theorem _root_.GlobalTheory.T.mem_wachModule_of_X_pow_smul_frobenius_gamma : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M a : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → W.γ T m - m ∈ aN W T letπ → W.X ^ a • m ∈ W.N T → m ∈ W.N T := by
  first | exact @GlobalTheory.NL.ExtLattice.mem_N | exact GlobalTheory.NL.ExtLattice.mem_N | (intros; apply GlobalTheory.NL.ExtLattice.mem_N <;> assumption)
