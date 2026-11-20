import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentWachLetterBasisFiltration
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedSubfieldLeCyclotomicExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupIndepDdRE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActQdRPeriodTEqCyclotomicBottom
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.JumpVec

/- English proof (translation)
Introduce `D HW l _ K s LL h T hC i ζ τ hPt a hJ`. Take `⟨-, hemb, ι, hComp⟩` from `(GlobalTheory.NL.Points.points D HW l K s LL h).2.1 i ζ τ hPt`. Establish `hC3` using `(GlobalTheory.NL.CompD.component D HW l K s LL h T hC i ζ τ ι hComp hemb).2.2.1`. Establish `hlt : FildR ((D.loc l).PD K) T.ρ τ (a + 1) < FildR ((D.loc l).PD K) T.ρ τ a` using `lt_of_le_of_ne (GlobalTheory.DeRhamCompare.FildR_succ_le _ _ τ a) hJ`. Take `⟨w, hwa, hwa1⟩` from `SetLike.exists_of_lt hlt`.

Take `⟨d, hd, hdw⟩` from `hC3 w hwa.1`. Use `⟨d, hd, ?_, ?_⟩` and prove the remaining obligations. Establish `: ιV ((D.loc l).PD K) (LL` using `↥LL.1) (V := T.V) d = w + (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d - w) := by abel`. Rewrite using `[this]`. Conclude with `Submodule.add_mem_sup hwa hdw`.

Introduce `hmem`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.1 hmem`. Establish `hdis` using `GlobalTheory.Per.FilLetUnram.iSupIndep_DdRE ((D.loc l).PD K) T.ρ τ`. Establish `hD : w - y ∈ DdRE ((D.loc l).PD K) T.ρ τ` using `Submodule.sub_mem _ hwa.1 hy.1`. Establish `hS : w - y ∈ ⨆ (τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (_ : τ' ≠ τ), DdRE ((D.loc l).PD K) T.ρ τ'`.

Establish `: w - y = z - (ιV ((D.loc l).PD K) (LL` using `↥LL.1) (V := T.V) d - w) := by`. Rewrite using `[← hyz]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ hz hdw`.

Establish `h0 : w - y = 0` using `Submodule.disjoint_def.1 hdis _ hD hS`. Establish `: w = y` using `sub_eq_zero.1 h0`. Conclude with `hwa1 (this ▸ hy)`.
-/
theorem exists_letter_of_jump : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → ∀ a : ℤ, IsJumpV ((D.loc l).PD K) T.ρ τ a → ∃ d ∈ Di (HW l) h T i, ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ FilAt ((D.loc l).PD K) T τ a ∧ ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∉ FilAt ((D.loc l).PD K) T τ (a + 1) := by
  intro D HW l _ K s LL h T hC i ζ τ hPt a hJ
  obtain ⟨-, hemb, ι, hComp⟩ := (GlobalTheory.NL.Points.points D HW l K s LL h).2.1 i ζ τ hPt
  have hC3 := (GlobalTheory.NL.CompD.component D HW l K s LL h T hC i ζ τ ι hComp hemb).2.2.1
  have hlt : FildR ((D.loc l).PD K) T.ρ τ (a + 1) < FildR ((D.loc l).PD K) T.ρ τ a :=
    lt_of_le_of_ne (GlobalTheory.DeRhamCompare.FildR_succ_le _ _ τ a) hJ
  obtain ⟨w, hwa, hwa1⟩ := SetLike.exists_of_lt hlt
  obtain ⟨d, hd, hdw⟩ := hC3 w hwa.1
  refine ⟨d, hd, ?_, ?_⟩
  · have : ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d =
        w + (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d - w) := by abel
    rw [this]
    exact Submodule.add_mem_sup hwa hdw
  · intro hmem
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
    have hdis := GlobalTheory.Per.FilLetUnram.iSupIndep_DdRE ((D.loc l).PD K) T.ρ τ
    have hD : w - y ∈ DdRE ((D.loc l).PD K) T.ρ τ := Submodule.sub_mem _ hwa.1 hy.1
    have hS : w - y ∈ ⨆ (τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (_ : τ' ≠ τ), DdRE ((D.loc l).PD K) T.ρ τ' := by
      have : w - y = z - (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d - w) := by
        rw [← hyz]; abel
      rw [this]
      exact Submodule.sub_mem _ hz hdw
    have h0 : w - y = 0 := Submodule.disjoint_def.1 hdis _ hD hS
    have : w = y := sub_eq_zero.1 h0
    exact hwa1 (this ▸ hy)

end GlobalTheory.NL.JumpVec
