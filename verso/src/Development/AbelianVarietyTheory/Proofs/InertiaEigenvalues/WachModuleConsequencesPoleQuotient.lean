import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleInverseQuotientFreeFiniteCrystallineStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeHodgeTateJumpsFiniteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdGammaSubJumpUnitsAnnihilatesQuotientStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaEigenvalueOnWachLatticeQPowerQuotientStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.WachModulePoleQuotient

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `D HW F Cm`. Unfold `gammaSemisimpleQuotientGlobal gammaSemisimpleLocal GammaSemisimpleQuotient`. Introduce `l _ K s LL h T hT y hy`. Establish `hfr` using `GlobalTheory.T.wachModule_inverseQuotient_free_finite_crystalline D HW F l K s LL h T hT y`. Establish `hJ` using `GlobalTheory.T.crystallineLattice_hodgeTateJumps_finite D HW l K s LL h T hT`.

Set `Fs : Finset (↥(OL LL))ˣ` to `(hJ.toFinset ×ˢ Finset.Icc 1 y).image (fun p : ℤ × ℕ => uU ((HW l).W K s LL h) ^ (-(p.1 + (p.2 : ℤ))))`. Establish `hmem : ∀ c, c ∈ Fs ↔ ∃ a ∈ Jumps (PD` using `(D.loc l).PD K) T, ∃ j : ℕ, 1 ≤ j ∧ j ≤ y ∧ c = uU ((HW l).W K s LL h) ^ (-(a + j)) := by`. Introduce `c`. Simplify using `only [Fs, Finset.mem_image, Finset.mem_product, Set.Finite.mem_toFinset, Finset.mem_Icc, Prod.exists]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, j, ⟨ha, h1, h2⟩, rfl⟩`. Conclude with `⟨a, ha, j, h1, h2, rfl⟩`. Introduce and unpack `⟨a, ha, j, h1, h2, rfl⟩`. Conclude with `⟨a, j, ⟨ha, h1, h2⟩, rfl⟩`. Use `⟨hfr.1, hfr.2, Fs, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `c`. Conclude with `hmem c`. Introduce `x hx`. Conclude with `GlobalTheory.T.prod_gamma_sub_jump_units_annihilates_quotient D HW F Cm l K s LL h T hT y hy Fs (fun a ha j h1 h2 => (hmem _).2 ⟨a, ha, j, h1, h2, rfl⟩) x hx`. Introduce `c hc`.

Take `⟨a, ha, j, h1, h2, rfl⟩` from `(hmem c).1 hc`. Take `⟨x, hx, hxN, hγ⟩` from `GlobalTheory.T.gamma_eigenvalue_on_wachLattice_qPower_quotient D HW F Cm l K s LL h T hT y hy a ha j h1 h2`. Conclude with `⟨x, hx, hxN, hγ⟩`.
-/
theorem wachModule_consequences_poleQuotient : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), gammaSemisimpleQuotientGlobal D HW F := by
  intro D HW F Cm
  unfold gammaSemisimpleQuotientGlobal gammaSemisimpleLocal GammaSemisimpleQuotient
  intro l _ K s LL h T hT y hy
  classical
  have hfr := GlobalTheory.T.wachModule_inverseQuotient_free_finite_crystalline D HW F l K s LL h T hT y
  have hJ := GlobalTheory.T.crystallineLattice_hodgeTateJumps_finite D HW l K s LL h T hT
  let Fs : Finset (↥(OL LL))ˣ := (hJ.toFinset ×ˢ Finset.Icc 1 y).image
    (fun p : ℤ × ℕ => uU ((HW l).W K s LL h) ^ (-(p.1 + (p.2 : ℤ))))
  have hmem : ∀ c, c ∈ Fs ↔ ∃ a ∈ Jumps (PD := (D.loc l).PD K) T, ∃ j : ℕ, 1 ≤ j ∧ j ≤ y ∧
      c = uU ((HW l).W K s LL h) ^ (-(a + j)) := by
    intro c
    simp only [Fs, Finset.mem_image, Finset.mem_product, Set.Finite.mem_toFinset, Finset.mem_Icc,
      Prod.exists]
    constructor
    · rintro ⟨a, j, ⟨ha, h1, h2⟩, rfl⟩
      exact ⟨a, ha, j, h1, h2, rfl⟩
    · rintro ⟨a, ha, j, h1, h2, rfl⟩
      exact ⟨a, j, ⟨ha, h1, h2⟩, rfl⟩
  refine ⟨hfr.1, hfr.2, Fs, ?_, ?_, ?_⟩
  · ext c
    exact hmem c
  · intro x hx
    exact GlobalTheory.T.prod_gamma_sub_jump_units_annihilates_quotient D HW F Cm l K s LL h T hT y hy Fs
      (fun a ha j h1 h2 => (hmem _).2 ⟨a, ha, j, h1, h2, rfl⟩) x hx
  · intro c hc
    obtain ⟨a, ha, j, h1, h2, rfl⟩ := (hmem c).1 hc
    obtain ⟨x, hx, hxN, hγ⟩ := GlobalTheory.T.gamma_eigenvalue_on_wachLattice_qPower_quotient D HW F Cm l K s LL h T hT y hy a ha j h1 h2
    exact ⟨x, hx, hxN, hγ⟩

end GlobalTheory.NL.WachModulePoleQuotient
