import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SiegelWeilFock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorFiniteUnderCompactCommutingCartanStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalSStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

/- English proof (translation)
Use extensionality with `i j`. Take `⟨k | k, rfl⟩` from `finSumFinEquiv.surjective j`. Simplify using `only [GlobalTheory.SiegelFormula.lagr, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr, Matrix.of_apply, pairVec_inl, Equiv.symm_apply_apply, Sum.elim_inl]`. Simplify using `only [GlobalTheory.SiegelFormula.lagr, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr, Matrix.of_apply, pairVec_inr, Equiv.symm_apply_apply, Sum.elim_inr, Pi.neg_apply]`.
-/
theorem lagr_eq_lagr {D : D7} (A B : HSp D) (y : WO A B) :
    GlobalTheory.SiegelFormula.lagr A B y = GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr A B y := by
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective j
  · simp only [GlobalTheory.SiegelFormula.lagr, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr, Matrix.of_apply, pairVec_inl, Equiv.symm_apply_apply,
      Sum.elim_inl]
  · simp only [GlobalTheory.SiegelFormula.lagr, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr, Matrix.of_apply, pairVec_inr, Equiv.symm_apply_apply,
      Sum.elim_inr, Pi.neg_apply]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [GlobalTheory.SiegelFormula.swSection, GlobalTheory.SiegelFormula.valZero, swSec, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero, lagr_eq_lagr]`.
-/
theorem swSection_eq_swSec {D : D7} (A B : HSp D) (ν : Measure (WO A B)) (𝓕 : Set (WO A B))
    (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (f : WO (dblSp A) B → ℂ) :
    GlobalTheory.SiegelFormula.swSection A B ν 𝓕 ω f = swSec A B ω ν 𝓕 f := by
  funext g
  simp only [GlobalTheory.SiegelFormula.swSection, GlobalTheory.SiegelFormula.valZero, swSec, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero, lagr_eq_lagr]

/- English proof (translation)
Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations. Establish `: (χ⁻¹ : (AE D)ˣ →* Circle) = fun x => (χ x)⁻¹` using `rfl`. Rewrite using `[this]`. Conclude with `h.1.inv`. Rewrite using `[MonoidHom.inv_apply, h.2 x, inv_one]`.
-/
theorem isHeckeCharacter_inv_of_isHeckeCharacter {D : D7} {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ := by
  refine ⟨?_, fun x => ?_⟩
  · have : (χ⁻¹ : (AE D)ˣ →* Circle) = fun x => (χ x)⁻¹ := rfl
    rw [this]; exact h.1.inv
  · rw [MonoidHom.inv_apply, h.2 x, inv_one]

end GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

/- English proof (translation)
Introduce `hW hWeil hIch D ψ A B ha hab hwitt χB omh homh a hmaj θ sS sB hθ hS hB hKc ν 𝓕 hcov mH hmH φ hF`. Establish `hφ` using `hF.1`. Establish `hK` using `GlobalTheory.T.fock_vector_finite_under_compact_commuting_cartan D ψ θ (dblSp A) B 1 χB omh sS sB homh hθ hS hB (Khat A a) (isCompact_Khat A a) hKc φ hF`. Establish `hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a)` using `GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hmaj`. Establish `hwitt' : Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank`.

Rewrite using `[GlobalTheory.RallisIP.wittIdx_eq_wittIndex]`. Conclude with `hwitt`. Distinguish the cases in `hb : B.rank ≤ 2 * A.rank`. Establish `h3 : A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank`. Break down `hwitt' with h | h` into its components or cases.

Rewrite using `[h]`. Use linear arithmetic over natural numbers and integers. Conclude with `h`. Conclude with `hIch D ψ A B hab hb h3 χB omh homh a hmaj hI θ sS sB hθ hS hB hKc ν 𝓕 hcov mH hmH φ hF`. Use `push_neg at hb`.

Take `⟨-, hW2⟩` from `hWeil D A B mH hmH ha hwitt'`. Take `⟨hint, hser⟩` from `hW2 ψ χB omh homh φ hφ`. Use `⟨hint, ?_⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨-, -, hsum⟩ : _ ∧ _ ∧ _ := by`. Take `⟨h1, h2⟩` from `hser hb ν 𝓕 hcov`.

Conclude with `⟨h1, fun g => (h2 g).1, fun g => (h2 g).2⟩`. Establish `hmem` using `GlobalTheory.T.doublingSiegelWeilSection_mem_degeneratePrincipalSeries hW D ψ A B χB omh homh ν 𝓕 hcov φ hφ a hK`. Establish `hre : (A.rank : ℝ) / 2 < (sZero A B).re`. Establish `: (sZero A B).re = ((B.rank : ℝ) - A.rank) / 2`. Simplify using `[sZero, Complex.div_re]`.

Rewrite using `[this]`. Establish `: (2 * A.rank : ℝ) < B.rank` using `by exact_mod_cast hb`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hv` using `GlobalTheory.Eis.SphConv.eisValueAt_flat hI hmem (GlobalTheory.Eis.sphConv D A a hI) (isHeckeCharacter_inv_of_isHeckeCharacter homh.hecT) hre`. Establish `he : GlobalTheory.Eis.eis A (swSec A B omh ν 𝓕 φ) = ThetaMean.thetaMean omh mH φ`.

Use function extensionality and compare the values at `g`. Rewrite using `[← swSection_eq_swSec]`. Conclude with `hsum g`. Rewrite `hv` using `[he]`. Conclude with `hv`.
-/
theorem siegelWeilAll_of_hypotheses : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary →
    GlobalTheory.Published.SiegelWeilUnitaryConvergent → ∀ D : D7, SiegelWeilFock D := by
  intro hW hWeil hIch D ψ A B ha hab hwitt χB omh homh a hmaj θ sS sB hθ hS hB hKc ν 𝓕 hcov mH hmH φ hF
  have hφ := hF.1
  have hK := GlobalTheory.T.fock_vector_finite_under_compact_commuting_cartan D ψ θ (dblSp A) B 1 χB omh sS sB homh hθ hS hB (Khat A a) (isCompact_Khat A a) hKc φ hF
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hmaj
  have hwitt' : Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank := by
    rw [GlobalTheory.RallisIP.wittIdx_eq_wittIndex]; exact hwitt
  by_cases hb : B.rank ≤ 2 * A.rank
  · have h3 : A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank := by
      rcases hwitt' with h | h
      · rw [h]; omega
      · exact h
    exact hIch D ψ A B hab hb h3 χB omh homh a hmaj hI θ sS sB hθ hS hB hKc ν 𝓕 hcov mH hmH φ hF
  · push_neg at hb
    obtain ⟨-, hW2⟩ := hWeil D A B mH hmH ha hwitt'
    obtain ⟨hint, hser⟩ := hW2 ψ χB omh homh φ hφ
    refine ⟨hint, ?_⟩
    obtain ⟨-, -, hsum⟩ : _ ∧ _ ∧ _ := by
      obtain ⟨h1, h2⟩ := hser hb ν 𝓕 hcov
      exact ⟨h1, fun g => (h2 g).1, fun g => (h2 g).2⟩
    have hmem := GlobalTheory.T.doublingSiegelWeilSection_mem_degeneratePrincipalSeries hW D ψ A B χB omh homh ν 𝓕 hcov φ hφ a hK
    have hre : (A.rank : ℝ) / 2 < (sZero A B).re := by
      have : (sZero A B).re = ((B.rank : ℝ) - A.rank) / 2 := by
        simp [sZero, Complex.div_re]
      rw [this]
      have : (2 * A.rank : ℝ) < B.rank := by exact_mod_cast hb
      linarith
    have hv := GlobalTheory.Eis.SphConv.eisValueAt_flat hI hmem (GlobalTheory.Eis.sphConv D A a hI) (isHeckeCharacter_inv_of_isHeckeCharacter homh.hecT) hre
    have he : GlobalTheory.Eis.eis A (swSec A B omh ν 𝓕 φ) = ThetaMean.thetaMean omh mH φ := by
      funext g
      rw [← swSection_eq_swSec]
      exact hsum g
    rw [he] at hv
    exact hv

end GlobalTheory.Core.Rk.IP
