import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.SplitGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.NatCastTmul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.LocSplitChiOf

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

/- English proof (translation)
Establish `: CharZero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v)` using `charZero_of_injective_algebraMap (algebraMap I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v)).injective`. Establish `h2K : (2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ≠ 0` using `two_ne_zero`. Take `⟨p1, h1, h2, h3, h4⟩` from `exists_adapted_first_projection (K := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) I.cm.sig (PI.UnitaryGroupMassFormula.AdIndexEq.spl_sig_sig I) (PI.UnitaryGroupMassFormula.AdIndexEq.spl_sig_fix I) I.cm.deg2 h2K (PI.FinKW.psiV I v Rf.ew) hsum (eps_orth Rf v …`. Use `⟨p1, ⟨h1, h2, h3, ?_⟩, h4⟩` and prove the remaining obligations. Introduce and unpack `x ⟨z, rfl⟩`.

Take `⟨fp, hm, hf⟩` from `NumberField.RingOfIntegers.isIntegral_coe z`. Establish `hf' : Polynomial.eval₂ (algebraMap ℤ I.E) (algebraMap (𝓞 I.E) I.E z) fp = 0` using `hf`. Use `show (p1.comp (PI.UnitaryGroupMassFormula.AdIndexEq.inclV I v)) (algebraMap (𝓞 I.E) I.E z) ∈ OV I v`. Use `(Valuation.valuationSubring.integers (Valued.v (R := v.adicCompletion I.F))).mem_of_integral ⟨fp.map (Int.castRingHom _), hm.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map]`.

Establish `hc : (algebraMap (Valued.v (R` using `v.adicCompletion I.F)).valuationSubring (v.adicCompletion I.F)).comp (Int.castRingHom (Valued.v (R := v.adicCompletion I.F)).valuationSubring) = (p1.comp (PI.UnitaryGroupMassFormula.AdIndexEq.inclV I v)).comp (algebraMap ℤ I.E) := RingHom.ext_int _ _`. Rewrite using `[hc, ← Polynomial.hom_eval₂, hf', map_zero]`.
-/
theorem locSplitP_dec (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (Rf : RefData I g r k e f)
    (v : HeightOneSpectrum (𝓞 I.F)) (hsum : SumOne I v (PI.FinKW.psiV I v Rf.ew)) :
    ∃ p1 : RV I v →+* KV I v, IsAdaptedFirstProjection I v (PI.FinKW.psiV I v Rf.ew) p1 ∧
      ∀ x : RV I v, x = algebraMap (KV I v) (RV I v) (p1 x) * PI.FinKW.psiV I v Rf.ew +
        algebraMap (KV I v) (RV I v) (p1 (PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v x)) *
          PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) := by
  have : CharZero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :=
    charZero_of_injective_algebraMap (algebraMap I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v)).injective
  have h2K : (2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ≠ 0 := two_ne_zero
  obtain ⟨p1, h1, h2, h3, h4⟩ := exists_adapted_first_projection (K := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) I.cm.sig
    (PI.UnitaryGroupMassFormula.AdIndexEq.spl_sig_sig I) (PI.UnitaryGroupMassFormula.AdIndexEq.spl_sig_fix I) I.cm.deg2 h2K
    (PI.FinKW.psiV I v Rf.ew) hsum (eps_orth Rf v)
  refine ⟨p1, ⟨h1, h2, h3, ?_⟩, h4⟩
  rintro x ⟨z, rfl⟩
  obtain ⟨fp, hm, hf⟩ := NumberField.RingOfIntegers.isIntegral_coe z
  have hf' : Polynomial.eval₂ (algebraMap ℤ I.E) (algebraMap (𝓞 I.E) I.E z) fp = 0 := hf
  show (p1.comp (PI.UnitaryGroupMassFormula.AdIndexEq.inclV I v)) (algebraMap (𝓞 I.E) I.E z) ∈ OV I v
  refine (Valuation.valuationSubring.integers (Valued.v (R := v.adicCompletion I.F))).mem_of_integral
    ⟨fp.map (Int.castRingHom _), hm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hc : (algebraMap (Valued.v (R := v.adicCompletion I.F)).valuationSubring (v.adicCompletion I.F)).comp
      (Int.castRingHom (Valued.v (R := v.adicCompletion I.F)).valuationSubring) =
      (p1.comp (PI.UnitaryGroupMassFormula.AdIndexEq.inclV I v)).comp (algebraMap ℤ I.E) := RingHom.ext_int _ _
  rw [hc, ← Polynomial.hom_eval₂, hf', map_zero]

/- English proof (translation)
Introduce `I g r k e f Rf v hsum`. Take `⟨p1, hp, -⟩` from `locSplitP_dec I g r k e f Rf v hsum`. Conclude with `⟨p1, hp⟩`.
-/
theorem local_splitting_projection : LocSplitP := by
  intro I g r k e f Rf v hsum
  obtain ⟨p1, hp, -⟩ := locSplitP_dec I g r k e f Rf v hsum
  exact ⟨p1, hp⟩

end PI.UnitaryGroupMassFormula.ScXuExists
