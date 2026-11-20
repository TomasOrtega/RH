import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqZeroOfForallLeExp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionExistence.LeOneIffOfMulEqOne

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitCompl

/- English proof (translation)
Introduce `L _ _ _ s`. Establish `hf : ∀ x : L, Valued.v (s.i.toRingHom x) = s.w.valuation L x` using `fun x => PI.CompAtExist.muV_eq s x`. Take `⟨φ, hφc, hφ, -⟩` from `GlobalTheory.DenseCompl.exists_extension s.w s.v (f := s.i.toRingHom) hf`. Set `g : maximalRealSubfield L →+* s.w.adicCompletion L` to `(algebraMap L (s.w.adicCompletion L)).comp (algebraMap (maximalRealSubfield L) L)`. Establish `hg : ∀ a, Valued.v (g a) = s.v.valuation (maximalRealSubfield L) a`.

Introduce `a`. Simplify using `only [g, RingHom.comp_apply]`. Rewrite using `[GlobalTheory.Idele.valued_algebraMap, ← PI.CompAtExist.muV_eq s, PI.CompAtExist.muV_apply, AlgHom.commutes, GlobalTheory.Idele.valued_algebraMap]`. Take `⟨ψ, hψc, hψ, -⟩` from `GlobalTheory.DenseCompl.exists_extension s.v s.w g hg`. Establish `hcomp : ∀ y, φ (ψ y) = y`.

Introduce `y`. Use `(HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L) s.v).induction_on (p := fun y => φ (ψ y) = y) y (isClosed_eq (hφc.comp hψc) continuous_id) fun a => ?_` and prove the remaining obligations. Rewrite using `[hψ]`. Simplify using `only [g, RingHom.comp_apply]`. Rewrite using `[hφ]`.

Conclude with `s.i.commutes a`. Establish `hsurj : Function.Surjective φ` using `fun y => ⟨ψ y, hcomp y⟩`. Set `e` to `RingEquiv.ofBijective φ ⟨φ.injective, hsurj⟩`. Establish `he : ∀ y, e.symm y = ψ y` using `fun y => e.injective (by rw [e.apply_symm_apply]; exact (hcomp y).symm)`. Use `⟨e.symm, ?_, ?_, fun x => ?_⟩` and prove the remaining obligations.

Conclude with `hψc.congr fun y => (he y).symm`. Conclude with `hφc`. Establish `h` using `e.symm_apply_apply (algebraMap L (s.w.adicCompletion L) x)`. Conclude with `(congrArg e.symm (hφ x)).symm.trans h`.
-/
theorem exists_ringEquiv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L),
    ∃ i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous i ∧ Continuous i.symm ∧
      ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x := by
  intro L _ _ _ s

  have hf : ∀ x : L, Valued.v (s.i.toRingHom x) = s.w.valuation L x :=
    fun x => PI.CompAtExist.muV_eq s x
  obtain ⟨φ, hφc, hφ, -⟩ := GlobalTheory.DenseCompl.exists_extension s.w s.v (f := s.i.toRingHom) hf

  let g : maximalRealSubfield L →+* s.w.adicCompletion L :=
    (algebraMap L (s.w.adicCompletion L)).comp (algebraMap (maximalRealSubfield L) L)
  have hg : ∀ a, Valued.v (g a) = s.v.valuation (maximalRealSubfield L) a := by
    intro a
    simp only [g, RingHom.comp_apply]
    rw [GlobalTheory.Idele.valued_algebraMap, ← PI.CompAtExist.muV_eq s, PI.CompAtExist.muV_apply, AlgHom.commutes,
      GlobalTheory.Idele.valued_algebraMap]
  obtain ⟨ψ, hψc, hψ, -⟩ := GlobalTheory.DenseCompl.exists_extension s.v s.w g hg
  have hcomp : ∀ y, φ (ψ y) = y := by
    intro y
    refine (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L) s.v).induction_on
      (p := fun y => φ (ψ y) = y) y (isClosed_eq (hφc.comp hψc) continuous_id) fun a => ?_
    rw [hψ]
    simp only [g, RingHom.comp_apply]
    rw [hφ]
    exact s.i.commutes a
  have hsurj : Function.Surjective φ := fun y => ⟨ψ y, hcomp y⟩
  let e := RingEquiv.ofBijective φ ⟨φ.injective, hsurj⟩
  have he : ∀ y, e.symm y = ψ y := fun y => e.injective (by rw [e.apply_symm_apply]; exact (hcomp y).symm)
  refine ⟨e.symm, ?_, ?_, fun x => ?_⟩
  · exact hψc.congr fun y => (he y).symm
  · exact hφc
  · have h := e.symm_apply_apply (algebraMap L (s.w.adicCompletion L) x)
    exact (congrArg e.symm (hφ x)).symm.trans h

end GlobalTheory.SplitCompl
