import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxCompactUnitaryConjRelIndexEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnimodMass.umax_relIndex_conj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMaxCompactUnitaryConjRelIndexEq.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.maxCompactUnitary_conj_relIndex_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (h : GAf L n), ((Umax L n).map (MulAut.conj h).toMonoidHom).relIndex (Umax L n) ≠ 0 ∧ ((Umax L n).map (MulAut.conj h).toMonoidHom).relIndex (Umax L n) = (Umax L n).relIndex ((Umax L n).map (MulAut.conj h).toMonoidHom) := by
  first | exact @GlobalTheory.UnimodMass.umax_relIndex_conj | exact GlobalTheory.UnimodMass.umax_relIndex_conj | (intros; apply GlobalTheory.UnimodMass.umax_relIndex_conj <;> assumption)
