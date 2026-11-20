import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
import ReciprocityTheory.DualLattices.AinfFacts
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

/- English proof (translation)
Establish an intermediate fact. Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem actC_eq_σC (g : GQ l) (y : PadicComplex l) : AI.actC g y = Formalism.Per.σC g y := by
  have hc : Continuous (AI.actC g) :=
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq hc (by apply GlobalTheory.RingIface.sigC_cont)
  | ih a => exact (AI.actC_ext g a).trans (GlobalTheory.RingBasics.σC_coe g a).symm

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem actT_eq_σF (g : GQ l) (x : OCb l) : AI.actT g x = Formalism.Per.σF g x := by
  refine Perfection.ext fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g x n y hy.symm
  have h3 : y' = Formalism.Per.σO g y := Subtype.ext ((h1.trans (actC_eq_σC AI g y)).trans
    (by symm; apply GlobalTheory.RingIface.sigO_coe))
  refine h2.trans ?_
  rw [h3]
  exact (GlobalTheory.AdicMaps.coeff_galois l g x n y hy.symm).symm

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem ζ_add_pow (j n : ℕ) : AI.ζ (j + n) ^ l ^ n = AI.ζ j := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, ← add_assoc, AI.ζ_succ, ih]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem coeff_εroot (j n : ℕ) : PreTilt.coeff n (AI.εroot j) =
    Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (AI.ζ (j + n)) := by
  rw [← AI.ε_coeff, LocAinf.εroot, PreTilt.coeff_iterate_frobeniusEquiv_symm, add_comm]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem untilt_εroot (j : ℕ) : (AI.εroot j).untilt = AI.ζ j := by
  refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : OC l)}) fun n => ?_
  refine ⟨AI.ζ (j + n), (coeff_εroot AI j n).symm, ?_⟩
  rw [ζ_add_pow]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isTheta_fontaineTheta : IsTheta AI (WittVector.fontaineTheta (OC l) l) := by
  have hprim : IsPrimitiveRoot (((frobeniusEquiv (OCb l) l).symm AI.ε).untilt) l := by
    have h : ((frobeniusEquiv (OCb l) l).symm AI.ε).untilt = AI.ζ 1 := untilt_εroot AI 1
    rw [h]
    have h1 : AI.ζ 1 ^ l = 1 := (AI.ζ_succ 0).trans AI.ζ_zero
    have h2 := IsPrimitiveRoot.orderOf (AI.ζ 1)
    rwa [orderOf_eq_prime h1 AI.ζ_one] at h2
  refine ⟨fun x y h => ?_, ?_, fun g a => ?_, fun a => ?_, fun j => ?_⟩
  · rw [← Ideal.Quotient.eq, WittVector.fontaineTheta_teichmuller, ← h]
    exact PreTilt.mk_untilt_eq_coeff_zero x
  · exact ReciprocityTheory.PGsh.Ainf.theta_surj l (OC l) (PadicComplexInt.integers l)
  · have e : AI.actW g a = Formalism.Per.σA g a := WittVector.ext fun n =>
      (actT_eq_σF AI g (a.coeff n)).trans (by symm; apply GlobalTheory.RingIface.sigA_coeff)
    rw [e, actC_eq_σC]
    exact (congrArg Subtype.val (GlobalTheory.RingBasics.θ_σA g a)).trans (by apply GlobalTheory.RingIface.sigO_coe)
  · rw [← RingHom.mem_ker,
      ReciprocityTheory.PGsh.Ainf.ker_theta l (OC l) (PadicComplexInt.integers l) AI.ε hprim,
      Ideal.mem_span_singleton]
    rfl
  · rw [WittVector.fontaineTheta_teichmuller, untilt_εroot]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem exists_isTheta : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    ∃ θ : Ainf l →+* OC l, IsTheta AI θ :=
  fun _ _ _ AI => ⟨_, isTheta_fontaineTheta AI⟩

end GlobalTheory.Cyc
