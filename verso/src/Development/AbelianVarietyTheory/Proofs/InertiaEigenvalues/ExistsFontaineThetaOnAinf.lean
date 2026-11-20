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
Establish `hc : Continuous (AI.actC g)` using `(AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous`. Proceed by induction on `y using UniformSpace.Completion.induction_on with`. Consider the case `hp => exact isClosed_eq hc (by apply GlobalTheory.RingIface.sigC_cont)`. Consider the case `ih a => exact (AI.actC_ext g a).trans (GlobalTheory.RingBasics.σC_coe g a).symm`.
-/
theorem actC_eq_σC (g : GQ l) (y : PadicComplex l) : AI.actC g y = Formalism.Per.σC g y := by
  have hc : Continuous (AI.actC g) :=
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq hc (by apply GlobalTheory.RingIface.sigC_cont)
  | ih a => exact (AI.actC_ext g a).trans (GlobalTheory.RingBasics.σC_coe g a).symm

/- English proof (translation)
Use `Perfection.ext fun n => ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (PreTilt.coeff n x)`. Take `⟨y', h1, h2⟩` from `AI.actT_coeff g x n y hy.symm`. Establish `h3 : y' = Formalism.Per.σO g y` using `Subtype.ext ((h1.trans (actC_eq_σC AI g y)).trans (by symm; apply GlobalTheory.RingIface.sigO_coe))`. Use `h2.trans ?_` and prove the remaining obligations.

Rewrite using `[h3]`. Conclude with `(GlobalTheory.AdicMaps.coeff_galois l g x n y hy.symm).symm`.
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
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ', pow_mul, ← add_assoc, AI.ζ_succ, ih]`.
-/
theorem ζ_add_pow (j n : ℕ) : AI.ζ (j + n) ^ l ^ n = AI.ζ j := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, ← add_assoc, AI.ζ_succ, ih]

/- English proof (translation)
Rewrite using `[← AI.ε_coeff, LocAinf.εroot, PreTilt.coeff_iterate_frobeniusEquiv_symm, add_comm]`.
-/
theorem coeff_εroot (j n : ℕ) : PreTilt.coeff n (AI.εroot j) =
    Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (AI.ζ (j + n)) := by
  rw [← AI.ε_coeff, LocAinf.εroot, PreTilt.coeff_iterate_frobeniusEquiv_symm, add_comm]

/- English proof (translation)
Use `Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : OC l)}) fun n => ?_` and prove the remaining obligations. Use `⟨AI.ζ (j + n), (coeff_εroot AI j n).symm, ?_⟩` and prove the remaining obligations. Rewrite using `[ζ_add_pow]`.
-/
theorem untilt_εroot (j : ℕ) : (AI.εroot j).untilt = AI.ζ j := by
  refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : OC l)}) fun n => ?_
  refine ⟨AI.ζ (j + n), (coeff_εroot AI j n).symm, ?_⟩
  rw [ζ_add_pow]

/- English proof (translation)
Establish `hprim : IsPrimitiveRoot (((frobeniusEquiv (OCb l) l).symm AI.ε).untilt) l`. Establish `h : ((frobeniusEquiv (OCb l) l).symm AI.ε).untilt = AI.ζ 1` using `untilt_εroot AI 1`. Rewrite using `[h]`. Establish `h1 : AI.ζ 1 ^ l = 1` using `(AI.ζ_succ 0).trans AI.ζ_zero`. Establish `h2` using `IsPrimitiveRoot.orderOf (AI.ζ 1)`.

Rewrite `h2` using `[orderOf_eq_prime h1 AI.ζ_one]`. Then use the resulting hypothesis. Use `⟨fun x y h => ?_, ?_, fun g a => ?_, fun a => ?_, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq, WittVector.fontaineTheta_teichmuller, ← h]`. Conclude with `PreTilt.mk_untilt_eq_coeff_zero x`. Conclude with `ReciprocityTheory.PGsh.Ainf.theta_surj l (OC l) (PadicComplexInt.integers l)`.

Establish `e : AI.actW g a = Formalism.Per.σA g a` using `WittVector.ext fun n => (actT_eq_σF AI g (a.coeff n)).trans (by symm; apply GlobalTheory.RingIface.sigA_coeff)`. Rewrite using `[e, actC_eq_σC]`. Conclude with `(congrArg Subtype.val (GlobalTheory.RingBasics.θ_σA g a)).trans (by apply GlobalTheory.RingIface.sigO_coe)`. Rewrite using `[← RingHom.mem_ker, ReciprocityTheory.PGsh.Ainf.ker_theta l (OC l) (PadicComplexInt.integers l) AI.ε hprim, Ideal.mem_span_singleton]`. Both sides reduce to the same expression.

Rewrite using `[WittVector.fontaineTheta_teichmuller, untilt_εroot]`.
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
Introduce `_ _ _ AI` and use `⟨_, isTheta_fontaineTheta AI⟩`.
-/
theorem exists_isTheta : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    ∃ θ : Ainf l →+* OC l, IsTheta AI θ :=
  fun _ _ _ AI => ⟨_, isTheta_fontaineTheta AI⟩

end GlobalTheory.Cyc
