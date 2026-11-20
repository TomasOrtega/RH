import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJetCalc

section General

variable {A B : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
  [CompleteSpace B]

/- English proof (translation)
Establish `hd : AnalyticAt ℂ (fderiv ℂ f) z` using `hf.fderiv`. Establish `hp : AnalyticAt ℂ (fun w => (fderiv ℂ f w, L w)) z` using `hd.prod (L.analyticAt z)`. Establish `hev : AnalyticAt ℂ (fun q : (A →L[ℂ] B) × A => q.1 q.2) (fderiv ℂ f z, L z)` using `(ContinuousLinearMap.id ℂ (A →L[ℂ] B)).analyticAt_bilinear _`. Conclude with `AnalyticAt.comp (g := fun q : (A →L[ℂ] B) × A => q.1 q.2) (f := fun w => (fderiv ℂ f w, L w)) hev hp`.
-/
theorem analyticAt_linField {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (L : A →L[ℂ] A) :
    AnalyticAt ℂ (fun w => fderiv ℂ f w (L w)) z := by

  have hd : AnalyticAt ℂ (fderiv ℂ f) z := hf.fderiv
  have hp : AnalyticAt ℂ (fun w => (fderiv ℂ f w, L w)) z := hd.prod (L.analyticAt z)
  have hev : AnalyticAt ℂ (fun q : (A →L[ℂ] B) × A => q.1 q.2) (fderiv ℂ f z, L z) :=
    (ContinuousLinearMap.id ℂ (A →L[ℂ] B)).analyticAt_bilinear _
  exact AnalyticAt.comp (g := fun q : (A →L[ℂ] B) × A => q.1 q.2)
    (f := fun w => (fderiv ℂ f w, L w)) hev hp

/- English proof (translation)
Establish `hD : HasFDerivAt (fderiv ℂ f) (fderiv ℂ (fderiv ℂ f) z) z` using `hf.fderiv.differentiableAt.hasFDerivAt`. Establish `hP` using `hD.clm_apply L.hasFDerivAt`. Rewrite using `[hP.fderiv]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]`. Conclude with `add_comm _ _`.
-/
theorem fderiv_linField {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (L : A →L[ℂ] A) (M : A) :
    fderiv ℂ (fun w => fderiv ℂ f w (L w)) z M
      = fderiv ℂ (fderiv ℂ f) z M (L z) + fderiv ℂ f z (L M) := by

  have hD : HasFDerivAt (fderiv ℂ f) (fderiv ℂ (fderiv ℂ f) z) z :=
    hf.fderiv.differentiableAt.hasFDerivAt
  have hP := hD.clm_apply L.hasFDerivAt
  rw [hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

/- English proof (translation)
Establish `hS : IsSymmSndFDerivAt ℂ f z` using `hf.contDiffAt.isSymmSndFDerivAt_of_omega`. Conclude with `hS M N`.
-/
theorem snd_symm {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (M N : A) :
    fderiv ℂ (fderiv ℂ f) z M N = fderiv ℂ (fderiv ℂ f) z N M := by

  have hS : IsSymmSndFDerivAt ℂ f z := hf.contDiffAt.isSymmSndFDerivAt_of_omega
  exact hS M N

/- English proof (translation)
Rewrite using `[fderiv_linField hf L, fderiv_linField hf K, snd_symm hf (K z) (L z), map_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem comm_linField {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (L K : A →L[ℂ] A) :
    fderiv ℂ (fun w => fderiv ℂ f w (L w)) z (K z) - fderiv ℂ (fun w => fderiv ℂ f w (K w)) z (L z)
      = fderiv ℂ f z (L (K z) - K (L z)) := by

  rw [fderiv_linField hf L, fderiv_linField hf K, snd_symm hf (K z) (L z), map_sub]
  abel

end General

/- English proof (translation)
Set `RM : Matrix (Fin n) (Fin n) ℂ → (Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ)` to `fun Z => LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ Z)`. Set `LM : Matrix (Fin n) (Fin n) ℂ → (Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ)` to `fun Y => LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ Y)`. Establish `hRz : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (g : Matrix (Fin n) (Fin n) ℂ → B), Rz Z g = fun w => fderiv ℂ g w (RM Z w)` using `fun Z g => rfl`. Establish `hev : ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), AnalyticAt ℂ f z` using `hf.eventually_analyticAt`. Use `⟨fun Z => ?_, fun A Z => ?_, fun Y Z => ?_⟩` and prove the remaining obligations.

Rewrite using `[hRz]`. Conclude with `analyticAt_linField hf (RM Z)`. Use `filter_upwards [hev] with z hz`. Establish `hc` using `comm_linField hz (RM Z) (RM A)`. Establish `hb : (RM Z) ((RM A) z) - (RM A) ((RM Z) z) = z * (A * Z - Z * A)` using `by show z * A * Z - z * Z * A = z * (A * Z - Z * A)`.

Rewrite using `[mul_sub, mul_assoc, mul_assoc]`. Rewrite `hc` using `[hb]`. Conclude with `hc`. Use `filter_upwards [hev] with z hz`. Establish `hc` using `comm_linField hz (RM Z) (LM Y)`.

Establish `hb : (RM Z) ((LM Y) z) - (LM Y) ((RM Z) z) = 0` using `by show Y * z * Z - Y * (z * Z) = 0`. Rewrite using `[mul_assoc, sub_self]`. Rewrite `hc` using `[hb, map_zero, sub_eq_zero]`. Conclude with `hc`.
-/
theorem leftInvariant_calculus (n : ℕ) (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (f : Matrix (Fin n) (Fin n) ℂ → B) (hf : AnalyticAt ℂ f 1) :
    (∀ Z, AnalyticAt ℂ (Rz Z f) 1) ∧
    (∀ A Z, (fun z => Rz A (Rz Z f) z - Rz Z (Rz A f) z) =ᶠ[𝓝 1] Rz (A * Z - Z * A) f) ∧
    ∀ Y Z : Matrix (Fin n) (Fin n) ℂ, (fun z => fderiv ℂ (Rz Z f) z (Y * z)) =ᶠ[𝓝 1]
      Rz Z (fun z => fderiv ℂ f z (Y * z)) := by

  let RM : Matrix (Fin n) (Fin n) ℂ → (Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) :=
    fun Z => LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ Z)
  let LM : Matrix (Fin n) (Fin n) ℂ → (Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) :=
    fun Y => LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ Y)
  have hRz : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (g : Matrix (Fin n) (Fin n) ℂ → B),
      Rz Z g = fun w => fderiv ℂ g w (RM Z w) := fun Z g => rfl
  have hev : ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), AnalyticAt ℂ f z :=
    hf.eventually_analyticAt
  refine ⟨fun Z => ?_, fun A Z => ?_, fun Y Z => ?_⟩
  · rw [hRz]
    exact analyticAt_linField hf (RM Z)
  · filter_upwards [hev] with z hz
    have hc := comm_linField hz (RM Z) (RM A)
    have hb : (RM Z) ((RM A) z) - (RM A) ((RM Z) z) = z * (A * Z - Z * A) := by
      show z * A * Z - z * Z * A = z * (A * Z - Z * A)
      rw [mul_sub, mul_assoc, mul_assoc]
    rw [hb] at hc
    exact hc
  · filter_upwards [hev] with z hz
    have hc := comm_linField hz (RM Z) (LM Y)
    have hb : (RM Z) ((LM Y) z) - (LM Y) ((RM Z) z) = 0 := by
      show Y * z * Z - Y * (z * Z) = 0
      rw [mul_assoc, sub_self]
    rw [hb, map_zero, sub_eq_zero] at hc
    exact hc

end GlobalTheory.SphJetCalc
