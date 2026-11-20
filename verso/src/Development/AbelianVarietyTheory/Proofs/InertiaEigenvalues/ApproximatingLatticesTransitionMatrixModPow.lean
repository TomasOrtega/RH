import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEStabilityPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatPowDvdPerPowMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisLimitLatticeTowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitBreuilKisinBasisInvariantEtaleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapBreuilKisinMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MittagLefflerImageBreuilKisinModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentCoefficientsAinfModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisOfEtaleInvariantBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescendRightInverseStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.TransLim

/- English proof (translation)
Introduce `l _ K bk τ hτ d N ρ tw F T0 R hT0 hR`. Establish `key : ∀ n, ∃ Y : Matrix (Fin (tw.d' n)) (Fin (tw.d' (n + 1))) bk.S, (F n).T * Y.map bk.evW = zW (tw.f n) * (F (n + 1)).T` using `fun n => GlobalTheory.T.exists_equivariantMap_breuilKisinMatrix l K bk τ hτ N N (tw.d' (n + 1)) (tw.d' n) (fun g => (tw.ρ' (n + 1) g).val) (fun g => (tw.ρ' n g).val) (F (n + 1)) (F n) (tw.f n) (tw.f_equi n)`. Use `choose Y hY using key`. Use `⟨Y, fun n => ?_⟩` and prove the remaining obligations. Set `π : WCb l →+* WCb l ⧸ Ideal.span {(l : WCb l) ^ n}` to `Ideal.Quotient.mk _`.

Establish `hz : ∀ {a b : ℕ} (M M' : Matrix (Fin a) (Fin b) (WCb l)), (∀ i j, (l : WCb l) ^ n ∣ (M - M') i j) ↔ M.map π = M'.map π`. Introduce `a b M M'`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `i j`.

Simplify using `only [Matrix.map_apply]`. Rewrite using `[← sub_eq_zero, ← map_sub]`. Conclude with `(Ideal.Quotient.eq_zero_iff_dvd _ _).2 (by simpa [Matrix.sub_apply] using h i j)`. Introduce `h i j`. Rewrite using `[Matrix.sub_apply]`.

Use `(Ideal.Quotient.eq_zero_iff_dvd _ _).1 ?_` and prove the remaining obligations. Rewrite using `[map_sub, sub_eq_zero]`. Conclude with `congrFun (congrFun h i) j`. Establish `hA : (zW (tw.Pi n)).map π * (F n).T.map π = T0.map π * (R n).map π`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul]`.

Conclude with `(hz _ _).1 (hR n)`. Establish `hD : (zW (tw.Pi (n + 1))).map π * (F (n + 1)).T.map π = T0.map π * (R (n + 1)).map π`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul]`. Use `(hz _ _).1 fun i j => ?_` and prove the remaining obligations. Conclude with `dvd_trans (pow_dvd_pow _ (Nat.le_succ n)) (hR (n + 1) i j)`.

Establish `hB : (F n).T.map π * ((Y n).map bk.evW).map π = (zW (tw.f n)).map π * (F (n + 1)).T.map π`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, hY n]`. Establish `hC : (zW (tw.Pi n)).map π * (zW (tw.f n)).map π = (zW (tw.Pi (n + 1))).map π`. Rewrite using `[← Matrix.map_mul]`. Use `(hz _ _).1 fun i j => ?_` and prove the remaining obligations.

Establish `h1` using `map_dvd (algebraMap ℤ_[l] (WCb l)) (tw.f_Pi n i j)`. Simplify using `only [map_pow, map_natCast] at h1`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Simplify using `[zW, Matrix.map_apply, Matrix.sub_apply, Matrix.mul_apply, map_sum, map_mul]`. Take `⟨u, hu⟩` from `hT0`.

Establish `hinv : ((u⁻¹ : (Matrix (Fin d) (Fin d) (WCb l))ˣ) : Matrix (Fin d) (Fin d) (WCb l)).map π * T0.map π = 1`. Rewrite using `[← Matrix.map_mul, ← hu, Units.inv_mul, Matrix.map_one _ (map_zero π) (map_one π)]`. Establish `hE : T0.map π * ((R n).map π * ((Y n).map bk.evW).map π) = T0.map π * (R (n + 1)).map π`. Rewrite using `[← Matrix.mul_assoc, ← hA, Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hC, hD]`. Establish `hF : (R n).map π * ((Y n).map bk.evW).map π = (R (n + 1)).map π`.

Use `congrArg (fun M => ((u⁻¹ : (Matrix (Fin d) (Fin d) (WCb l))ˣ) : Matrix (Fin d) (Fin d) (WCb l)).map π * M) hE` as an intermediate fact. Simplify `this` using `only [← Matrix.mul_assoc, hinv, Matrix.one_mul]`. Rewrite `hF` using `[← Matrix.map_mul]`. Conclude with `(hz _ _).2 hF`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), IsUnit T0 → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∃ Y : ∀ n, Matrix (Fin (tw.d' n)) (Fin (tw.d' (n + 1))) bk.S, ∀ n i j, (l : WCb l) ^ n ∣ (R n * (Y n).map bk.evW - R (n + 1)) i j := by
  intro l _ K bk τ hτ d N ρ tw F T0 R hT0 hR
  have key : ∀ n, ∃ Y : Matrix (Fin (tw.d' n)) (Fin (tw.d' (n + 1))) bk.S,
      (F n).T * Y.map bk.evW = zW (tw.f n) * (F (n + 1)).T := fun n =>
    GlobalTheory.T.exists_equivariantMap_breuilKisinMatrix l K bk τ hτ N N (tw.d' (n + 1)) (tw.d' n) (fun g => (tw.ρ' (n + 1) g).val)
      (fun g => (tw.ρ' n g).val) (F (n + 1)) (F n) (tw.f n) (tw.f_equi n)
  choose Y hY using key
  refine ⟨Y, fun n => ?_⟩
  let π : WCb l →+* WCb l ⧸ Ideal.span {(l : WCb l) ^ n} := Ideal.Quotient.mk _
  have hz : ∀ {a b : ℕ} (M M' : Matrix (Fin a) (Fin b) (WCb l)),
      (∀ i j, (l : WCb l) ^ n ∣ (M - M') i j) ↔ M.map π = M'.map π := by
    intro a b M M'
    constructor
    · intro h
      ext i j
      simp only [Matrix.map_apply]
      rw [← sub_eq_zero, ← map_sub]
      exact (Ideal.Quotient.eq_zero_iff_dvd _ _).2 (by simpa [Matrix.sub_apply] using h i j)
    · intro h i j
      rw [Matrix.sub_apply]
      refine (Ideal.Quotient.eq_zero_iff_dvd _ _).1 ?_
      rw [map_sub, sub_eq_zero]
      exact congrFun (congrFun h i) j
  have hA : (zW (tw.Pi n)).map π * (F n).T.map π = T0.map π * (R n).map π := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]; exact (hz _ _).1 (hR n)
  have hD : (zW (tw.Pi (n + 1))).map π * (F (n + 1)).T.map π = T0.map π * (R (n + 1)).map π := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    refine (hz _ _).1 fun i j => ?_
    exact dvd_trans (pow_dvd_pow _ (Nat.le_succ n)) (hR (n + 1) i j)
  have hB : (F n).T.map π * ((Y n).map bk.evW).map π = (zW (tw.f n)).map π * (F (n + 1)).T.map π := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hY n]
  have hC : (zW (tw.Pi n)).map π * (zW (tw.f n)).map π = (zW (tw.Pi (n + 1))).map π := by
    rw [← Matrix.map_mul]
    refine (hz _ _).1 fun i j => ?_
    have h1 := map_dvd (algebraMap ℤ_[l] (WCb l)) (tw.f_Pi n i j)
    simp only [map_pow, map_natCast] at h1
    convert h1 using 1
    simp [zW, Matrix.map_apply, Matrix.sub_apply, Matrix.mul_apply, map_sum, map_mul]
  obtain ⟨u, hu⟩ := hT0
  have hinv : ((u⁻¹ : (Matrix (Fin d) (Fin d) (WCb l))ˣ) : Matrix (Fin d) (Fin d) (WCb l)).map π * T0.map π = 1 := by
    rw [← Matrix.map_mul, ← hu, Units.inv_mul, Matrix.map_one _ (map_zero π) (map_one π)]
  have hE : T0.map π * ((R n).map π * ((Y n).map bk.evW).map π) = T0.map π * (R (n + 1)).map π := by
    rw [← Matrix.mul_assoc, ← hA, Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hC, hD]
  have hF : (R n).map π * ((Y n).map bk.evW).map π = (R (n + 1)).map π := by
    have := congrArg (fun M => ((u⁻¹ : (Matrix (Fin d) (Fin d) (WCb l))ˣ) : Matrix (Fin d) (Fin d) (WCb l)).map π * M) hE
    simpa only [← Matrix.mul_assoc, hinv, Matrix.one_mul] using this
  rw [← Matrix.map_mul] at hF
  exact (hz _ _).2 hF

end GlobalTheory.BKLim.TransLim
