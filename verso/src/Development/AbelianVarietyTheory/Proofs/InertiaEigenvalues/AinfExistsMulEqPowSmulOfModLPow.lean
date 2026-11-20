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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisOfEtaleInvariantBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescendRightInverseStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfInvLim

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Conclude with `Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right (h k j) _`.
-/
theorem dvd_mul_entry {R : Type} [CommRing R] {d : ℕ} (c : R) (A B : Matrix (Fin d) (Fin d) R)
    (h : ∀ i j, c ∣ B i j) (i j : Fin d) : c ∣ (A * B) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right (h k j) _

/- English proof (translation)
Introduce `l _ d M τ Y hY hQ`. Establish `hinj : Function.Injective (inclW l)` using `WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))`. Use `set A := Y.map (inclW l) with hA`. Use `set c := inclW l τ ^ M with hc`. Establish `hAinv : A * A⁻¹ = 1` using `Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hY)`.

Establish `hinvA : A⁻¹ * A = 1` using `Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).1 hY)`. Use `set Z := c • A⁻¹ with hZ`. Establish `hZent : ∀ i j, ∃ a : Ainf l, Z i j = inclW l (1 * a)`. Introduce `i j`. Use `GlobalTheory.AinfSat.mem_ideal_of_saturated l 1 (by rw [map_one]; exact isUnit_one) 0 (Z i j) fun n => ?_` and prove the remaining obligations.

Take `⟨Q, hQn⟩` from `hQ n`. Apply the tactic sequence `have h1 := dvd_mul_entry _ A⁻¹ _ hQn i j`. Establish `h2 : A⁻¹ * (A * Q.map (inclW l) - c • (1 : Matrix (Fin d) (Fin d) (WCb l))) = Q.map (inclW l) - Z`. Rewrite using `[Matrix.mul_sub, ← Matrix.mul_assoc, hinvA, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]`. Rewrite `h1` using `[h2]`.

Use `⟨Q i j, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, one_mul, one_mul, dvd_sub_comm]`. Simplify `h1` using `[Matrix.sub_apply]`. Use `choose Y' hY' using hZent`. Use `⟨Matrix.of fun i j => Y' i j, ?_⟩` and prove the remaining obligations.

Establish `hmap : (Matrix.of fun i j => Y' i j).map (inclW l) = Z`. Use extensionality with `i j`. Simplify using `[hY' i j]`. Establish `key : (Y * Matrix.of fun i j => Y' i j).map (inclW l) = (τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))).map (inclW l)`. Rewrite using `[Matrix.map_mul, hmap, hZ, Matrix.mul_smul, ← hA, hAinv]`.

Use extensionality with `i j`. Simplify using `[Matrix.one_apply, hc, Matrix.smul_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Use `Matrix.ext fun i j => hinj ?_` and prove the remaining obligations. Conclude with `congrFun (congrFun (congrArg Matrix.of.symm key) i) j`.
-/
theorem exists_mul_eq_smul_one : ∀ (l : ℕ) [Fact l.Prime] (d M : ℕ) (τ : Ainf l)
    (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) →
    (∀ n, ∃ Q : Matrix (Fin d) (Fin d) (Ainf l), ∀ i j, (l : WCb l) ^ n ∣
      (Y.map (inclW l) * Q.map (inclW l) - inclW l τ ^ M • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) →
    ∃ Y' : Matrix (Fin d) (Fin d) (Ainf l), Y * Y' = τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  intro l _ d M τ Y hY hQ
  have hinj : Function.Injective (inclW l) :=
    WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))
  set A := Y.map (inclW l) with hA
  set c := inclW l τ ^ M with hc
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hY)
  have hinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).1 hY)
  set Z := c • A⁻¹ with hZ
  have hZent : ∀ i j, ∃ a : Ainf l, Z i j = inclW l (1 * a) := by
    intro i j
    refine GlobalTheory.AinfSat.mem_ideal_of_saturated l 1 (by rw [map_one]; exact isUnit_one) 0 (Z i j) fun n => ?_
    obtain ⟨Q, hQn⟩ := hQ n
    have h1 := dvd_mul_entry _ A⁻¹ _ hQn i j
    have h2 : A⁻¹ * (A * Q.map (inclW l) - c • (1 : Matrix (Fin d) (Fin d) (WCb l))) =
        Q.map (inclW l) - Z := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hinvA, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
    rw [h2] at h1
    refine ⟨Q i j, ?_⟩
    rw [pow_zero, one_mul, one_mul, dvd_sub_comm]
    simpa [Matrix.sub_apply] using h1
  choose Y' hY' using hZent
  refine ⟨Matrix.of fun i j => Y' i j, ?_⟩
  have hmap : (Matrix.of fun i j => Y' i j).map (inclW l) = Z := by
    ext i j; simp [hY' i j]
  have key : (Y * Matrix.of fun i j => Y' i j).map (inclW l) =
      (τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))).map (inclW l) := by
    rw [Matrix.map_mul, hmap, hZ, Matrix.mul_smul, ← hA, hAinv]
    ext i j
    simp [Matrix.one_apply, hc, Matrix.smul_apply]
    split_ifs <;> simp
  refine Matrix.ext fun i j => hinj ?_
  exact congrFun (congrFun (congrArg Matrix.of.symm key) i) j

end GlobalTheory.AinfInvLim
