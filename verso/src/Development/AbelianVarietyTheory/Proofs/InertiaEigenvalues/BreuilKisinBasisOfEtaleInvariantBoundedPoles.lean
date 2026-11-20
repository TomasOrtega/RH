import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesLiftOfPeriodPowSmulIntegralMatr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEvWIsUnitInjectiveDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_smul_ringHom {R S : Type*} [CommRing R] [CommRing S] {m n : Type*} (f : R →+* S) (c : R)
    (M : Matrix m n R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

/- English proof (translation)
Introduce `l _ K bk τ hτ N d ρ T A0 A0' Y Y' hT hA0 hA0' hφ hA hfix hY hYY'`. Establish `htu : IsUnit (inclW l τ)` using `(GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ).1`. Take `⟨-, hinj, -⟩` from `GlobalTheory.BSP.BK.evW_isUnit_injective_dvd l K bk`. Establish `hdet : IsUnit T.det` using `(Matrix.isUnit_iff_isUnit_det T).mp hT`. Establish `hTi : T⁻¹ * T = 1` using `Matrix.nonsing_inv_mul T hdet`.

Establish `hiT : T * T⁻¹ = 1` using `Matrix.mul_nonsing_inv T hdet`. Use `set t := inclW l τ with ht`. Use `set e := bk.evW bk.E with he`. Establish `hYm : Y.map (inclW l) = t ^ N • T` using `hY`. Establish `hYY'm : Y.map (inclW l) * Y'.map (inclW l) = t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l))`.

Rewrite using `[← Matrix.map_mul, hYY', map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), map_pow]`. Establish `hTY' : T * Y'.map (inclW l) = t ^ N • (1 : Matrix (Fin d) (Fin d) (WCb l))`. Rewrite `hYY'm` using `[hYm, Matrix.smul_mul, show 2 * N = N + N by ring, pow_add, ← smul_smul]`. Conclude with `((htu.pow N).smul_left_cancel).1 hYY'm`. Establish `hY'm : Y'.map (inclW l) = t ^ N • T⁻¹`.

Combine the equalities or inequalities in the displayed calculation. Establish `hfr : ∀ M : Matrix (Fin d) (Fin d) (Ainf l), (M.map WittVector.frobenius).map (inclW l) = (M.map (inclW l)).map (frobW l)`. Introduce `M`. Use extensionality with `i j`. Simplify using `[GlobalTheory.Prism.frobW_inclW]`.

Establish `hft : frobW l t = e * t`. Rewrite using `[ht, GlobalTheory.Prism.frobW_inclW, hτ.1, map_mul]`. Both sides reduce to the same expression. Establish `hfmul : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l), (M * M').map (frobW l) = M.map (frobW l) * M'.map (frobW l)` using `fun M M' => Matrix.map_mul (f := (frobW l).toRingHom)`. Establish `hfsmul : ∀ (c : WCb l) (M : Matrix (Fin d) (Fin d) (WCb l)), (c • M).map (frobW l) = frobW l c • M.map (frobW l)` using `fun c M => map_smul_ringHom (frobW l).toRingHom c M`.

Establish `hOE : ∀ s : bk.S, bk.evW s ∈ bk.OE` using `fun s n => ⟨0, s, 0, by simp⟩`. Take `⟨A, hAm⟩` from `GlobalTheory.BSP.KisinFF.main l K bk τ hτ d d (2 * N) (e ^ N • A0) (Y' * Y.map WittVector.frobenius) (fun i j => by`. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Conclude with `bk.OE.mul_mem (bk.OE.pow_mem (hOE _) _) (hA0 i j)) (by`. Rewrite using `[Matrix.map_mul, hfr, hY'm, hYm, hfsmul, map_pow, hft, hφ, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, hTi, Matrix.one_mul, smul_smul, smul_smul]`.

Rewrite using `[← ht]; exact congrArg (· • A0) (by ring))`. Establish `hTf : (T⁻¹).map (frobW l) * T = A0'`. Establish `h1 : (T⁻¹).map (frobW l) * T.map (frobW l) = 1`. Rewrite using `[← hfmul, hTi, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite `h1` using `[hφ, ← Matrix.mul_assoc]`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨A', hA'm⟩` from `GlobalTheory.BSP.KisinFF.main l K bk τ hτ d d (2 * N) (e ^ N • A0') (Y'.map WittVector.frobenius * Y) (fun i j => by`. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Conclude with `bk.OE.mul_mem (bk.OE.pow_mem (hOE _) _) (hA0' i j)) (by`. Rewrite using `[Matrix.map_mul, hfr, hY'm, hYm, hfsmul, map_pow, hft, Matrix.smul_mul, Matrix.mul_smul, hTf, smul_smul, smul_smul]`.

Rewrite using `[← ht]; exact congrArg (· • A0') (by ring))`. Use `⟨{ T := T, unit := hT, A := A, A' := A', A_mul := ?_, φ := ?_, fix := hfix }, rfl⟩` and prove the remaining obligations. Use `Matrix.map_injective hinj (?_ : (A * A').map bk.evW = (bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S)).map bk.evW)` and prove the remaining obligations. Rewrite using `[Matrix.map_mul, hAm, hA'm, map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), Matrix.smul_mul, Matrix.mul_smul, hA, smul_smul, map_pow, ← pow_add]`. Rewrite using `[← he, two_mul]`.

Rewrite using `[hAm, hφ, Matrix.mul_smul]`.
-/
theorem pre_of_etale : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (T A0 A0' : Matrix (Fin d) (Fin d) (WCb l)) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit T → (∀ i j, A0 i j ∈ bk.OE) → (∀ i j, A0' i j ∈ bk.OE) → T.map (frobW l) = T * A0 → A0 * A0' = 1 → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T.map (galW l (g : GQ l)) = T) → Y.map (inclW l) = inclW l τ ^ N • T → Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → ∃ F : Pre bk N d ρ, F.T = T := by
  intro l _ K bk τ hτ N d ρ T A0 A0' Y Y' hT hA0 hA0' hφ hA hfix hY hYY'
  classical
  have htu : IsUnit (inclW l τ) := (GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ).1
  obtain ⟨-, hinj, -⟩ := GlobalTheory.BSP.BK.evW_isUnit_injective_dvd l K bk
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hT
  have hTi : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hdet
  have hiT : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hdet
  set t := inclW l τ with ht
  set e := bk.evW bk.E with he
  have hYm : Y.map (inclW l) = t ^ N • T := hY
  have hYY'm : Y.map (inclW l) * Y'.map (inclW l) = t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [← Matrix.map_mul, hYY', map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), map_pow]
  have hTY' : T * Y'.map (inclW l) = t ^ N • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [hYm, Matrix.smul_mul, show 2 * N = N + N by ring, pow_add, ← smul_smul] at hYY'm
    exact ((htu.pow N).smul_left_cancel).1 hYY'm
  have hY'm : Y'.map (inclW l) = t ^ N • T⁻¹ := by
    calc Y'.map (inclW l) = T⁻¹ * (T * Y'.map (inclW l)) := by rw [← Matrix.mul_assoc, hTi, Matrix.one_mul]
      _ = t ^ N • T⁻¹ := by rw [hTY', Matrix.mul_smul, Matrix.mul_one]
  have hfr : ∀ M : Matrix (Fin d) (Fin d) (Ainf l),
      (M.map WittVector.frobenius).map (inclW l) = (M.map (inclW l)).map (frobW l) := by
    intro M; ext i j; simp [GlobalTheory.Prism.frobW_inclW]
  have hft : frobW l t = e * t := by
    rw [ht, GlobalTheory.Prism.frobW_inclW, hτ.1, map_mul]; rfl
  have hfmul : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l), (M * M').map (frobW l) = M.map (frobW l) * M'.map (frobW l) :=
    fun M M' => Matrix.map_mul (f := (frobW l).toRingHom)
  have hfsmul : ∀ (c : WCb l) (M : Matrix (Fin d) (Fin d) (WCb l)), (c • M).map (frobW l) = frobW l c • M.map (frobW l) :=
    fun c M => map_smul_ringHom (frobW l).toRingHom c M

  have hOE : ∀ s : bk.S, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  obtain ⟨A, hAm⟩ := GlobalTheory.BSP.KisinFF.main l K bk τ hτ d d (2 * N) (e ^ N • A0) (Y' * Y.map WittVector.frobenius)
    (fun i j => by
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact bk.OE.mul_mem (bk.OE.pow_mem (hOE _) _) (hA0 i j)) (by
      rw [Matrix.map_mul, hfr, hY'm, hYm, hfsmul, map_pow, hft, hφ, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, hTi,
        Matrix.one_mul, smul_smul, smul_smul]
      rw [← ht]; exact congrArg (· • A0) (by ring))
  have hTf : (T⁻¹).map (frobW l) * T = A0' := by
    have h1 : (T⁻¹).map (frobW l) * T.map (frobW l) = 1 := by
      rw [← hfmul, hTi, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hφ, ← Matrix.mul_assoc] at h1
    calc (T⁻¹).map (frobW l) * T = (T⁻¹).map (frobW l) * T * (A0 * A0') := by rw [hA, Matrix.mul_one]
      _ = A0' := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  obtain ⟨A', hA'm⟩ := GlobalTheory.BSP.KisinFF.main l K bk τ hτ d d (2 * N) (e ^ N • A0') (Y'.map WittVector.frobenius * Y)
    (fun i j => by
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact bk.OE.mul_mem (bk.OE.pow_mem (hOE _) _) (hA0' i j)) (by
      rw [Matrix.map_mul, hfr, hY'm, hYm, hfsmul, map_pow, hft, Matrix.smul_mul, Matrix.mul_smul, hTf, smul_smul, smul_smul]
      rw [← ht]; exact congrArg (· • A0') (by ring))
  refine ⟨{ T := T, unit := hT, A := A, A' := A', A_mul := ?_, φ := ?_, fix := hfix }, rfl⟩
  · refine Matrix.map_injective hinj (?_ : (A * A').map bk.evW = (bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S)).map bk.evW)
    rw [Matrix.map_mul, hAm, hA'm, map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), Matrix.smul_mul,
      Matrix.mul_smul, hA, smul_smul, map_pow, ← pow_add]
    rw [← he, two_mul]
  · rw [hAm, hφ, Matrix.mul_smul]

end GlobalTheory.BKLim

end
