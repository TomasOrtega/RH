import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRFiltrationKerThetaGeneratorFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiSTmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExtFixing
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

noncomputable section
namespace GlobalTheory.HodgeAt

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (σ : GQ l) (L : FinExt l)

/- English proof (translation)
Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul c d => simp [phiS, map_mul]`.
-/
theorem phiS_map_emb (u : ↥L.1 ⊗[ℚ_[l]] ↥L.1) :
    phiS P σ L (Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) u) =
      emb P σ L (Algebra.TensorProduct.lift (AlgHom.id ℚ_[l] ↥L.1) (AlgHom.id ℚ_[l] ↥L.1)
        (fun _ _ => Commute.all _ _) u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c d => simp [phiS, map_mul]

/- English proof (translation)
Establish `h` using `congrArg (Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L)) (ht c)`. Rewrite `h` using `[map_mul, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]`. Rewrite using `[h, Algebra.smul_def, map_mul]`. Use `congr 1`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]`.

Simplify using the standard rewrite rules.
-/
theorem key_emb (t : ↥L.1 ⊗[ℚ_[l]] ↥L.1)
    (ht : ∀ c : ↥L.1, ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] c) * t = (AlgHom.id ℚ_[l] ↥L.1) c • t) (c : ↥L.1) :
    ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) * Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) t =
      (c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) * Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) t := by
  have h := congrArg (Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L)) (ht c)
  rw [map_mul, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] at h
  rw [h, Algebra.smul_def, map_mul]
  congr 1
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  simp

/- English proof (translation)
Proceed by induction on `s using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [mul_add, hx, hy, map_add, TensorProduct.tmul_add, mul_add]`. Consider the case `tmul c b`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_comm (c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) e, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Use `_ = (((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) * e) * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) := by rw [hkey]`. Use `_ = e * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiS P σ L (c ⊗ₜ[ℚ_[l]] b)) := by`. Rewrite using `[mul_comm ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) e, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, phiS_tmul, emb_apply]`.
-/
theorem mul_eq_mul_phiS (e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR)
    (hkey : ∀ c : ↥L.1, ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) * e = (c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) * e)
    (s : ↥L.1 ⊗[ℚ_[l]] P.R.BdR) : e * s = e * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiS P σ L s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [mul_add, hx, hy, map_add, TensorProduct.tmul_add, mul_add]
  | tmul c b =>
    calc e * (c ⊗ₜ[ℚ_[l]] b) = ((c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) * e) * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) := by
          rw [mul_comm (c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) e, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul]
      _ = (((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) * e) * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) := by rw [hkey]
      _ = e * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiS P σ L (c ⊗ₜ[ℚ_[l]] b)) := by
          rw [mul_comm ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) e, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
            one_mul, phiS_tmul, emb_apply]

/- English proof (translation)
Establish `hc : ∀ i, phiS P σ L (GlobalTheory.DRFil.ext ℚ_[l] P.R.BdR ((Pi.basisFun ↥L.1 (Fin a)).coord i) x) = 0`. Introduce `i`. Establish `: (Pi.basisFun ↥L.1 (Fin a)).coord i = (LinearMap.proj i : (Fin a → ↥L.1) →ₗ[↥L.1] ↥L.1)`. Use extensionality with `v`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `congrFun hx i`. Establish `hsum` using `GlobalTheory.DRFil.eq_sum_basis (Qp := ℚ_[l]) (F := P.R.BdR) (Pi.basisFun ↥L.1 (Fin a)) x`. Rewrite using `[hsum, map_sum]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← GlobalTheory.DRFil.sm_mul, hmul, hc i, TensorProduct.tmul_zero, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem sm_eq_zero_of_PhiS (a : ℕ) (e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR)
    (hmul : ∀ s : ↥L.1 ⊗[ℚ_[l]] P.R.BdR, e * s = e * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiS P σ L s))
    (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) (hx : PhiS P σ L a x = 0) :
    GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) e x = 0 := by
  have hc : ∀ i, phiS P σ L (GlobalTheory.DRFil.ext ℚ_[l] P.R.BdR ((Pi.basisFun ↥L.1 (Fin a)).coord i) x) = 0 := by
    intro i
    have : (Pi.basisFun ↥L.1 (Fin a)).coord i = (LinearMap.proj i : (Fin a → ↥L.1) →ₗ[↥L.1] ↥L.1) := by
      ext v; simp
    rw [this]
    exact congrFun hx i
  have hsum := GlobalTheory.DRFil.eq_sum_basis (Qp := ℚ_[l]) (F := P.R.BdR) (Pi.basisFun ↥L.1 (Fin a)) x
  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← GlobalTheory.DRFil.sm_mul, hmul, hc i, TensorProduct.tmul_zero, mul_zero]
  simp

end GlobalTheory.HodgeAt

/- English proof (translation)
Introduce `l _ P σ L _ a`. Take `⟨t, ht1, ht2⟩` from `GlobalTheory.DRFil.exists_idem (Qp := ℚ_[l]) (AlgHom.id ℚ_[l] ↥L.1)`. Use `⟨Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) t, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[phiS_map_emb, ht1, map_one]`. Conclude with `sm_eq_zero_of_PhiS P σ L a _ (mul_eq_mul_phiS P σ L _ (key_emb P σ L t ht2))`.
-/
theorem GlobalTheory.HodgeAt.exists_idem_phiS_ker : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (σ : GQ l) (L : FinExt l) [FiniteDimensional ℚ_[l] ↥L.1] (a : ℕ), ∃ e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR, phiS P σ L e = 1 ∧ ∀ x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR, PhiS P σ L a x = 0 → GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) e x = 0 := by
  intro l _ P σ L _ a
  obtain ⟨t, ht1, ht2⟩ := GlobalTheory.DRFil.exists_idem (Qp := ℚ_[l]) (AlgHom.id ℚ_[l] ↥L.1)
  refine ⟨Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) t, ?_, ?_⟩
  · rw [phiS_map_emb, ht1, map_one]
  · exact sm_eq_zero_of_PhiS P σ L a _ (mul_eq_mul_phiS P σ L _ (key_emb P σ L t ht2))
