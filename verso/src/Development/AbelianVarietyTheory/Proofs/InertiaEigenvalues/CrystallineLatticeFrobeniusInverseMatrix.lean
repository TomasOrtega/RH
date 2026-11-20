import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinAinfDiscIsDomainNormBoundsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsFrobeniusEqMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZeroStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix

/- English proof (translation)
Establish `hdet : W.det ≠ 0`. Introduce `h`. Establish `h1` using `congrArg Matrix.det hW`. Rewrite `h1` using `[Matrix.det_mul, h, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one]`. Conclude with `pow_ne_zero _ ht h1.symm`.

Establish `h2 : W.map Φ * W'.map Φ = (e * t) • (1 : Matrix (Fin d) (Fin d) R)`. Rewrite using `[← Matrix.map_mul, hW, ← hΦ]`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hij]`. Establish `h3 : W * (B * W'.map Φ - (lam * e) • W') = 0`. Rewrite using `[Matrix.mul_sub, ← Matrix.mul_assoc, ← hB, Matrix.smul_mul, h2, Matrix.mul_smul, hW, smul_smul, smul_smul, mul_assoc, sub_self]`. Establish `h4 : W.det • (B * W'.map Φ - (lam * e) • W') = 0`.

Rewrite using `[← Matrix.one_mul (B * W'.map Φ - (lam * e) • W'), ← Matrix.smul_mul, ← Matrix.adjugate_mul, Matrix.mul_assoc, h3, Matrix.mul_zero]`. Rewrite using `[← sub_eq_zero]`. Use extensionality with `i j`. Establish `h5` using `congrFun (congrFun h4 i) j`. Rewrite `h5` using `[Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]`.

Conclude with `(mul_eq_zero.1 h5).resolve_left hdet`.
-/
theorem frob_inverse {R : Type} [CommRing R] [IsDomain R] {d : ℕ} (Φ : R →+* R)
    (W W' B : Matrix (Fin d) (Fin d) R) (t e lam : R) (ht : t ≠ 0)
    (hW : W * W' = t • (1 : Matrix (Fin d) (Fin d) R)) (hB : lam • W.map Φ = W * B) (hΦ : Φ t = e * t) :
    B * W'.map Φ = (lam * e) • W' := by
  have hdet : W.det ≠ 0 := by
    intro h
    have h1 := congrArg Matrix.det hW
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ ht h1.symm
  have h2 : W.map Φ * W'.map Φ = (e * t) • (1 : Matrix (Fin d) (Fin d) R) := by
    rw [← Matrix.map_mul, hW, ← hΦ]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have h3 : W * (B * W'.map Φ - (lam * e) • W') = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← hB, Matrix.smul_mul, h2, Matrix.mul_smul, hW, smul_smul, smul_smul,
      mul_assoc, sub_self]
  have h4 : W.det • (B * W'.map Φ - (lam * e) • W') = 0 := by
    rw [← Matrix.one_mul (B * W'.map Φ - (lam * e) • W'), ← Matrix.smul_mul, ← Matrix.adjugate_mul,
      Matrix.mul_assoc, h3, Matrix.mul_zero]
  rw [← sub_eq_zero]
  ext i j
  have h5 := congrFun (congrFun h4 i) j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h5
  exact (mul_eq_zero.1 h5).resolve_left hdet

/- English proof (translation)
Establish `h1 : (1 : ℝ≥0) < (l : ℝ≥0)` using `by exact_mod_cast hl.out.one_lt`. Establish `h2 : (0 : ℝ) < (bk.Ep.natDegree : ℝ)` using `by exact_mod_cast bk.deg_pos`. Use `⟨NNReal.rpow_pos (lt_trans zero_lt_one h1), ?_⟩` and prove the remaining obligations. Conclude with `NNReal.rpow_lt_one_of_one_lt_of_neg h1 (neg_lt_zero.2 (one_div_pos.2 h2))`.
-/
theorem radius_mem (l : ℕ) [hl : Fact l.Prime] (K : FinExt l) (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have h1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
  have h2 : (0 : ℝ) < (bk.Ep.natDegree : ℝ) := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (lt_trans zero_lt_one h1), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg h1 (neg_lt_zero.2 (one_div_pos.2 h2))

end GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix

/- English proof (translation)
Introduce `l _ K bk τ hτ d ρ hρ s Φ hΦ`. Take `⟨h0, h1⟩` from `GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix.radius_mem l K bk`. Use `haveI := (GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1).1`. Establish `hτ0` using `(GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ).2.1`. Use `GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix.frob_inverse Φ s.W s.W' _ (bk.iA τ ^ (2 * s.N)) _ _ (pow_ne_zero _ hτ0) s.W_mul (GlobalTheory.T.discPeriods_map_frobenius_eq_mul l K bk τ hτ d ρ hρ s Φ hΦ) ?_` and prove the remaining obligations.

Establish `h2 : Φ (bk.iA τ) = bk.iS bk.E * bk.iA τ`. Establish `h3` using `hΦ.ext τ`. Rewrite `h3` using `[hτ.1, map_mul]`. Conclude with `h3`. Rewrite using `[map_pow, h2, mul_pow]`.
-/
theorem GlobalTheory.BSP.seed_frob_inverse : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap WittVector.frobenius Φ → (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS * s.W'.map Φ = (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) * bk.iS bk.E ^ (2 * s.N)) • s.W' := by
  intro l _ K bk τ hτ d ρ hρ s Φ hΦ
  obtain ⟨h0, h1⟩ := GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix.radius_mem l K bk
  haveI := (GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1).1
  have hτ0 := (GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ).2.1
  refine GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix.frob_inverse Φ s.W s.W' _ (bk.iA τ ^ (2 * s.N)) _ _ (pow_ne_zero _ hτ0) s.W_mul
    (GlobalTheory.T.discPeriods_map_frobenius_eq_mul l K bk τ hτ d ρ hρ s Φ hΦ) ?_
  have h2 : Φ (bk.iA τ) = bk.iS bk.E * bk.iA τ := by
    have h3 := hΦ.ext τ
    rw [hτ.1, map_mul] at h3
    exact h3
  rw [map_pow, h2, mul_pow]
