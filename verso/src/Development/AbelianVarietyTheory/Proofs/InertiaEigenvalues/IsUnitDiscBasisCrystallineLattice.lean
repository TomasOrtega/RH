import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscCoefficientsTopologicallyFreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMemSpanCoeffPeriodPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP

/- English proof (translation)
Establish `h1 : (1 : ℝ≥0) < l` using `by exact_mod_cast hl.out.one_lt`. Establish `he : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ)`. Use `bk.deg_pos` as an intermediate fact. Check the signs of the components of the expression. Use `⟨NNReal.rpow_pos (by exact_mod_cast hl.out.pos), ?_⟩` and prove the remaining obligations.

Conclude with `NNReal.rpow_lt_one_of_one_lt_of_neg h1 (neg_neg_of_pos he)`.
-/
theorem breuilKisinDatum_radius_pos_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have h1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ) := by
    have := bk.deg_pos
    positivity
  refine ⟨NNReal.rpow_pos (by exact_mod_cast hl.out.pos), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg h1 (neg_neg_of_pos he)

/- English proof (translation)
Introduce `l _ K bk τ hτ d ρ _ s Y Z k S' hYS hW`. Take `⟨hρ0, hρ1⟩` from `breuilKisinDatum_radius_pos_lt_one bk`. Establish `hu : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀`. Simplify using `using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0`. Set `j0 : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀` to `Disc.map (u := (X : bk.S)) (ρ := bk.ρ₀) bk.ev hu`.

Establish `hj0 : IsDiscMap bk.ev j0` using `isDiscMap_map bk.ev hu`. Take `⟨ι, ⟨TB⟩⟩` from `GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk`. Take `⟨cD, hcD1, hcD2, -⟩` from `GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1 j0 hj0`. Take `⟨r, hr⟩` from `GlobalTheory.T.exists_pow_mem_span_coeff_period_pow l K bk τ hτ ι TB (2 * s.N * d)`. Use `set δ := Z.det with hδ`.

Establish `hdet : j0 δ * (s.W.det * bk.iA S'.det) = bk.iA (bk.ev ((l : bk.S) ^ (k * d)) * τ ^ (2 * s.N * d))`. Establish `h1` using `congrArg (fun M => bk.iA M.det) hYS`. Simplify using `only [det_mul, det_smul, det_one, mul_one, Fintype.card_fin] at h1`. Establish `h2 : bk.iA Y.det = s.W.det * j0 δ`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, ← hW j0 hj0, det_mul, hδ, RingHom.map_det, RingHom.mapMatrix_apply]`.

Rewrite `h1` using `[map_mul, h2]`. Establish `e : bk.ev ((l : bk.S) ^ (k * d)) * τ ^ (2 * s.N * d) = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) ^ d`. Rewrite using `[map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ← h1]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hdvd : ∀ i, δ ∣ toDisc l (X : bk.S) bk.ρ₀ (TB.c i (τ ^ (2 * s.N * d)))`. Introduce `i`. Establish `h3` using `congrArg (cD i) hdet`. Rewrite `h3` using `[hcD2, hcD1, TB.c_mul, map_mul (toDisc l (X : bk.S) bk.ρ₀)]`.

Establish `hunit : IsUnit (toDisc l (X : bk.S) bk.ρ₀ ((l : bk.S) ^ (k * d)))`. Rewrite using `[map_pow, map_natCast]`. Conclude with `(isUnit_l_disc l _ _).pow _`. Conclude with `(hunit.dvd_mul_left).1 ⟨_, h3.symm⟩`. Establish `hle : Ideal.span (Set.range fun i => TB.c i (τ ^ (2 * s.N * d))) ≤ (Ideal.span {δ}).comap (toDisc l (X : bk.S) bk.ρ₀)`.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Ideal.mem_span_singleton.2 (hdvd i)`. Establish `hl` using `Ideal.mem_span_singleton.1 (hle hr)`. Rewrite `hl` using `[map_pow, map_natCast]`.

Rewrite using `[Matrix.isUnit_iff_isUnit_det]`. Conclude with `isUnit_of_dvd_unit hl ((isUnit_l_disc l _ _).pow _)`.
-/
theorem height_Z_isUnit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ)
    (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (k : ℕ)
    (S' : Matrix (Fin d) (Fin d) (Ainf l)),
    Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) →
    (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z.map j = Y.map bk.iA) → IsUnit Z := by
  intro l _ K bk τ hτ d ρ _ s Y Z k S' hYS hW
  obtain ⟨hρ0, hρ1⟩ := breuilKisinDatum_radius_pos_lt_one bk
  have hu : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  let j0 : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map (u := (X : bk.S)) (ρ := bk.ρ₀) bk.ev hu
  have hj0 : IsDiscMap bk.ev j0 := isDiscMap_map bk.ev hu
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨cD, hcD1, hcD2, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1 j0 hj0
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_mem_span_coeff_period_pow l K bk τ hτ ι TB (2 * s.N * d)

  set δ := Z.det with hδ
  have hdet : j0 δ * (s.W.det * bk.iA S'.det) =
      bk.iA (bk.ev ((l : bk.S) ^ (k * d)) * τ ^ (2 * s.N * d)) := by
    have h1 := congrArg (fun M => bk.iA M.det) hYS
    simp only [det_mul, det_smul, det_one, mul_one, Fintype.card_fin] at h1
    have h2 : bk.iA Y.det = s.W.det * j0 δ := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hW j0 hj0, det_mul, hδ, RingHom.map_det,
        RingHom.mapMatrix_apply]
    rw [map_mul, h2] at h1
    have e : bk.ev ((l : bk.S) ^ (k * d)) * τ ^ (2 * s.N * d) = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) ^ d := by
      rw [map_pow, map_natCast]; ring
    rw [e, ← h1]
    ring
  have hdvd : ∀ i, δ ∣ toDisc l (X : bk.S) bk.ρ₀ (TB.c i (τ ^ (2 * s.N * d))) := by
    intro i
    have h3 := congrArg (cD i) hdet
    rw [hcD2, hcD1, TB.c_mul, map_mul (toDisc l (X : bk.S) bk.ρ₀)] at h3
    have hunit : IsUnit (toDisc l (X : bk.S) bk.ρ₀ ((l : bk.S) ^ (k * d))) := by
      rw [map_pow, map_natCast]; exact (isUnit_l_disc l _ _).pow _
    exact (hunit.dvd_mul_left).1 ⟨_, h3.symm⟩
  have hle : Ideal.span (Set.range fun i => TB.c i (τ ^ (2 * s.N * d))) ≤
      (Ideal.span {δ}).comap (toDisc l (X : bk.S) bk.ρ₀) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_span_singleton.2 (hdvd i)
  have hl := Ideal.mem_span_singleton.1 (hle hr)
  rw [map_pow, map_natCast] at hl
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_of_dvd_unit hl ((isUnit_l_disc l _ _).pow _)

end GlobalTheory.BSP
