import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce and unpack `rfl`. Conclude with `hε.2 (by simp)`.
-/
theorem ne_one_of_isEps {l : ℕ} [hl : Fact l.Prime] {ε : OCb l} (hε : GlobalTheory.MemLoc.IsEps ε) : ε ≠ 1 := by
  rintro rfl
  exact hε.2 (by simp)

/- English proof (translation)
Take `⟨-, ε, η, hε, hφ⟩` from `hτ`. Introduce `h`. Establish `h1` using `congrArg (WittVector.constantCoeff (p := l) (R := OCb l)) hφ`. Simplify using `only [map_mul, map_sub, map_one, WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP, WittVector.teichmuller_coeff_zero, h] at h1`. Rewrite `h1` using `[zero_pow hl.out.ne_zero]`.

Establish `hη : (η : Ainf l).coeff 0 ≠ 0`. Use `η.isUnit.map (WittVector.constantCoeff (p := l) (R := OCb l))` as an intermediate fact. Rewrite `this` using `[WittVector.constantCoeff_apply]`. Conclude with `this.ne_zero`. Conclude with `mul_ne_zero hη (sub_ne_zero.2 (ne_one_of_isEps hε)) h1.symm`.
-/
theorem coeff_zero_ne_zero_of_isPer {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) {τ : Ainf l}
    (hτ : bk.IsPer τ) : τ.coeff 0 ≠ 0 := by
  obtain ⟨-, ε, η, hε, hφ⟩ := hτ
  intro h
  have h1 := congrArg (WittVector.constantCoeff (p := l) (R := OCb l)) hφ
  simp only [map_mul, map_sub, map_one, WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP,
    WittVector.teichmuller_coeff_zero, h] at h1
  rw [zero_pow hl.out.ne_zero] at h1
  have hη : (η : Ainf l).coeff 0 ≠ 0 := by
    have := η.isUnit.map (WittVector.constantCoeff (p := l) (R := OCb l))
    rw [WittVector.constantCoeff_apply] at this
    exact this.ne_zero
  exact mul_ne_zero hη (sub_ne_zero.2 (ne_one_of_isEps hε)) h1.symm

/- English proof (translation)
Establish `hl1 : (1 : ℝ≥0) < (l : ℝ≥0)` using `by exact_mod_cast hl.out.one_lt`. Establish `he : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ)` using `one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)`. Conclude with `⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (neg_neg_of_pos he)⟩`.
-/
theorem ρ₀_pos_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ) := one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)
  exact ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (neg_neg_of_pos he)⟩

/- English proof (translation)
Introduce `l _ K bk τ hτ`. Establish `h0` using `coeff_zero_ne_zero_of_isPer bk hτ`. Establish `hτ0 : τ ≠ 0`. Introduce and unpack `rfl`. Conclude with `h0 (WittVector.zero_coeff _ _ _)`.

Establish `hU : IsUnit (inclW l τ)`. Use `WittVector.isUnit_of_coeff_zero_ne_zero _ ?_` and prove the remaining obligations. Rewrite using `[inclW, WittVector.map_coeff]`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 h0`. Take `⟨ι, ⟨tb⟩⟩` from `GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk`.

Establish `hinj` using `(GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ (ρ₀_pos_lt_one bk).1 (ρ₀_pos_lt_one bk).2).1`. Use `⟨hU, fun h => hτ0 (hinj (h.trans (map_zero _).symm)), hτ0, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[← galW_inclW]`. Conclude with `hU.map (galW l g)`.
-/
theorem isUnit_inclW_of_isPer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    IsUnit (inclW l τ) ∧ bk.iA τ ≠ 0 ∧ τ ≠ 0 ∧ ∀ g : GQ l, IsUnit (inclW l (Per.σA g τ)) := by
  intro l _ K bk τ hτ
  have h0 := coeff_zero_ne_zero_of_isPer bk hτ
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    exact h0 (WittVector.zero_coeff _ _ _)
  have hU : IsUnit (inclW l τ) := by
    refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
    rw [inclW, WittVector.map_coeff]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 h0
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ (ρ₀_pos_lt_one bk).1 (ρ₀_pos_lt_one bk).2).1
  refine ⟨hU, fun h => hτ0 (hinj (h.trans (map_zero _).symm)), hτ0, fun g => ?_⟩
  rw [← galW_inclW]
  exact hU.map (galW l g)

end GlobalTheory.BSP
