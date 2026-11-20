import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementB
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
import Formalism.GL3MeanSquares.HookFormulaTorsion.ExpSeries

noncomputable section

namespace Formalism.L2.Th1.B.Sim

open Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.HermitianLattices.ExpSeriesBivariate (InLam)
open Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition (inLam_zero inLam_add inLam_neg inLam_nsmul integral_of_mul_eq_one)

variable {K ι : Type} [NormedField K] [CharZero K]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem simeq_iff (f g : MvPowerSeries ι K) : Simeq f g ↔ InLam (f - g) := Iff.rfl

/- English proof (translation)
Take `⟨m, rfl | rfl⟩` from `n.eq_nat_or_neg`. Rewrite using `[natCast_zsmul]`. Conclude with `inLam_nsmul hf m`. Rewrite using `[neg_zsmul, natCast_zsmul]`. Conclude with `inLam_neg (inLam_nsmul hf m)`.
-/
theorem inLam_zsmul [IsUltrametricDist K] {f : MvPowerSeries ι K} (hf : InLam f) (n : ℤ) :
    InLam (n • f) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [natCast_zsmul]; exact inLam_nsmul hf m
  · rw [neg_zsmul, natCast_zsmul]; exact inLam_neg (inLam_nsmul hf m)

/- English proof (translation)
Establish `main : ∀ (m : ℕ) (d : ι →₀ ℕ), d.degree = m → ‖MvPowerSeries.coeff d y‖ ≤ 1`. Introduce `m`. Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`. Introduce `d hd`.

Distinguish the cases in `hd0 : d = 0`. Substitute `hd0` using the available equality. Rewrite using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hy0, norm_one]`. Establish `hmem : ((d, 0) : (ι →₀ ℕ) × (ι →₀ ℕ)) ∈ (antidiagonal d).erase ((0 : ι →₀ ℕ), d)`. Use `Finset.mem_erase.mpr ⟨fun h => hd0 (congrArg Prod.fst h), by simp⟩` and prove the remaining obligations.

Establish `h1 : MvPowerSeries.coeff d (y * y) = _` using `MvPowerSeries.coeff_mul d y y`. Rewrite `h1` using `[← Finset.add_sum_erase _ _ (show ((0 : ι →₀ ℕ), d) ∈ antidiagonal d by simp), ← Finset.add_sum_erase _ _ hmem]`. Simplify using `only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hy0, one_mul, mul_one] at h1`. Establish `h3 : 2 * MvPowerSeries.coeff d y = MvPowerSeries.coeff d (y * y) + - ∑ p ∈ ((antidiagonal d).erase ((0 : ι →₀ ℕ), d)).erase (d, 0), MvPowerSeries.coeff p.1 y * MvPowerSeries.coeff p.2 y`. Rewrite using `[h1]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h4 : ‖MvPowerSeries.coeff d y‖ = ‖2 * MvPowerSeries.coeff d y‖`. Rewrite using `[norm_mul, h2, one_mul]`. Rewrite using `[h4, h3]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hy d) ?_)` and prove the remaining obligations.

Rewrite using `[norm_neg]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p hp => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Establish `hpa` using `Finset.mem_erase.mp hp`. Establish `hpb` using `Finset.mem_erase.mp hpa.2`.

Establish `hp1 : p.1 + p.2 = d` using `by simpa using hpb.2`. Establish `hdeg : p.1.degree + p.2.degree = d.degree` using `by rw [← map_add, hp1]`. Establish `hne1 : p.1 ≠ 0`. Introduce `h0`. Apply `hpb.1` to reduce the goal to its premises.

Use `ext1`. Conclude with `h0`. Simplify `hp1` using `[h0]`. Establish `hne2 : p.2 ≠ 0`. Introduce `h0`.

Apply `hpa.1` to reduce the goal to its premises. Use `ext1`. Simplify `hp1` using `[h0]`. Conclude with `h0`. Establish `hpos1 : p.1.degree ≠ 0` using `fun h => hne1 ((Finsupp.degree_eq_zero_iff _).mp h)`.

Establish `hpos2 : p.2.degree ≠ 0` using `fun h => hne2 ((Finsupp.degree_eq_zero_iff _).mp h)`. Conclude with `mul_le_one₀ (ih p.1.degree (by omega) p.1 rfl) (norm_nonneg _) (ih p.2.degree (by omega) p.2 rfl)`. Conclude with `fun d => main _ d rfl`.
-/
theorem integral_of_sq [IsUltrametricDist K] {y : MvPowerSeries ι K} (h2 : ‖(2 : K)‖ = 1)
    (hy0 : MvPowerSeries.constantCoeff y = 1) (hy : Integral (y * y)) : Integral y := by
  classical
  have main : ∀ (m : ℕ) (d : ι →₀ ℕ), d.degree = m → ‖MvPowerSeries.coeff d y‖ ≤ 1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro d hd
      by_cases hd0 : d = 0
      · subst hd0
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hy0, norm_one]
      have hmem : ((d, 0) : (ι →₀ ℕ) × (ι →₀ ℕ)) ∈ (antidiagonal d).erase ((0 : ι →₀ ℕ), d) := by
        refine Finset.mem_erase.mpr ⟨fun h => hd0 (congrArg Prod.fst h), by simp⟩
      have h1 : MvPowerSeries.coeff d (y * y) = _ := MvPowerSeries.coeff_mul d y y
      rw [← Finset.add_sum_erase _ _ (show ((0 : ι →₀ ℕ), d) ∈ antidiagonal d by simp),
        ← Finset.add_sum_erase _ _ hmem] at h1
      simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hy0, one_mul, mul_one] at h1
      have h3 : 2 * MvPowerSeries.coeff d y = MvPowerSeries.coeff d (y * y) +
          - ∑ p ∈ ((antidiagonal d).erase ((0 : ι →₀ ℕ), d)).erase (d, 0),
            MvPowerSeries.coeff p.1 y * MvPowerSeries.coeff p.2 y := by
        rw [h1]; ring
      have h4 : ‖MvPowerSeries.coeff d y‖ = ‖2 * MvPowerSeries.coeff d y‖ := by
        rw [norm_mul, h2, one_mul]
      rw [h4, h3]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hy d) ?_)
      rw [norm_neg]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p hp => ?_
      rw [norm_mul]
      have hpa := Finset.mem_erase.mp hp
      have hpb := Finset.mem_erase.mp hpa.2
      have hp1 : p.1 + p.2 = d := by simpa using hpb.2
      have hdeg : p.1.degree + p.2.degree = d.degree := by rw [← map_add, hp1]
      have hne1 : p.1 ≠ 0 := by
        intro h0
        apply hpb.1
        ext1
        · exact h0
        · simpa [h0] using hp1
      have hne2 : p.2 ≠ 0 := by
        intro h0
        apply hpa.1
        ext1
        · simpa [h0] using hp1
        · exact h0
      have hpos1 : p.1.degree ≠ 0 := fun h => hne1 ((Finsupp.degree_eq_zero_iff _).mp h)
      have hpos2 : p.2.degree ≠ 0 := fun h => hne2 ((Finsupp.degree_eq_zero_iff _).mp h)
      exact mul_le_one₀ (ih p.1.degree (by omega) p.1 rfl) (norm_nonneg _)
        (ih p.2.degree (by omega) p.2 rfl)
  exact fun d => main _ d rfl

/- English proof (translation)
Establish `h0 : MvPowerSeries.constantCoeff f = 0`. Establish `h` using `hf.1`. Rewrite `h` using `[map_mul, map_ofNat]`. Conclude with `(mul_eq_zero.mp h).resolve_left two_ne_zero`. Use `⟨h0, integral_of_sq h2 (constantCoeff_fExp h0) ?_⟩` and prove the remaining obligations.

Establish `h` using `hf.2`. Rewrite `h` using `[two_mul]`. Establish `e : fExp (f + f) = fExp f * fExp f` using `fExp_add h0 h0`. Conclude with `e ▸ h`.
-/
theorem inLam_of_two_mul [IsUltrametricDist K] {f : MvPowerSeries ι K} (h2 : ‖(2 : K)‖ = 1)
    (hf : InLam (2 * f)) : InLam f := by
  have h0 : MvPowerSeries.constantCoeff f = 0 := by
    have h := hf.1
    rw [map_mul, map_ofNat] at h
    exact (mul_eq_zero.mp h).resolve_left two_ne_zero
  refine ⟨h0, integral_of_sq h2 (constantCoeff_fExp h0) ?_⟩
  have h := hf.2
  rw [two_mul] at h
  have e : fExp (f + f) = fExp f * fExp f := fExp_add h0 h0
  exact e ▸ h

/- English proof (translation)
Use `⟨constantCoeff_fLog hg0, ?_⟩` and prove the remaining obligations. Establish `e : fExp (fLog g) = g` using `fExp_fLog hg0`. Establish `h : Integral (fExp (fLog g))` using `by rw [e]; exact hg`. Conclude with `h`.
-/
theorem inLam_fLog {g : MvPowerSeries ι K} (hg0 : MvPowerSeries.constantCoeff g = 1)
    (hg : Integral g) : InLam (fLog g) := by
  refine ⟨constantCoeff_fLog hg0, ?_⟩
  have e : fExp (fLog g) = g := fExp_fLog hg0
  have h : Integral (fExp (fLog g)) := by rw [e]; exact hg
  exact h

end Formalism.L2.Th1.B.Sim

namespace Formalism.L2.Th1.B.Sim

open Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition (inLam_add inLam_neg)

/- English proof (translation)
Introduce `K ι _ _ _ f g f' g' h h'`. Rewrite `h`, `h'` using `[simeq_iff]`. Use `⟨?_, ?_, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[simeq_iff]`. Establish `e : f - f' - (g - g') = (f - g) + -(f' - g')` using `by ring`.

Rewrite using `[e]`. Conclude with `inLam_add h (inLam_neg h')`. Rewrite using `[simeq_iff]`. Establish `e : -f - -g = -(f - g)` using `by ring`. Rewrite using `[e]`.

Conclude with `inLam_neg h`. Rewrite using `[simeq_iff]`. Establish `e : (n : MvPowerSeries ι K) * f - n * g = n • (f - g)`. Rewrite using `[zsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `inLam_zsmul h n`.
-/
theorem simeq_integral_series : SimeqInt := by
  intro K ι _ _ _ f g f' g' h h'
  rw [simeq_iff] at h h'
  refine ⟨?_, ?_, fun n => ?_⟩
  · rw [simeq_iff]
    have e : f - f' - (g - g') = (f - g) + -(f' - g') := by ring
    rw [e]; exact inLam_add h (inLam_neg h')
  · rw [simeq_iff]
    have e : -f - -g = -(f - g) := by ring
    rw [e]; exact inLam_neg h
  · rw [simeq_iff]
    have e : (n : MvPowerSeries ι K) * f - n * g = n • (f - g) := by
      rw [zsmul_eq_mul]; ring
    rw [e]; exact inLam_zsmul h n

/- English proof (translation)
Introduce `K ι _ _ _ f g h2 h`. Rewrite `h`, the goal using `[simeq_iff]`. Rewrite `h` using `[← mul_sub]`. Conclude with `inLam_of_two_mul h2 h`.
-/
theorem simeq_halving : SimeqHalf := by
  intro K ι _ _ _ f g h2 h
  rw [simeq_iff] at h ⊢
  rw [← mul_sub] at h
  exact inLam_of_two_mul h2 h

/- English proof (translation)
Introduce `K ι _ _ _ g hg0 hg`. Establish `h` using `inLam_fLog hg0 hg`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[simeq_iff, sub_zero]`. Conclude with `h`.

Rewrite using `[simeq_iff, sub_zero]`. Conclude with `inLam_neg h`.
-/
theorem simeq_formal_log : SimeqLog := by
  intro K ι _ _ _ g hg0 hg
  have h := inLam_fLog hg0 hg
  refine ⟨?_, ?_⟩
  · rw [simeq_iff, sub_zero]; exact h
  · rw [simeq_iff, sub_zero]; exact inLam_neg h

end Formalism.L2.Th1.B.Sim
