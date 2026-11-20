import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.HaarUp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.PsiGen

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ} {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]

/- English proof (translation)
Establish `: Continuous (rmulF a : Mt k r → Mt k r)`. Unfold `rmulF`. Conclude with `Continuous.matrix_mul continuous_id continuous_const`. Conclude with `this.measurable`.
-/
theorem equivA_measurable_rmulF (a : Mat k r) : Measurable (rmulF a : Mt k r → Mt k r) := by
  have : Continuous (rmulF a : Mt k r → Mt k r) := by
    unfold rmulF
    exact Continuous.matrix_mul continuous_id continuous_const
  exact this.measurable

/- English proof (translation)
Establish `: Continuous (conjM a : Mt k r → Mt k r)`. Unfold `conjM`. Conclude with `Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const`. Conclude with `this.measurable`.
-/
theorem equivA_measurable_conjM (a : Mat k r) : Measurable (conjM a : Mt k r → Mt k r) := by
  have : Continuous (conjM a : Mt k r → Mt k r) := by
    unfold conjM
    exact Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const
  exact this.measurable

open Formalism.QuantumDeterminants.WeylGroupFacts in
/- English proof (translation)
Establish `hW'` using `isHaarOn_fourier_of_isHaarOn_main hSF hCW hHW hz hT hW`. Establish `hN'` using `haarUp_N hSF hCN hHN hN`. Establish `hσW : SigmaFinite μW` using `hW.1`. Establish `hσN : SigmaFinite μN` using `hN.1`. Establish `hi : h₀⁻¹ ∈ UWset k r z` using `uw_inv hh₀`.

Establish `hu : IsUnit h₀.det` using `isUnit_of_uh hh₀.1`. Establish `hconj` using `conjInv_N hSF hCN hHN hc hz hT hN h₀⁻¹ hi`. Establish `h1 : MeasurePreserving (rmulF h₀ : Mt k r → Mt k r) μW μW` using `⟨equivA_measurable_rmulF h₀, hW'.right h₀ hh₀⟩`. Establish `h2 : MeasurePreserving (fun x : Mt k r => rmulF m₀ (conjM h₀⁻¹ x)) μN μN` using `(⟨equivA_measurable_rmulF m₀, hN'.right m₀ hm₀⟩ : MeasurePreserving (rmulF m₀ : Mt k r → Mt k r) μN μN).comp ⟨equivA_measurable_conjM h₀⁻¹, hconj⟩`. Establish `h3` using `h1.prod h2`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Simplify using `only [Prod.map, rmulF, conjM, Matrix.nonsing_inv_nonsing_inv _ hu]`. Both sides reduce to the same expression.
-/
theorem shift_measurePreserving (hSF : HaarUniqueSF) (hCW : ClosedW) (hHW : HaarWExists) (hCN : ClosedN)
    (hHN : HaarNExists) (hc : ConjInvRaw) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {μW μN : Measure (Mt k r)} (hW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN)
    {h₀ m₀ : Mat k r} (hh₀ : h₀ ∈ UWset k r z) (hm₀ : m₀ ∈ Nset k r) :
    MeasurePreserving (fun p : Mt k r × Mt k r =>
      Prod.mk (α := Mt k r) (β := Mt k r) (Matrix.of p.1 * h₀ : Mat k r) (h₀⁻¹ * Matrix.of p.2 * h₀ * m₀ : Mat k r))
      (μW.prod μN) (μW.prod μN) := by
  have hW' := isHaarOn_fourier_of_isHaarOn_main hSF hCW hHW hz hT hW
  have hN' := haarUp_N hSF hCN hHN hN
  have hσW : SigmaFinite μW := hW.1
  have hσN : SigmaFinite μN := hN.1
  have hi : h₀⁻¹ ∈ UWset k r z := uw_inv hh₀
  have hu : IsUnit h₀.det := isUnit_of_uh hh₀.1
  have hconj := conjInv_N hSF hCN hHN hc hz hT hN h₀⁻¹ hi
  have h1 : MeasurePreserving (rmulF h₀ : Mt k r → Mt k r) μW μW :=
    ⟨equivA_measurable_rmulF h₀, hW'.right h₀ hh₀⟩
  have h2 : MeasurePreserving (fun x : Mt k r => rmulF m₀ (conjM h₀⁻¹ x)) μN μN :=
    (⟨equivA_measurable_rmulF m₀, hN'.right m₀ hm₀⟩ : MeasurePreserving (rmulF m₀ : Mt k r → Mt k r) μN μN).comp
      ⟨equivA_measurable_conjM h₀⁻¹, hconj⟩
  have h3 := h1.prod h2
  convert h3 using 1
  funext p
  simp only [Prod.map, rmulF, conjM, Matrix.nonsing_inv_nonsing_inv _ hu]
  rfl

open Formalism.QuantumDeterminants.WeylGroupFacts in
/- English proof (translation)
Establish `hi : h₀⁻¹ ∈ UWset k r z` using `uw_inv hh₀`. Establish `hhi : h⁻¹ ∈ UWset k r z` using `uw_inv hh`. Establish `hu : IsUnit h₀.det` using `isUnit_of_uh hh₀.1`. Establish `hii : h₀⁻¹⁻¹ = h₀` using `Matrix.nonsing_inv_nonsing_inv _ hu`. Establish `hcN : h₀⁻¹ * m * h₀ ∈ Nset k r`.

Use `(hUN k r z hz h₀⁻¹ hi m hm).1` as an intermediate fact. Rewrite `this` using `[hii]`. Then use the resulting hypothesis. Establish `hψ : Formalism.MainNotions.S.psiGen k r z c (h₀⁻¹ * m * h₀ * m₀) = Formalism.MainNotions.S.psiGen k r z c m * Formalism.MainNotions.S.psiGen k r z c m₀`. Rewrite using `[psiGen_mul hz c hcN hm₀]`. Use `congr 1`.

Use `psiGen_conj hz c hi hm` as an intermediate fact. Rewrite `this` using `[hii]`. Then use the resulting hypothesis. Establish `hmat : h * h₀ * (h₀⁻¹ * m * h₀ * m₀) * g = h * m * (h₀ * m₀ * g)`. Establish `e : h₀ * h₀⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hu`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = h * m * (h₀ * m₀ * g) := by rw [e, Matrix.mul_one]`. Establish `hπ1 : π h₀ (π (h * h₀)⁻¹ ξ) = π h⁻¹ ξ`. Rewrite using `[Matrix.mul_inv_rev, hπ.1.2 _ hi _ hhi, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, ← hπ.1.2 _ hh₀ _ hi, Matrix.mul_nonsing_inv _ hu, hπ.1.1, one_apply_eq_self]`. Establish `hn : Formalism.MainNotions.S.psiGen k r z c m₀ * star (Formalism.MainNotions.S.psiGen k r z c m₀) = 1`.

Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, psiGen_norm]`. Simplify using the standard rewrite rules. Unfold `Lap.chiInv`. Establish `key : ∀ F : ℂ, F * star (Formalism.MainNotions.S.psiGen k r z c m) = Formalism.MainNotions.S.psiGen k r z c m₀ * (F * (star (Formalism.MainNotions.S.psiGen k r z c m₀) * star (Formalism.MainNotions.S.psiGen k r z c m)))` using `fun F => by`. Take the linear combination `(-(F * star (Formalism.MainNotions.S.psiGen k r z c m))) * hn`.

Rewrite using `[hmat, hψ, map_smul, map_smul, hπ1]`. Simplify using `only [smul_smul, star_mul]`. Use `congr 1`. Conclude with `key _`.
-/
theorem integrand_shift (hCW : ClosedW) (hCN : ClosedN) (hUN : UWNormal) {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (c : Fin r → ℂ)
    {π : Lap.Mat k r → (Vp →L[ℂ] Vp)} (hπ : Formalism.MainNotions.S.IsURepOn (UWset k r z) π) (f : Lap.Mat k r → ℂ) (ξ : Vp)
    {h₀ m₀ g h m : Mat k r} (hh₀ : h₀ ∈ UWset k r z) (hm₀ : m₀ ∈ Nset k r) (hh : h ∈ UWset k r z)
    (hm : m ∈ Nset k r) :
    f (h * m * (h₀ * m₀ * g)) • Lap.chiInv (Formalism.MainNotions.S.psiGen k r z c) π h m ξ =
      Formalism.MainNotions.S.psiGen k r z c m₀ • π h₀ (f (h * h₀ * (h₀⁻¹ * m * h₀ * m₀) * g) •
        Lap.chiInv (Formalism.MainNotions.S.psiGen k r z c) π (h * h₀) (h₀⁻¹ * m * h₀ * m₀) ξ) := by
  have hi : h₀⁻¹ ∈ UWset k r z := uw_inv hh₀
  have hhi : h⁻¹ ∈ UWset k r z := uw_inv hh
  have hu : IsUnit h₀.det := isUnit_of_uh hh₀.1
  have hii : h₀⁻¹⁻¹ = h₀ := Matrix.nonsing_inv_nonsing_inv _ hu
  have hcN : h₀⁻¹ * m * h₀ ∈ Nset k r := by
    have := (hUN k r z hz h₀⁻¹ hi m hm).1
    rwa [hii] at this
  have hψ : Formalism.MainNotions.S.psiGen k r z c (h₀⁻¹ * m * h₀ * m₀) =
      Formalism.MainNotions.S.psiGen k r z c m * Formalism.MainNotions.S.psiGen k r z c m₀ := by
    rw [psiGen_mul hz c hcN hm₀]
    congr 1
    have := psiGen_conj hz c hi hm
    rwa [hii] at this
  have hmat : h * h₀ * (h₀⁻¹ * m * h₀ * m₀) * g = h * m * (h₀ * m₀ * g) := by
    have e : h₀ * h₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    calc h * h₀ * (h₀⁻¹ * m * h₀ * m₀) * g = h * (h₀ * h₀⁻¹) * m * (h₀ * m₀ * g) := by
          simp only [Matrix.mul_assoc]
      _ = h * m * (h₀ * m₀ * g) := by rw [e, Matrix.mul_one]
  have hπ1 : π h₀ (π (h * h₀)⁻¹ ξ) = π h⁻¹ ξ := by
    rw [Matrix.mul_inv_rev, hπ.1.2 _ hi _ hhi, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
      ← hπ.1.2 _ hh₀ _ hi, Matrix.mul_nonsing_inv _ hu, hπ.1.1, one_apply_eq_self]
  have hn : Formalism.MainNotions.S.psiGen k r z c m₀ * star (Formalism.MainNotions.S.psiGen k r z c m₀) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, psiGen_norm]
    simp
  unfold Lap.chiInv
  have key : ∀ F : ℂ, F * star (Formalism.MainNotions.S.psiGen k r z c m) = Formalism.MainNotions.S.psiGen k r z c m₀ *
      (F * (star (Formalism.MainNotions.S.psiGen k r z c m₀) * star (Formalism.MainNotions.S.psiGen k r z c m))) := fun F => by
    linear_combination (-(F * star (Formalism.MainNotions.S.psiGen k r z c m))) * hn
  rw [hmat, hψ, map_smul, map_smul, hπ1]
  simp only [smul_smul, star_mul]
  congr 1
  exact key _

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
