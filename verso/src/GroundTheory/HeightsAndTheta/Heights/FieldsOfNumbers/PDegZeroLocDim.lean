import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsMChart
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

omit [DecidableEq K] in

/- English proof (translation)
The claim follows from `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ_surjective F I)`.
-/
theorem finiteType_quotient_mRing (I : Ideal (MRing ι F)) : Algebra.FiniteType F (MRing ι F ⧸ I) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ_surjective F I)

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Unfold `chartMonomial`. Introduce `h`. Take `⟨k, -, hk⟩` from `Ideal.IsPrime.prod_mem_iff.mp h`. Conclude with `hu k (Ideal.IsPrime.mem_of_pow_mem ‹_› _ hk)`.
-/
theorem chartMonomial_not_mem (Q : Ideal (MRing ι F)) [Q.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) (b : K → ℕ) : chartMonomial u b ∉ Q := by
  unfold chartMonomial
  intro h
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hu k (Ideal.IsPrime.mem_of_pow_mem ‹_› _ hk)

/- English proof (translation)
Use `finiteType_quotient_mRing (F := F) (chartIdeal Q u)` as an intermediate fact. Use `finiteType_quotient_mRing (F := F) Q` as an intermediate fact. Rewrite using `[GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F (A := MRing ι F ⧸ Q), ← h F K ι Q hQ u hu, map_add, map_natCast]`. Use `norm_cast`.
-/
theorem chart_ringKrullDim_add_card (h : MChartTrdeg.Statement.{u}) (Q : Ideal (MRing ι F)) [Q.IsPrime]
    (hQ : IsMultiHomogIdeal Q) (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) :
    ringKrullDim (MRing ι F ⧸ chartIdeal Q u) + Fintype.card K = ringKrullDim (MRing ι F ⧸ Q) := by
  have := finiteType_quotient_mRing (F := F) (chartIdeal Q u)
  have := finiteType_quotient_mRing (F := F) Q
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F,
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F (A := MRing ι F ⧸ Q), ← h F K ι Q hQ u hu,
    map_add, map_natCast]
  norm_cast

end

/- English proof (translation)
Introduce `F _ K _ _ ι _ P hP W hW hPW`. Use `hP.isPrime` as an intermediate fact. Use `hW.isPrime` as an intermediate fact. Use `choose u hu using hW.relevant`. Establish `huP : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P` using `fun k hk => hu k (hPW hk)`.

Establish `hle : chartIdeal P u ≤ chartIdeal W u`. Introduce `p hp`. Take `⟨b, h, -, hh⟩` from `h₁ F K ι u p`. Simplify using `only [chartIdeal, RingHom.mem_ker] at hp ⊢`. Rewrite `hp` using `[hh P huP, div_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem]`.

Establish `hW' : h ∈ W`. Break down `hp with hp | hp` into its components or cases. Conclude with `hPW hp`. Conclude with `absurd hp (chartMonomial_not_mem P u huP b)`. Rewrite using `[hh W hu, IsFractionRing.to_map_eq_zero_iff.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr hW'), zero_div]`.

Establish `: ((chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u))).IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle)`. Use `finiteType_quotient_mRing (F := F) (chartIdeal P u)` as an intermediate fact. Establish `hform` using `GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F ((chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u)))`. Rewrite `hform` using `[ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)]`. Use `show ringKrullDim (degZeroLoc P {W}) + ringKrullDim (MRing ι F ⧸ W) = ringKrullDim (MRing ι F ⧸ P)`.

Rewrite using `[h₃ F K ι P W hPW u hu, ← chart_ringKrullDim_add_card h₂ W hW.multiHomog u hu, ← chart_ringKrullDim_add_card h₂ P hP.multiHomog u huP, ← hform, add_assoc]`.
-/
theorem DegZeroLocDim.proof (h₁ : MChartHomog.Statement.{u}) (h₂ : MChartTrdeg.Statement.{u})
    (h₃ : MChartLocDim.Statement.{u}) : DegZeroLocDim.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  have := hW.isPrime
  choose u hu using hW.relevant
  have huP : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P := fun k hk => hu k (hPW hk)
  have hle : chartIdeal P u ≤ chartIdeal W u := by
    intro p hp
    obtain ⟨b, h, -, hh⟩ := h₁ F K ι u p
    simp only [chartIdeal, RingHom.mem_ker] at hp ⊢
    rw [hh P huP, div_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff,
      IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.Quotient.eq_zero_iff_mem] at hp
    have hW' : h ∈ W := by
      rcases hp with hp | hp
      · exact hPW hp
      · exact absurd hp (chartMonomial_not_mem P u huP b)
    rw [hh W hu, IsFractionRing.to_map_eq_zero_iff.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr hW'), zero_div]
  have : ((chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle)
  have := finiteType_quotient_mRing (F := F) (chartIdeal P u)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F
    ((chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u)))
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)] at hform
  show ringKrullDim (degZeroLoc P {W}) + ringKrullDim (MRing ι F ⧸ W) = ringKrullDim (MRing ι F ⧸ P)
  rw [h₃ F K ι P W hPW u hu, ← chart_ringKrullDim_add_card h₂ W hW.multiHomog u hu,
    ← chart_ringKrullDim_add_card h₂ P hP.multiHomog u huP, ← hform, add_assoc]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
