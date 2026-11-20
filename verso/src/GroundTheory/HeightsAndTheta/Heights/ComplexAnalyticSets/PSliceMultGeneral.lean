import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMultGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMGeneralPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseSliceGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthTransverseSlice
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

/- English proof (translation)
Consider the cases of `x using WithBot.recBotCoe with`. Consider the case `bot => rw [WithBot.add_bot] at hsum`. Conclude with `absurd hsum (WithBot.bot_ne_natCast _)`. Consider the case `coe y`. Consider the cases of `y using ENat.recTopCoe with`.

Consider the case `top`. Establish `h1' : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((e + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)` using `h1`. Rewrite `h1'` using `[WithBot.coe_le_coe, top_add, top_le_iff]`. Conclude with `absurd h1' (ENat.natCast_ne_top _)`. Consider the case `coe y`.

Consider the cases of `h using ENat.recTopCoe with`. Consider the case `top => simp at hh`. Consider the case `coe h`. Establish `a1 : h + y = e + 1` using `by exact_mod_cast hsum`. Establish `a2 : h ≤ 1` using `by exact_mod_cast hh`.

Establish `a3 : y + 1 ≤ e + 1` using `by exact_mod_cast h1`. Establish `: y = e` using `by omega`. Substitute `this` using the available equality. Both sides reduce to the same expression.
-/
theorem dim_eq_of_height_add {h : ℕ∞} {x : WithBot ℕ∞} {e : ℕ} (h1 : x + 1 ≤ ((e + 1 : ℕ) : WithBot ℕ∞))
    (hh : h ≤ 1) (hsum : (h : WithBot ℕ∞) + x = ((e + 1 : ℕ) : WithBot ℕ∞)) : x = ((e : ℕ) : WithBot ℕ∞) := by
  cases x using WithBot.recBotCoe with
  | bot => rw [WithBot.add_bot] at hsum; exact absurd hsum (WithBot.bot_ne_natCast _)
  | coe y =>
    cases y using ENat.recTopCoe with
    | top =>
      have h1' : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((e + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h1
      rw [WithBot.coe_le_coe, top_add, top_le_iff] at h1'
      exact absurd h1' (ENat.natCast_ne_top _)
    | coe y =>
      cases h using ENat.recTopCoe with
      | top => simp at hh
      | coe h =>
        have a1 : h + y = e + 1 := by exact_mod_cast hsum
        have a2 : h ≤ 1 := by exact_mod_cast hh
        have a3 : y + 1 ≤ e + 1 := by exact_mod_cast h1
        have : y = e := by omega
        subst this; rfl

/- English proof (translation)
Establish `_ : W.IsPrime` using `hW.1.1`. Establish `hJW : J ≤ W` using `le_sup_left.trans hW.1.2`. Establish `hsW : s ∈ W` using `(le_sup_right.trans hW.1.2) (Ideal.mem_span_singleton_self _)`. Establish `_ : Algebra.FiniteType ℂ (MvPolynomial (Fin n) ℂ ⧸ J)` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ J) (Ideal.Quotient.mkₐ_surjective ℂ J)`. Use `set W' : Ideal (MvPolynomial (Fin n) ℂ ⧸ J) := W.map (Ideal.Quotient.mk J)`.

Establish `_ : W'.IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])`. Establish `hW'ne : W' ≠ ⊥` using `fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp (by`. Establish `: Ideal.Quotient.mk J s ∈ W'` using `Ideal.mem_map_of_mem _ hsW`. Rewrite using `[h, Ideal.mem_bot] at this))` and apply the resulting hypothesis. Establish `hquot : ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ J) ⧸ W') = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W)` using `ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJW)`.

Establish `hform` using `GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient ℂ W'`. Establish `hdrop` using `GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne`. Rewrite `hform`, `hdrop` using `[hquot, hdim]`. Conclude with `dim_eq_of_height_add hdrop (Ideal.map_height_le_one_of_mem_minimalPrimes hW) hform`.
-/
theorem ringKrullDim_component {n d : ℕ} {J W : Ideal (MvPolynomial (Fin n) ℂ)} [J.IsPrime]
    {s : MvPolynomial (Fin n) ℂ} (hs : s ∉ J) (hW : W ∈ (J ⊔ Ideal.span {s}).minimalPrimes)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((d : ℕ) : WithBot ℕ∞) := by
  have _ : W.IsPrime := hW.1.1
  have hJW : J ≤ W := le_sup_left.trans hW.1.2
  have hsW : s ∈ W := (le_sup_right.trans hW.1.2) (Ideal.mem_span_singleton_self _)
  have _ : Algebra.FiniteType ℂ (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ J) (Ideal.Quotient.mkₐ_surjective ℂ J)
  set W' : Ideal (MvPolynomial (Fin n) ℂ ⧸ J) := W.map (Ideal.Quotient.mk J)
  have _ : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp (by
    have : Ideal.Quotient.mk J s ∈ W' := Ideal.mem_map_of_mem _ hsW
    rwa [h, Ideal.mem_bot] at this))
  have hquot : ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ J) ⧸ W') = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient ℂ W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot, hdim] at hform hdrop
  exact dim_eq_of_height_add hdrop (Ideal.map_height_le_one_of_mem_minimalPrimes hW) hform

/- English proof (translation)
Introduce `n d J W u hJ hdim hu hW`. Establish `hWp : W.IsPrime` using `hW.1.1`. Establish `hdW` using `ringKrullDim_component hu hW hdim`. Take `⟨f₁, hf₁W, hf₁⟩` from `hC n _ W hW`. Take `⟨f₂, hf₂W, hf₂⟩` from `hT n d W hWp hdW`.

Use `⟨f₁ * f₂, fun h => (hWp.mem_or_mem h).elim hf₁W hf₂W, fun q hq hqf => ?_⟩` and prove the remaining obligations. Rewrite `hqf` using `[map_mul, mul_ne_zero_iff]`. Take `⟨hone, hcm⟩` from `hf₁ q hq hqf.1`. Take `⟨hO, hD⟩` from `hf₂ q hq hqf.2`. Use `⟨_, hO, hD, fun L hL' => ?_⟩` and prove the remaining obligations.

Establish `hsl : sliceIdeal J L q ⊔ Ideal.span {linForm u} = sliceIdeal (J ⊔ Ideal.span {linForm u}) L q`. Simplify using `only [sliceIdeal, sup_right_comm]`. Rewrite using `[hsl]`. Conclude with `hL n d _ W q L hW hdW hq hone hcm hL'`.
-/
theorem SliceMultGeneral.proof (hC : CMGeneralPoint.Statement) (hT : TransverseSliceGeneral.Statement)
    (hL : LengthTransverseSlice.Statement) : SliceMultGeneral.Statement := by
  intro n d J W u hJ hdim hu hW
  have hWp : W.IsPrime := hW.1.1
  have hdW := ringKrullDim_component hu hW hdim
  obtain ⟨f₁, hf₁W, hf₁⟩ := hC n _ W hW
  obtain ⟨f₂, hf₂W, hf₂⟩ := hT n d W hWp hdW
  refine ⟨f₁ * f₂, fun h => (hWp.mem_or_mem h).elim hf₁W hf₂W, fun q hq hqf => ?_⟩
  rw [map_mul, mul_ne_zero_iff] at hqf
  obtain ⟨hone, hcm⟩ := hf₁ q hq hqf.1
  obtain ⟨hO, hD⟩ := hf₂ q hq hqf.2
  refine ⟨_, hO, hD, fun L hL' => ?_⟩
  have hsl : sliceIdeal J L q ⊔ Ideal.span {linForm u} = sliceIdeal (J ⊔ Ideal.span {linForm u}) L q := by
    simp only [sliceIdeal, sup_right_comm]
  rw [hsl]
  exact hL n d _ W q L hW hdW hq hone hcm hL'

end GroundTheory.Heights₂.Heights
