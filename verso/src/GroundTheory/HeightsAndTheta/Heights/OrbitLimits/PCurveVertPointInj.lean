import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertPointLengthSteps
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

namespace CurveVerticalPointInjective

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Introduce `h0`. Apply `hp` to reduce the goal to its premises. Simplify using `[mCoordIdeal, mConeMap, RingHom.mem_ker, h0]`.
-/
theorem coord_ne_zero (y : (Σ k, ι k) → Ω) (p : Σ k, ι k)
    (hp : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply hp
  simp [mCoordIdeal, mConeMap, RingHom.mem_ker, h0]

/- English proof (translation)
Establish `hP : NumbersDVR.IsMultiHomogIdeal (mCoordIdeal y)` using `(Bridge.isMultiHomogIdeal_iff _).2 hA.2.1.2.1`. Establish `hJ` using `NumbersDVR.SupSpanMultiHomog.full.{0} ℤ K ι (mCoordIdeal y) s d hP ((Bridge.isMultiHomog_iff s _).2 hs)`. Conclude with `(Bridge.isMultiHomogIdeal_iff _).1 (NumbersDVR.MinimalPrimeMultiHomog.full.{0} ℤ K ι _ W hJ hW.1)`.
-/
theorem isMultiHomogIdeal_of_mem_divSupp (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ)
    (hA : IsArithVar (mCoordIdeal y) 1) (hs : IsMultiHomog s d) {W : Ideal (MRing ι)}
    (hW : W ∈ divSupp (mCoordIdeal y) s) : IsMultiHomogIdeal W := by
  classical
  have hP : NumbersDVR.IsMultiHomogIdeal (mCoordIdeal y) :=
    (Bridge.isMultiHomogIdeal_iff _).2 hA.2.1.2.1
  have hJ := NumbersDVR.SupSpanMultiHomog.full.{0} ℤ K ι (mCoordIdeal y) s d hP
    ((Bridge.isMultiHomog_iff s _).2 hs)
  exact (Bridge.isMultiHomogIdeal_iff _).1
    (NumbersDVR.MinimalPrimeMultiHomog.full.{0} ℤ K ι _ W hJ hW.1)

end CurveVerticalPointInjective

open CurveVerticalPointInjective in

/- English proof (translation)
Introduce `K _ ι _ Ω _ y s d hA hs hsP W hW W' hW' hWW'`. Use `choose c hc using hW.2`. Use `choose c' hc' using hW'.2`. Take `⟨hmax, hrat, hform⟩` from `hCh K ι Ω y s d hA hs hsP W hW c hc`. Take `⟨-, -, hform'⟩` from `hCh K ι Ω y s d hA hs hsP W' hW' c' hc'`.

Establish `hyc : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => coord_ne_zero y _ fun h => hc k (le_sup_left.trans hW.1.1.2 h)`. Use `choose a' b' hb' hab' using fun k => hrat ⟨k, c' k⟩`. Establish `hab'' : ∀ k, (b' k : Ω) * y ⟨k, c' k⟩ = a' k * y ⟨k, c k⟩` using `fun k => by`. Rewrite using `[← hab' k]`. Clear denominators, using `[hyc k]` for the nonvanishing conditions.

Establish `hle : W' ≤ W`. Take `⟨S, hS, hSeq⟩` from `isMultiHomogIdeal_of_mem_divSupp y s d hA hs hW'`. Rewrite using `[hSeq, Ideal.span_le]`. Introduce `g hg`. Take `⟨e, he⟩` from `hS g hg`.

Take `⟨a, b, ha, hb, habg⟩` from `(hform' e g he).1 (hSeq ▸ Ideal.subset_span hg)`. Rewrite `ha`, `hb` using `[← hWW']`. Use `(hform e g he).2 ⟨a * ∏ k, a' k ^ e k, (∏ k, b' k ^ e k) * b, Ideal.mul_mem_right _ _ ha, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Break down `hmax.isPrime.mem_or_mem h with h | h` into its components or cases.

Take `⟨k, -, hk⟩` from `(hmax.isPrime.prod_mem_iff (s := Finset.univ)).1 h`. Conclude with `hb' k (hmax.isPrime.mem_of_pow_mem _ hk)`. Conclude with `hb h`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_assoc, habg, Finset.prod_congr rfl fun k _ => mul_pow (b' k : Ω) _ (e k), Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = (a * ∏ k, (a' k : Ω) ^ e k) * ∏ k, y ⟨k, c k⟩ ^ e k := by`. Repeatedly rewrite using `[hab'', mul_pow, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `le_antisymm (hW.1.2 ⟨hW'.1.1.1, hW'.1.1.2⟩ hle) hle`.
-/
theorem CurveVertPointInj.proof (hCh : CurveVertPointChart.Statement) : CurveVertPointInj.Statement := by
  intro K _ ι _ Ω _ y s d hA hs hsP W hW W' hW' hWW'
  choose c hc using hW.2
  choose c' hc' using hW'.2
  obtain ⟨hmax, hrat, hform⟩ := hCh K ι Ω y s d hA hs hsP W hW c hc
  obtain ⟨-, -, hform'⟩ := hCh K ι Ω y s d hA hs hsP W' hW' c' hc'
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k =>
    coord_ne_zero y _ fun h => hc k (le_sup_left.trans hW.1.1.2 h)
  choose a' b' hb' hab' using fun k => hrat ⟨k, c' k⟩
  have hab'' : ∀ k, (b' k : Ω) * y ⟨k, c' k⟩ = a' k * y ⟨k, c k⟩ := fun k => by
    rw [← hab' k]; field_simp [hyc k]
  have hle : W' ≤ W := by
    obtain ⟨S, hS, hSeq⟩ := isMultiHomogIdeal_of_mem_divSupp y s d hA hs hW'
    rw [hSeq, Ideal.span_le]
    intro g hg
    obtain ⟨e, he⟩ := hS g hg
    obtain ⟨a, b, ha, hb, habg⟩ := (hform' e g he).1 (hSeq ▸ Ideal.subset_span hg)
    rw [← hWW'] at ha hb
    refine (hform e g he).2 ⟨a * ∏ k, a' k ^ e k, (∏ k, b' k ^ e k) * b, Ideal.mul_mem_right _ _ ha, ?_, ?_⟩
    · intro h
      rcases hmax.isPrime.mem_or_mem h with h | h
      · obtain ⟨k, -, hk⟩ := (hmax.isPrime.prod_mem_iff (s := Finset.univ)).1 h
        exact hb' k (hmax.isPrime.mem_of_pow_mem _ hk)
      · exact hb h
    · push_cast
      calc (∏ k, (b' k : Ω) ^ e k) * b * aeval y g
          = a * ∏ k, ((b' k : Ω) * y ⟨k, c' k⟩) ^ e k := by
            rw [mul_assoc, habg, Finset.prod_congr rfl fun k _ => mul_pow (b' k : Ω) _ (e k),
              Finset.prod_mul_distrib]; ring
        _ = (a * ∏ k, (a' k : Ω) ^ e k) * ∏ k, y ⟨k, c k⟩ ^ e k := by
            simp_rw [hab'', mul_pow, Finset.prod_mul_distrib]; ring
  exact le_antisymm (hW.1.2 ⟨hW'.1.1.1, hW'.1.1.2⟩ hle) hle

end GroundTheory.Heights₂.Heights.Targets
