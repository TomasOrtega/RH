import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffLocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Length
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.AI

universe u

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Conclude with `h (by unfold locCycle; rw [dif_neg hc])`.
-/
theorem mem_minimalPrimes_of_locCycle_ne_zero' {S : Type*} [CommRing S] {J W : Ideal S}
    (h : locCycle J W ≠ 0) : W ∈ J.minimalPrimes := by
  by_contra hc
  exact h (by unfold locCycle; rw [dif_neg hc])

/- English proof (translation)
Introduce `A _ _ _ _ hchain f g s u v hf hg hs hu huv hno`. Establish `hv : v ≠ 0`. Introduce and unpack `rfl`. Rewrite `huv` using `[zero_mul]`. Conclude with `hf ((IsUnit.mul_right_eq_zero hu).mp huv)`.

Establish `hspan : Ideal.span {f} = Ideal.span {v * g}`. Rewrite using `[← huv]`. Conclude with `(Ideal.span_singleton_mul_left_unit hu f).symm`. Establish `hcolon : (Ideal.span {f}).colon {g} = Ideal.span {v}`. Use extensionality with `x`.

Rewrite using `[hspan, Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton, Ideal.mem_span_singleton, mul_dvd_mul_iff_right hg]`. Establish `hadd : ∀ W : Ideal A, locCycle (Ideal.span {f}) W = locCycle (Ideal.span {v}) W + locCycle (Ideal.span {g}) W`. Introduce `W`. Rewrite using `[hspan]`. Conclude with `h₁ A v g hv hg W`.

Establish `hmin1 : ∀ x : A, x ≠ 0 → ∀ W : Ideal A, locCycle (Ideal.span {x}) W ≠ 0 → W.IsPrime ∧ W.height = 1 ∧ x ∈ W` using `fun x hx W h => (h₃ A x hx W).mp (mem_minimalPrimes_of_locCycle_ne_zero' h)`. Establish `hpos : ∀ x : A, x ≠ 0 → ∀ p : Ideal A, p.IsPrime → p.height = 1 → x ∈ p → locCycle (Ideal.span {x}) p ≠ 0` using `fun x hx p hp h1 hxp => (h₂ A _ p ((h₃ A x hx p).mpr ⟨hp, h1, hxp⟩)).ne'`. Establish `nb : ∀ p : Ideal A, p.IsPrime → p.height = 1 → v ∈ p → s ∉ p`. Introduce `p hp h1 hvp hsp`. Establish `e` using `hno p (hpos s hs p hp h1 hsp)`.

Rewrite `e` using `[hadd]`. Conclude with `hpos v hv p hp h1 hvp (by omega)`. Establish `hne : ∀ x : A, x ≠ 0 → ∀ p : Ideal A, x ∈ p → p ≠ ⊥` using `fun x hx p hxp h => hx (by rw [h] at hxp; exact (Submodule.mem_bot A).mp hxp)`. Establish `hL : ∀ G : Ideal A, (locCycle (Ideal.span {f}) G - locCycle (Ideal.span {g}) G) * locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) = locCycle (Ideal.span {v}) G * locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A)`. Introduce `G`.

Rewrite using `[hadd]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[finsum_congr hL, hcolon]`. Distinguish the cases in `hQ : ∃ Q : Ideal A, Q.IsPrime ∧ ⊥ < Q ∧ Q < IsLocalRing.maximalIdeal A`. Take `⟨hd, -, hht⟩` from `h₄ A hchain hQ`.

Take `⟨n₁, e₁, e₁'⟩` from `h₅ A hd v s hv nb`. Take `⟨n₂, e₂, e₂'⟩` from `h₅ A hd s v hs (fun p hp h1 hsp hvp => nb p hp h1 hvp hsp)`. Establish `hlen : Module.length A (A ⧸ Ideal.span {v, s}) ≠ ⊤`. Distinguish the cases in `hvs : Ideal.span {v, s} = ⊤`. Establish `: Subsingleton (A ⧸ Ideal.span {v, s})` using `Ideal.Quotient.subsingleton_iff.mpr hvs`.

Rewrite using `[Module.length_eq_zero]`. Conclude with `ENat.zero_ne_top`. Establish `hvm : v ∈ Ideal.span {v, s}` using `Ideal.subset_span (Set.mem_insert _ _)`. Establish `hsm : s ∈ Ideal.span {v, s}` using `Ideal.subset_span (Set.mem_insert_of_mem _ rfl)`. Establish `hI : IsLocalRing.maximalIdeal A ∈ (Ideal.span {v, s}).minimalPrimes`.

Use `⟨⟨inferInstance, IsLocalRing.le_maximalIdeal hvs⟩, fun Q hQ' hQm => ?_⟩` and prove the remaining obligations. Take `⟨hQp, hQI⟩` from `hQ'`. Assume the negation of the conclusion as `hmQ`. Establish `hlt : Q < IsLocalRing.maximalIdeal A` using `lt_of_le_of_ne hQm fun h => hmQ h.ge`. Establish `h0 : ⊥ < Q` using `bot_lt_iff_ne_bot.mpr (hne v hv Q (hQI hvm))`.

Conclude with `nb Q hQp (hht Q hQp h0 hlt) (hQI hvm) (hQI hsm)`. Establish `: IsArtinianRing (A ⧸ Ideal.span {v, s})` using `IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hI`. Establish `: IsArtinian A (A ⧸ Ideal.span {v, s})` using `isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := Ideal.span {v, s}))`. Conclude with `Module.length_ne_top`. Establish `key` using `(lengthFormulaDimTwo A v s hd hv hs hlen).2.2`.

Rewrite `key` using `[e₁', e₂']`. Rewrite using `[e₁, e₂, Nat.cast_inj.mp key]`. Establish `hQ' : ∀ Q : Ideal A, Q.IsPrime → Q ≠ ⊥ → Q = IsLocalRing.maximalIdeal A`. Introduce `Q hQp h0`. Assume the negation of the conclusion as `hQm`.

Conclude with `hQ ⟨Q, hQp, bot_lt_iff_ne_bot.mpr h0, lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQp.ne_top) hQm⟩`. Establish `zl : ∀ G : Ideal A, locCycle (Ideal.span {v}) G * locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) = 0`. Introduce `G`. Assume the negation of the conclusion as `h`. Take `⟨hGp, hG1, hvG⟩` from `hmin1 v hv G (left_ne_zero_of_mul h)`.

Establish `hGm` using `hQ' G hGp (hne v hv G hvG)`. Establish `hsG : s ∈ G`. Establish `h'` using `(mem_minimalPrimes_of_locCycle_ne_zero' (right_ne_zero_of_mul h)).1.2`. Rewrite `h'` using `[← hGm]`. Conclude with `h' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))`.

Conclude with `nb G hGp hG1 hvG hsG`. Establish `zr : ∀ W : Ideal A, locCycle (Ideal.span {s}) W * locCycle (W ⊔ Ideal.span {v}) (IsLocalRing.maximalIdeal A) = 0`. Introduce `W`. Assume the negation of the conclusion as `h`. Take `⟨hWp, hW1, hsW⟩` from `hmin1 s hs W (left_ne_zero_of_mul h)`.

Establish `hWm` using `hQ' W hWp (hne s hs W hsW)`. Establish `hvW : v ∈ W`. Establish `h'` using `(mem_minimalPrimes_of_locCycle_ne_zero' (right_ne_zero_of_mul h)).1.2`. Rewrite `h'` using `[← hWm]`. Conclude with `h' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self v))`.

Conclude with `nb W hWp hW1 hvW hsW`. Rewrite using `[(finsum_congr zl).trans finsum_zero, (finsum_congr zr).trans finsum_zero]`.
-/
theorem LocalCoeffLocal.proof (h₁ : LocCycleSpanMul.Statement.{u}) (h₂ : LocCyclePos.Statement.{u})
    (h₃ : MinimalPrimesSpanSingleton.Statement.{u}) (h₄ : LocalDomainDimTwo.Statement.{u})
    (h₅ : DimTwoSumReading.Statement.{u}) : LocalCoeffLocal.Statement.{u} := by
  intro A _ _ _ _ hchain f g s u v hf hg hs hu huv hno

  have hv : v ≠ 0 := by
    rintro rfl
    rw [zero_mul] at huv
    exact hf ((IsUnit.mul_right_eq_zero hu).mp huv)
  have hspan : Ideal.span {f} = Ideal.span {v * g} := by
    rw [← huv]
    exact (Ideal.span_singleton_mul_left_unit hu f).symm
  have hcolon : (Ideal.span {f}).colon {g} = Ideal.span {v} := by
    ext x
    rw [hspan, Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton,
      Ideal.mem_span_singleton, mul_dvd_mul_iff_right hg]
  have hadd : ∀ W : Ideal A, locCycle (Ideal.span {f}) W =
      locCycle (Ideal.span {v}) W + locCycle (Ideal.span {g}) W := by
    intro W
    rw [hspan]
    exact h₁ A v g hv hg W

  have hmin1 : ∀ x : A, x ≠ 0 → ∀ W : Ideal A, locCycle (Ideal.span {x}) W ≠ 0 →
      W.IsPrime ∧ W.height = 1 ∧ x ∈ W :=
    fun x hx W h => (h₃ A x hx W).mp (mem_minimalPrimes_of_locCycle_ne_zero' h)
  have hpos : ∀ x : A, x ≠ 0 → ∀ p : Ideal A, p.IsPrime → p.height = 1 → x ∈ p →
      locCycle (Ideal.span {x}) p ≠ 0 :=
    fun x hx p hp h1 hxp => (h₂ A _ p ((h₃ A x hx p).mpr ⟨hp, h1, hxp⟩)).ne'

  have nb : ∀ p : Ideal A, p.IsPrime → p.height = 1 → v ∈ p → s ∉ p := by
    intro p hp h1 hvp hsp
    have e := hno p (hpos s hs p hp h1 hsp)
    rw [hadd] at e
    exact hpos v hv p hp h1 hvp (by omega)
  have hne : ∀ x : A, x ≠ 0 → ∀ p : Ideal A, x ∈ p → p ≠ ⊥ :=
    fun x hx p hxp h => hx (by rw [h] at hxp; exact (Submodule.mem_bot A).mp hxp)
  have hL : ∀ G : Ideal A, (locCycle (Ideal.span {f}) G - locCycle (Ideal.span {g}) G) *
      locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) =
      locCycle (Ideal.span {v}) G * locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) := by
    intro G
    rw [hadd]
    ring
  rw [finsum_congr hL, hcolon]
  by_cases hQ : ∃ Q : Ideal A, Q.IsPrime ∧ ⊥ < Q ∧ Q < IsLocalRing.maximalIdeal A
  ·
    obtain ⟨hd, -, hht⟩ := h₄ A hchain hQ
    obtain ⟨n₁, e₁, e₁'⟩ := h₅ A hd v s hv nb
    obtain ⟨n₂, e₂, e₂'⟩ := h₅ A hd s v hs (fun p hp h1 hsp hvp => nb p hp h1 hvp hsp)
    have hlen : Module.length A (A ⧸ Ideal.span {v, s}) ≠ ⊤ := by
      by_cases hvs : Ideal.span {v, s} = ⊤
      · have : Subsingleton (A ⧸ Ideal.span {v, s}) := Ideal.Quotient.subsingleton_iff.mpr hvs
        rw [Module.length_eq_zero]
        exact ENat.zero_ne_top
      · have hvm : v ∈ Ideal.span {v, s} := Ideal.subset_span (Set.mem_insert _ _)
        have hsm : s ∈ Ideal.span {v, s} := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
        have hI : IsLocalRing.maximalIdeal A ∈ (Ideal.span {v, s}).minimalPrimes := by
          refine ⟨⟨inferInstance, IsLocalRing.le_maximalIdeal hvs⟩, fun Q hQ' hQm => ?_⟩
          obtain ⟨hQp, hQI⟩ := hQ'
          by_contra hmQ
          have hlt : Q < IsLocalRing.maximalIdeal A := lt_of_le_of_ne hQm fun h => hmQ h.ge
          have h0 : ⊥ < Q := bot_lt_iff_ne_bot.mpr (hne v hv Q (hQI hvm))
          exact nb Q hQp (hht Q hQp h0 hlt) (hQI hvm) (hQI hsm)
        have : IsArtinianRing (A ⧸ Ideal.span {v, s}) :=
          IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hI
        have : IsArtinian A (A ⧸ Ideal.span {v, s}) :=
          isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := Ideal.span {v, s}))
        exact Module.length_ne_top
    have key := (lengthFormulaDimTwo A v s hd hv hs hlen).2.2
    rw [e₁', e₂'] at key
    rw [e₁, e₂, Nat.cast_inj.mp key]
  ·
    have hQ' : ∀ Q : Ideal A, Q.IsPrime → Q ≠ ⊥ → Q = IsLocalRing.maximalIdeal A := by
      intro Q hQp h0
      by_contra hQm
      exact hQ ⟨Q, hQp, bot_lt_iff_ne_bot.mpr h0,
        lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQp.ne_top) hQm⟩
    have zl : ∀ G : Ideal A, locCycle (Ideal.span {v}) G *
        locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) = 0 := by
      intro G
      by_contra h
      obtain ⟨hGp, hG1, hvG⟩ := hmin1 v hv G (left_ne_zero_of_mul h)
      have hGm := hQ' G hGp (hne v hv G hvG)
      have hsG : s ∈ G := by
        have h' := (mem_minimalPrimes_of_locCycle_ne_zero' (right_ne_zero_of_mul h)).1.2
        rw [← hGm] at h'
        exact h' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
      exact nb G hGp hG1 hvG hsG
    have zr : ∀ W : Ideal A, locCycle (Ideal.span {s}) W *
        locCycle (W ⊔ Ideal.span {v}) (IsLocalRing.maximalIdeal A) = 0 := by
      intro W
      by_contra h
      obtain ⟨hWp, hW1, hsW⟩ := hmin1 s hs W (left_ne_zero_of_mul h)
      have hWm := hQ' W hWp (hne s hs W hsW)
      have hvW : v ∈ W := by
        have h' := (mem_minimalPrimes_of_locCycle_ne_zero' (right_ne_zero_of_mul h)).1.2
        rw [← hWm] at h'
        exact h' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self v))
      exact nb W hWp hW1 hvW hsW
    rw [(finsum_congr zl).trans finsum_zero, (finsum_congr zr).trans finsum_zero]

end GroundTheory.Heights₂.Heights.NumbersDVR
