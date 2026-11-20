import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.UnitLemma Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.EtaCompare

open WithZero

/- English proof (translation)
Use `set v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E`. Establish `hint : ∀ y : K.E, v y ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range`. Introduce `y`. Use `⟨fun h => IsDiscreteValuationRing.exists_lift_of_le_one h, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨a, rfl⟩`.

Conclude with `(IsDiscreteValuationRing.maximalIdeal K.O).valuation_le_one a`. Establish `hφb : φ b ≠ 0` using `by simpa using hb`. Establish `hvb : v b ≠ 0` using `(Valuation.ne_zero_iff v).2 hb`. Rewrite using `[← div_le_one₀ (norm_pos_iff.2 hφb), ← norm_div, ← map_div₀, hball, ← hint, map_div₀, div_le_one₀ (zero_lt_iff.2 hvb)]`.
-/
theorem norm_le_iff_valuation_le (K : UQ) {E : Type} [NormedField E] (φ : K.E ≃+* E)
    (hball : ∀ y : K.E, ‖φ y‖ ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range) (a b : K.E) (hb : b ≠ 0) :
    ‖φ a‖ ≤ ‖φ b‖ ↔ (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E a ≤
      (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E b := by
  set v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E
  have hint : ∀ y : K.E, v y ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range := by
    intro y
    refine ⟨fun h => IsDiscreteValuationRing.exists_lift_of_le_one h, ?_⟩
    rintro ⟨a, rfl⟩
    exact (IsDiscreteValuationRing.maximalIdeal K.O).valuation_le_one a
  have hφb : φ b ≠ 0 := by simpa using hb
  have hvb : v b ≠ 0 := (Valuation.ne_zero_iff v).2 hb
  rw [← div_le_one₀ (norm_pos_iff.2 hφb), ← norm_div, ← map_div₀, hball, ← hint, map_div₀,
    div_le_one₀ (zero_lt_iff.2 hvb)]

/- English proof (translation)
Use `set v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E`. Distinguish the cases in `hb : b = 0`. Substitute `hb` using the available equality. Simplify using `[v]`. Distinguish the cases in `ha : a = 0`.

Substitute `ha` using the available equality. Simplify using `only [map_zero, norm_zero, v]`. Prove the components needed by the constructor for the conclusion. Introduce `h; exact absurd (norm_eq_zero.1 h.symm) (by simpa using hb)`. Introduce `h`.

Conclude with `absurd ((Valuation.zero_iff _).1 h.symm) hb`. Rewrite using `[le_antisymm_iff, le_antisymm_iff, norm_le_iff_valuation_le K φ hball a b hb, norm_le_iff_valuation_le K φ hball b a ha]`.
-/
theorem norm_eq_iff_valuation_eq (K : UQ) {E : Type} [NormedField E] (φ : K.E ≃+* E)
    (hball : ∀ y : K.E, ‖φ y‖ ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range) (a b : K.E) :
    ‖φ a‖ = ‖φ b‖ ↔ (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E a =
      (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E b := by
  set v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E
  by_cases hb : b = 0
  · subst hb; simp [v]
  by_cases ha : a = 0
  · subst ha
    simp only [map_zero, norm_zero, v]
    constructor
    · intro h; exact absurd (norm_eq_zero.1 h.symm) (by simpa using hb)
    · intro h; exact absurd ((Valuation.zero_iff _).1 h.symm) hb
  rw [le_antisymm_iff, le_antisymm_iff, norm_le_iff_valuation_le K φ hball a b hb,
    norm_le_iff_valuation_le K φ hball b a ha]

end GlobalTheory.EtaCompare

namespace GlobalTheory.EtaCompare

open WithZero

/- English proof (translation)
Introduce `K F E _ _ _ _ hU φ hball x`. Use `set v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E with hv`. Establish `hn : ∀ t : F, ‖φ (φ.symm (algebraMap F E t))‖ = ‖t‖` using `fun t => by`. Rewrite using `[RingEquiv.apply_symm_apply, norm_algebraMap']`. Establish `key : (∃ y : F, ‖x‖ = ‖y‖ ^ 2) ↔ ∃ y : F, v (φ.symm (algebraMap F E x)) = v (φ.symm (algebraMap F E y)) ^ 2`.

Use `exists_congr fun y => ?_` and prove the remaining obligations. Rewrite using `[← hn x, ← hn y, ← norm_pow, ← map_pow φ, norm_eq_iff_valuation_eq K φ hball, map_pow]`. Take `⟨π, hπ⟩` from `(IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E`. Take `⟨p, hp⟩` from `hU.unram (φ π)`. Establish `hvp : v (φ.symm (algebraMap F E p)) = exp (-1)`.

Rewrite using `[← hπ]`. Use `((norm_eq_iff_valuation_eq K φ hball _ _).1 ?_)` and prove the remaining obligations. Rewrite using `[hn, hp]`. Unfold `GlobalTheory.JR.eta UQ.eta val`. Rewrite using `[key]`.

Rewrite using `[← hv]`. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using `only [map_zero, WithZero.log_zero, neg_zero, zpow_zero, Rat.cast_one]`. Rewrite using `[if_pos ⟨0, by simp⟩]`.

Use `set z := φ.symm (algebraMap F E x) with hz`. Establish `hz0 : z ≠ 0` using `by simpa [z] using hx`. Establish `hvz : v z ≠ 0` using `(Valuation.ne_zero_iff v).2 hz0`. Use `set m := log (v z) with hm`. Establish `hiff : (∃ y : F, v z = v (φ.symm (algebraMap F E y)) ^ 2) ↔ Even m`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Use `⟨log (v (φ.symm (algebraMap F E y))), ?_⟩` and prove the remaining obligations. Rewrite using `[hm, hy, log_pow, two_nsmul]`. Introduce and unpack `⟨l, hl⟩`.

Use `⟨p ^ (-l), ?_⟩` and prove the remaining obligations. Establish `hl' : log (v z) = l + l` using `hl`. Rewrite using `[map_zpow₀, map_zpow₀, map_zpow₀, hvp, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_log hvz, hl']`. Use `congr 1`. Simplify using `only [smul_eq_mul, nsmul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `split_ifs with h`. Rewrite using `[Even.neg_one_zpow ((hiff.1 h).neg)]`. Simplify using the standard rewrite rules.

Establish `ho : Odd (-m)` using `(Int.not_even_iff_odd.1 (fun he => h (hiff.2 (by simpa using he.neg))))`. Rewrite using `[Odd.neg_one_zpow ho]`. Simplify using the standard rewrite rules.
-/
theorem eta_eq_uq_eta : ∀ (K : UQ) (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (φ : K.E ≃+* E),
    (∀ y : K.E, ‖φ y‖ ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range) →
    ∀ x : F, GlobalTheory.JR.eta x = ((K.eta (φ.symm (algebraMap F E x)) : ℚ) : ℂ) := by
  intro K F E _ _ _ _ hU φ hball x
  set v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E with hv
  have hn : ∀ t : F, ‖φ (φ.symm (algebraMap F E t))‖ = ‖t‖ := fun t => by
    rw [RingEquiv.apply_symm_apply, norm_algebraMap']
  have key : (∃ y : F, ‖x‖ = ‖y‖ ^ 2) ↔
      ∃ y : F, v (φ.symm (algebraMap F E x)) = v (φ.symm (algebraMap F E y)) ^ 2 := by
    refine exists_congr fun y => ?_
    rw [← hn x, ← hn y, ← norm_pow, ← map_pow φ, norm_eq_iff_valuation_eq K φ hball, map_pow]

  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E
  obtain ⟨p, hp⟩ := hU.unram (φ π)
  have hvp : v (φ.symm (algebraMap F E p)) = exp (-1) := by
    rw [← hπ]
    refine ((norm_eq_iff_valuation_eq K φ hball _ _).1 ?_)
    rw [hn, hp]
  unfold GlobalTheory.JR.eta UQ.eta val
  rw [key]
  rw [← hv]
  by_cases hx : x = 0
  · subst hx
    simp only [map_zero, WithZero.log_zero, neg_zero, zpow_zero, Rat.cast_one]
    rw [if_pos ⟨0, by simp⟩]
  set z := φ.symm (algebraMap F E x) with hz
  have hz0 : z ≠ 0 := by simpa [z] using hx
  have hvz : v z ≠ 0 := (Valuation.ne_zero_iff v).2 hz0
  set m := log (v z) with hm
  have hiff : (∃ y : F, v z = v (φ.symm (algebraMap F E y)) ^ 2) ↔ Even m := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨log (v (φ.symm (algebraMap F E y))), ?_⟩
      rw [hm, hy, log_pow, two_nsmul]
    · rintro ⟨l, hl⟩
      refine ⟨p ^ (-l), ?_⟩
      have hl' : log (v z) = l + l := hl
      rw [map_zpow₀, map_zpow₀, map_zpow₀, hvp, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_log hvz, hl']
      congr 1
      simp only [smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
  split_ifs with h
  · rw [Even.neg_one_zpow ((hiff.1 h).neg)]; simp
  · have ho : Odd (-m) := (Int.not_even_iff_odd.1 (fun he => h (hiff.2 (by simpa using he.neg))))
    rw [Odd.neg_one_zpow ho]; simp

end GlobalTheory.EtaCompare
