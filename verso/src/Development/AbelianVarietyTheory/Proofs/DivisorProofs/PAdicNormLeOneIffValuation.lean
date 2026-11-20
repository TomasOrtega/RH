import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt
open scoped NNReal

namespace GlobalTheory.PlaceNorm

/- English proof (translation)
Introduce `K _ _ la p _ T io e ho k kO hk a`. Take `⟨r, hr⟩` from `GlobalTheory.CompHt.exists_log_eq (PadicComplexInt.integers p) k kO hk`. Establish `hnorm : ∀ x : ℂ_[p], ((Valued.v x : ℝ≥0) : ℝ) = ‖x‖` using `GlobalTheory.FlatModel.coe_valued p`. Establish `hpne : (p : ℕ) ≠ 0` using `(Fact.out : p.Prime).ne_zero`. Establish `hp0 : (p : T.Fr) ≠ 0` using `Nat.cast_ne_zero.2 hpne`.

Establish `hpv : 0 ≤ vV T.V (p : T.Fr)`. Establish `h1` using `(IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) (p : T.V)`. Establish `h1' : valV T.V (p : T.Fr) ≤ 1`. Rewrite using `[← map_natCast (algebraMap T.V T.Fr)]`. Conclude with `h1`.

Establish `h2 : valV T.V (p : T.Fr) ≠ 0` using `valV_ne_zero hp0`. Establish `h3` using `(WithZero.log_le_log h2 one_ne_zero).2 h1'`. Rewrite `h3` using `[WithZero.log_one]`. Simplify using `only [vV]`. Use linear arithmetic over natural numbers and integers.

Establish `h1` using `hr (p : T.Fr) hp0`. Rewrite `h1` using `[map_natCast, hnorm]`. Establish `hpn : ‖(p : ℂ_[p])‖ < 1` using `GlobalTheory.RingBasics.norm_p_lt`. Establish `hpos : 0 < ‖(p : ℂ_[p])‖` using `norm_pos_iff.2 (Nat.cast_ne_zero.2 hpne)`. Establish `hl : Real.log ‖(p : ℂ_[p])‖ < 0` using `Real.log_neg hpos hpn`.

Establish `hr0 : r < 0`. Rewrite `hl` using `[h1]`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `: (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) * r` using `mul_nonneg (by exact_mod_cast hpv) hc`.

Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality. Simplify using the standard rewrite rules. Establish `hx : io a ≠ 0` using `(map_ne_zero io).2 ha`.

Establish `hk0 : k (io a) ≠ 0` using `(map_ne_zero k).2 hx`. Establish `h2` using `hr (io a) hx`. Rewrite `h2` using `[hnorm, ho.2 a]`. Establish `hva : la.valuation K a ≠ 0` using `(la.valuation K).ne_zero_iff.2 ha`. Establish `he : (0 : ℝ) < e` using `by exact_mod_cast ho.1`.

Rewrite using `[← Real.log_nonpos_iff (norm_nonneg _), h2, ← WithZero.log_le_log hva one_ne_zero, WithZero.log_one]`. Establish `hv : vLa la a = -WithZero.log (la.valuation K a)` using `rfl`. Use `push_cast`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h3 : 0 ≤ (e : ℝ) * (vLa la a : ℝ)` using `by nlinarith`. Establish `h4 : (0 : ℝ) ≤ (vLa la a : ℝ)`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h5 : (0 : ℤ) ≤ vLa la a` using `by exact_mod_cast h4`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Establish `h5 : (0 : ℤ) ≤ vLa la a` using `by omega`. Establish `h4 : (0 : ℝ) ≤ (vLa la a : ℝ)` using `by exact_mod_cast h5`.

Establish `h3 : 0 ≤ (e : ℝ) * (vLa la a : ℝ)` using `mul_nonneg he.le h4`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_le_one_iff_valuation_le_one :
    ∀ {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime] (T : CDVR)
      (io : K →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (k : T.Fr →+* ℂ_[p]) (kO : T.V →+* 𝓞_ℂ_[p]),
      (∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a)) →
      ∀ a : K, ‖k (io a)‖ ≤ 1 ↔ la.valuation K a ≤ 1 := by
  intro K _ _ la p _ T io e ho k kO hk a
  obtain ⟨r, hr⟩ := GlobalTheory.CompHt.exists_log_eq (PadicComplexInt.integers p) k kO hk
  have hnorm : ∀ x : ℂ_[p], ((Valued.v x : ℝ≥0) : ℝ) = ‖x‖ := GlobalTheory.FlatModel.coe_valued p
  have hpne : (p : ℕ) ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp0 : (p : T.Fr) ≠ 0 := Nat.cast_ne_zero.2 hpne

  have hpv : 0 ≤ vV T.V (p : T.Fr) := by
    have h1 := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) (p : T.V)
    have h1' : valV T.V (p : T.Fr) ≤ 1 := by
      rw [← map_natCast (algebraMap T.V T.Fr)]; exact h1
    have h2 : valV T.V (p : T.Fr) ≠ 0 := valV_ne_zero hp0
    have h3 := (WithZero.log_le_log h2 one_ne_zero).2 h1'
    rw [WithZero.log_one] at h3
    simp only [vV]; omega

  have h1 := hr (p : T.Fr) hp0
  rw [map_natCast, hnorm] at h1
  have hpn : ‖(p : ℂ_[p])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hpos : 0 < ‖(p : ℂ_[p])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hpne)
  have hl : Real.log ‖(p : ℂ_[p])‖ < 0 := Real.log_neg hpos hpn
  have hr0 : r < 0 := by
    rw [h1] at hl
    by_contra hc
    push_neg at hc
    have : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) * r := mul_nonneg (by exact_mod_cast hpv) hc
    linarith
  by_cases ha : a = 0
  · subst ha; simp
  have hx : io a ≠ 0 := (map_ne_zero io).2 ha
  have hk0 : k (io a) ≠ 0 := (map_ne_zero k).2 hx
  have h2 := hr (io a) hx
  rw [hnorm, ho.2 a] at h2
  have hva : la.valuation K a ≠ 0 := (la.valuation K).ne_zero_iff.2 ha
  have he : (0 : ℝ) < e := by exact_mod_cast ho.1
  rw [← Real.log_nonpos_iff (norm_nonneg _), h2, ← WithZero.log_le_log hva one_ne_zero, WithZero.log_one]
  have hv : vLa la a = -WithZero.log (la.valuation K a) := rfl
  push_cast
  constructor
  · intro h
    have h3 : 0 ≤ (e : ℝ) * (vLa la a : ℝ) := by nlinarith
    have h4 : (0 : ℝ) ≤ (vLa la a : ℝ) := by
      by_contra hc; push_neg at hc; nlinarith
    have h5 : (0 : ℤ) ≤ vLa la a := by exact_mod_cast h4
    omega
  · intro h
    have h5 : (0 : ℤ) ≤ vLa la a := by omega
    have h4 : (0 : ℝ) ≤ (vLa la a : ℝ) := by exact_mod_cast h5
    have h3 : 0 ≤ (e : ℝ) * (vLa la a : ℝ) := mul_nonneg he.le h4
    nlinarith

end GlobalTheory.PlaceNorm
