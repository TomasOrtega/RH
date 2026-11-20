import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementV
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalC

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair mfact)

namespace InflationOneCocycles

/- English proof (translation)
Unfold `mfact`. Rewrite using `[Finsupp.prod_single_index]`. Both sides reduce to the same expression.
-/
theorem mfact_single_unit (n : ℕ) : mfact (Finsupp.single () n) = n.factorial := by
  unfold mfact
  rw [Finsupp.prod_single_index]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h κ`. Establish `e : κ = Finsupp.single () (κ ())`. Use `ext`. Simplify using the standard rewrite rules.

Rewrite using `[e, mfact_single_unit]`. Conclude with `h (κ ())`. Introduce `h n`. Use `h (Finsupp.single () n)` as an intermediate fact. Rewrite `this` using `[mfact_single_unit]`.

Conclude with `this`.
-/
theorem jetsIn1_iff {K : Type} [Field K] (R : Subring K) (f : PowerSeries K) :
    JetsIn1 R f ↔ JetsIn R (f : MvPowerSeries Unit K) := by
  constructor
  · intro h κ
    have e : κ = Finsupp.single () (κ ()) := by
      ext
      simp
    rw [e, mfact_single_unit]
    exact h (κ ())
  · intro h n
    have := h (Finsupp.single () n)
    rw [mfact_single_unit] at this
    exact this

/- English proof (translation)
Establish `e : MvPowerSeries.C (S / 2) * sqSum c = ∑ i, MvPowerSeries.C (S * c i) * (MvPowerSeries.C (((2 : ℕ).factorial : K)⁻¹) * MvPowerSeries.X i ^ 2)`. Unfold `sqSum`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]`.

Use `congr 2`. Simplify using `only [Nat.factorial]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `jetsIn_sum _ _ fun i _ => jetsIn_mul (jetsIn_C (R.mul_mem hS (hc i))) (jetsIn_divPow (MvPowerSeries.constantCoeff_X i) (jetsIn_X i) 2)`.
-/
theorem jetsIn_half_sqSum {K : Type} [Field K] [CharZero K] {R : Subring K} {n : Type} [Fintype n]
    {S : K} (hS : S ∈ R) {c : n → K} (hc : ∀ i, c i ∈ R) :
    JetsIn R (MvPowerSeries.C (S / 2) * sqSum c) := by
  have e : MvPowerSeries.C (S / 2) * sqSum c =
      ∑ i, MvPowerSeries.C (S * c i) *
        (MvPowerSeries.C (((2 : ℕ).factorial : K)⁻¹) * MvPowerSeries.X i ^ 2) := by
    unfold sqSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
    congr 2
    simp only [Nat.factorial]
    push_cast
    ring
  rw [e]
  exact jetsIn_sum _ _ fun i _ => jetsIn_mul (jetsIn_C (R.mul_mem hS (hc i)))
    (jetsIn_divPow (MvPowerSeries.constantCoeff_X i) (jetsIn_X i) 2)

/- English proof (translation)
Use `h 1` as an intermediate fact. Simplify `this` using `[binom]`.
-/
theorem mem_of_binomScalar {K : Type} [Field K] {R : Subring K} {z : K} (h : IsBinomScalar R z) :
    z ∈ R := by
  have := h 1
  simpa [binom] using this

/- English proof (translation)
Establish `hv : PowerSeries.constantCoeff linv = 0` using `hlp.2.2.1`. Establish `hs : PowerSeries.HasSubst linv` using `JetSubstitutionLemmas.hs1 hv`. Use `⟨?_, fun i hi _ => hj i hi, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_one, norm_one, Real.one_rpow]`. Conclude with `hj 2 (by norm_num)`.

Use `set S : K := jet l ph 2 / 2 with hS set ph0 : PowerSeries K := PowerSeries.subst linv ph - PowerSeries.C S * PowerSeries.X ^ 2 with hph0`. Establish `j0 : JetsIn1 (unitBall K) ph0` using `jetsIn1_rest hlp hph fun i hi _ => hj i hi`. Establish `cph0 : PowerSeries.constantCoeff ph0 = 0`. Rewrite using `[hph0, map_sub, JetSubstitutionLemmas.cc_subst1 hv, hph]`. Simplify using the standard rewrite rules.

Establish `c1 : PowerSeries.constantCoeff (-ph) = 0` using `by rw [map_neg, hph, neg_zero]`. Establish `c2 : PowerSeries.constantCoeff (-(PowerSeries.C S * PowerSeries.X ^ 2) : PowerSeries K) = 0`. Simplify using the standard rewrite rules. Establish `c3 : PowerSeries.constantCoeff (-ph0) = 0` using `by rw [map_neg, cph0, neg_zero]`. Establish `e : PowerSeries.subst linv (-ph) = -(PowerSeries.C S * PowerSeries.X ^ 2) + -ph0`.

Rewrite using `[← PowerSeries.coe_substAlgHom hs, map_neg, PowerSeries.coe_substAlgHom hs, hph0]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨(mvExp (-ph0) : PowerSeries K), ?_, (mvExpLaws K Unit).2.1 _ c3, ?_⟩` and prove the remaining obligations. Rewrite using `[jetsIn1_iff]`. Conclude with `jetsIn_mvExp c3 (jetsIn_neg ((jetsIn1_iff _ _).1 j0))`.

Rewrite using `[mvExpSubst K Unit _ linv c1 hv, e]`. Conclude with `mvExp_add c2 c3`.
-/
theorem shapeAt_one {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
    {l linv ph : PowerSeries K} (hlp : IsLogPair l linv) (hph : PowerSeries.constantCoeff ph = 0)
    (hj : ∀ i : ℕ, 1 ≤ i → ‖jet l ph i‖ ≤ 1) : ShapeAt l linv ph 1 := by
  have hv : PowerSeries.constantCoeff linv = 0 := hlp.2.2.1
  have hs : PowerSeries.HasSubst linv := JetSubstitutionLemmas.hs1 hv
  refine ⟨?_, fun i hi _ => hj i hi, ?_⟩
  · rw [Nat.cast_one, norm_one, Real.one_rpow]
    exact hj 2 (by norm_num)
  · set S : K := jet l ph 2 / 2 with hS
    set ph0 : PowerSeries K := PowerSeries.subst linv ph - PowerSeries.C S * PowerSeries.X ^ 2
      with hph0
    have j0 : JetsIn1 (unitBall K) ph0 := jetsIn1_rest hlp hph fun i hi _ => hj i hi
    have cph0 : PowerSeries.constantCoeff ph0 = 0 := by
      rw [hph0, map_sub, JetSubstitutionLemmas.cc_subst1 hv, hph]
      simp
    have c1 : PowerSeries.constantCoeff (-ph) = 0 := by rw [map_neg, hph, neg_zero]
    have c2 : PowerSeries.constantCoeff (-(PowerSeries.C S * PowerSeries.X ^ 2) : PowerSeries K) = 0 := by
      simp
    have c3 : PowerSeries.constantCoeff (-ph0) = 0 := by rw [map_neg, cph0, neg_zero]
    have e : PowerSeries.subst linv (-ph) = -(PowerSeries.C S * PowerSeries.X ^ 2) + -ph0 := by
      rw [← PowerSeries.coe_substAlgHom hs, map_neg, PowerSeries.coe_substAlgHom hs, hph0]
      ring
    refine ⟨(mvExp (-ph0) : PowerSeries K), ?_, (mvExpLaws K Unit).2.1 _ c3, ?_⟩
    · rw [jetsIn1_iff]
      exact jetsIn_mvExp c3 (jetsIn_neg ((jetsIn1_iff _ _).1 j0))
    · rw [mvExpSubst K Unit _ linv c1 hv, e]
      exact mvExp_add c2 c3

end InflationOneCocycles

open InflationOneCocycles

/- English proof (translation)
Introduce `K _ _ _ l linv ph hF hu h1 hj O _ _ τ hE hB hN hA n m _ _ _ w hw δ hδ Th G hG hT`. Take `⟨J, hJ, hJe⟩` from `intAtD K l linv ph 1 hF hu h1 (shapeAt_one hF.1 hF.2.2 hj) O τ hE hB hN hA n m w hw δ hδ Th G hG hT`. Establish `hq : JetsIn (unitBall K) (MvPowerSeries.C (jet l ph 2 / 2) * sqSum (fun j => τ (w j)))` using `jetsIn_half_sqSum (hj 2 (by norm_num)) fun j => mem_of_binomScalar (hB (w j) (hw j))`. Establish `c0 : MvPowerSeries.constantCoeff (-(MvPowerSeries.C (jet l ph 2 / 2) * sqSum (fun j => τ (w j)))) = 0`. Rewrite using `[map_neg, map_mul, cc_sqSum, mul_zero, neg_zero]`.

Establish `key : JetsIntegral Th`. Rewrite using `[hJe]`. Conclude with `jetsIn_mul (R := unitBall K) (jetsIn_mvExp c0 (jetsIn_neg hq)) hJ`. Use `⟨key, fun ν _ A hAx P hP => ?_⟩` and prove the remaining obligations. Conclude with `Formalism.DworkPowerSeriesWeights.intOp K ν _ (jetsIn_linSub (R := unitBall K) hAx key) P hP`.
-/
theorem integral_unramified_holds : IntUnram := by
  intro K _ _ _ l linv ph hF hu h1 hj O _ _ τ hE hB hN hA n m _ _ _ w hw δ hδ Th G hG hT
  obtain ⟨J, hJ, hJe⟩ := intAtD K l linv ph 1 hF hu h1 (shapeAt_one hF.1 hF.2.2 hj) O τ hE hB hN hA
    n m w hw δ hδ Th G hG hT
  have hq : JetsIn (unitBall K) (MvPowerSeries.C (jet l ph 2 / 2) * sqSum (fun j => τ (w j))) :=
    jetsIn_half_sqSum (hj 2 (by norm_num)) fun j => mem_of_binomScalar (hB (w j) (hw j))
  have c0 : MvPowerSeries.constantCoeff
      (-(MvPowerSeries.C (jet l ph 2 / 2) * sqSum (fun j => τ (w j)))) = 0 := by
    rw [map_neg, map_mul, cc_sqSum, mul_zero, neg_zero]
  have key : JetsIntegral Th := by
    rw [hJe]
    exact jetsIn_mul (R := unitBall K) (jetsIn_mvExp c0 (jetsIn_neg hq)) hJ
  refine ⟨key, fun ν _ A hAx P hP => ?_⟩
  exact Formalism.DworkPowerSeriesWeights.intOp K ν _ (jetsIn_linSub (R := unitBall K) hAx key) P hP

/- English proof (translation)
Introduce `K _ _ _ W hc h2 s2 al albar t ι _ neg xP yP hE hx hy hNal hal ht hd hb hs`. Conclude with `curveJetsUnram K W hc h2 s2 al albar t ι neg xP yP hE hx hy hNal hal ht hd hb hs`.
-/
theorem curve_jets_unramified_holds : CurveJetsUnram := by
  intro K _ _ _ W hc h2 s2 al albar t ι _ neg xP yP hE hx hy hNal hal ht hd hb hs
  exact curveJetsUnram K W hc h2 s2 al albar t ι neg xP yP hE hx hy hNal hal ht hd hb hs

end Formalism.L2.Th1.G
