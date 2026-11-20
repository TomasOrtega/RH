import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValueRamifiedOfLifts
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRamifiedEigenLiftsOfChartDirectionsStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueBoundOfColumnProductsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

namespace GlobalTheory.PlaceInt.ChartRam

/- English proof (translation)
Use `⟨IsFractionRing.injective T.V T.Fr, fun y => ?_⟩` and prove the remaining obligations. Establish `hNV0 : (N : T.V) ≠ 0` using `by exact_mod_cast hN0`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible T.V`. Take `⟨m, hm⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hNV0 hϖ`. Establish `hϖN : ϖ ∣ (N : T.V)`.

Break down `m with _ | m` into its components or cases. Conclude with `absurd (hm.isUnit_iff.2 (by simp)) hNu`. Conclude with `(dvd_pow_self ϖ (Nat.succ_ne_zero m)).trans hm.symm.dvd`. Take `⟨a, s, hs, rfl⟩` from `IsFractionRing.div_surjective (A := T.V) y`. Establish `hs0 : s ≠ 0` using `nonZeroDivisors.ne_zero hs`.

Take `⟨n, hn⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hs0 hϖ`. Establish `hsd : s ∣ (N : T.V) ^ n` using `hn.dvd.trans (pow_dvd_pow_of_dvd hϖN n)`. Take `⟨c, hc⟩` from `hsd`. Use `⟨c * a, N ^ n, pow_pos (Nat.pos_of_ne_zero hN0) n, ?_⟩` and prove the remaining obligations. Establish `hsK : algebraMap T.V T.Fr s ≠ 0`.

Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)]`. Conclude with `hs0`. Establish `hcast : ((N ^ n : ℕ) : T.Fr) = algebraMap T.V T.Fr ((N : T.V) ^ n)`. Rewrite using `[map_pow, map_natCast]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[hcast, hc, map_mul, map_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem isRQ_of_not_isUnit (T : CDVR) (N : ℕ) (hN0 : N ≠ 0) (hNu : ¬ IsUnit (N : T.V)) :
    TB.IsRQ (R := T.V) T.Fr := by
  refine ⟨IsFractionRing.injective T.V T.Fr, fun y => ?_⟩
  have hNV0 : (N : T.V) ≠ 0 := by exact_mod_cast hN0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hNV0 hϖ
  have hϖN : ϖ ∣ (N : T.V) := by
    rcases m with _ | m
    · exact absurd (hm.isUnit_iff.2 (by simp)) hNu
    · exact (dvd_pow_self ϖ (Nat.succ_ne_zero m)).trans hm.symm.dvd
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := T.V) y
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hs0 hϖ
  have hsd : s ∣ (N : T.V) ^ n := hn.dvd.trans (pow_dvd_pow_of_dvd hϖN n)
  obtain ⟨c, hc⟩ := hsd
  refine ⟨c * a, N ^ n, pow_pos (Nat.pos_of_ne_zero hN0) n, ?_⟩
  have hsK : algebraMap T.V T.Fr s ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)]; exact hs0
  have hcast : ((N ^ n : ℕ) : T.Fr) = algebraMap T.V T.Fr ((N : T.V) ^ n) := by
    rw [map_pow, map_natCast]; push_cast; rfl
  rw [hcast, hc, map_mul, map_mul]
  field_simp

/- English proof (translation)
Establish `hr : algebraMap T.V T.Fr (N : T.V) ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)]`. Conclude with `hN0` after adjusting the coercions. Establish `h1` using `(IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) (N : T.V)`. Establish `h2 : valV T.V (algebraMap T.V T.Fr (N : T.V)) ≠ 0` using `valV_ne_zero hr`.

Establish `h3` using `(WithZero.log_le_log h2 one_ne_zero).mpr h1`. Rewrite `h3` using `[WithZero.log_one, map_natCast]`. Unfold `vV`. Use linear arithmetic over natural numbers and integers.
-/
theorem vV_natCast_nonneg (T : CDVR) (N : ℕ) (hN0 : N ≠ 0) : 0 ≤ vV T.V (N : T.Fr) := by
  have hr : algebraMap T.V T.Fr (N : T.V) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)]
    exact_mod_cast hN0
  have h1 := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) (N : T.V)
  have h2 : valV T.V (algebraMap T.V T.Fr (N : T.V)) ≠ 0 := valV_ne_zero hr
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr h1
  rw [WithZero.log_one, map_natCast] at h3
  unfold vV
  omega

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ hstar T io y C hG p a m hp hpu hpm hd hmv e he w n`. Use `GlobalTheory.T.harmonicValue_bound_of_column_products E H Dw l Xo c hstar T io y C e _ w n ?_` and prove the remaining obligations. Introduce `k P hP f hf`. Set `_` to `io.toAlgebra`. Take `⟨π, _, _, cc, s, hcs, φ, ψ, hψ, heig, h21a, h21b, h21c⟩` from `GlobalTheory.T.exists_ramified_eigen_lifts_of_chart_directions E H Dw l Xo c hstar T io y C hG p a m hp hpu hpm hd hmv e he`.

Take `⟨hF, hA, h1, h2, hs, had, hu⟩` from `C.gen.1`. Establish `hinj : Function.Injective (algebraMap T.V T.Fr)` using `IsFractionRing.injective T.V T.Fr`. Set `t : CVA.IntTie (algebraMap T.V T.Fr) C.ch.B` to `⟨C.FT, C.actT, C.ph1T, C.ph2T, C.syT, C.adT, funext fun i => (hF i).symm, fun a => funext fun i => (hA a i).symm, h1.symm, h2.symm, hs.symm, fun a => (had a).symm⟩`. Establish `huv : C.ch.uvec = fun ℓ i => algebraMap T.V T.Fr (C.uvecT ℓ i)` using `funext fun ℓ => funext fun i => hu ℓ i`. Simplify using `only [huv] at heig h21a h21b h21c`.

Use `set cJ : ℝ := (vV T.V (p : T.Fr) : ℝ) / e * ((a : ℝ) / Module.finrank ℚ E) with hcJ`. Establish `hv : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ)` using `by exact_mod_cast vV_natCast_nonneg T p hp.ne_zero`. Establish `hcJ0 : 0 ≤ cJ` using `by rw [hcJ]; positivity`. Establish `hw0 : H.w0 + star H.w0 = 1` using `by rw [hstar]; exact CVA.cmHostUnit_add_conj_eq_one H`. Establish `hpmin : ∀ mo ∈ P.support, ∑ b, TB.pairMin (fun ℓ : Lt1 Dw => cc ℓ.1) (fun ℓ => s ℓ.1) (colL Dw.mult n mo b) ≤ Formalism.L2.Pj.DF Dw w / 2` using `fun mo hmo => sum_pairMin_le Dw.mult n cc s (fun τ i => w (τ, i)) mo (hP.1.2.2 mo hmo)`.

Establish `hmem` using `chartValJ (isRQ_of_not_isUnit T p hp.ne_zero hpu) (Jv T e cJ) (one_mem_Jv T e hcJ0) (CVA.fbOf t hinj) C.ch.h (CVA.fbOf_canon t hinj C.ch.h C.ch.gauge) H.w0 hw0 k Dw.mult ComplexEmbedding.conjugate (fun τ => by ext x; simp) (InPsi H) (CVA.inPsi_or H) cc s hcs C.uvecT φ ψ hψ heig h …`. Establish `hval` using `mem_Jv_pow T e hcJ0 _ _ hmem`. Simplify using `only [CVA.fbOf_nabVal] at hval`. Rewrite using `[huv]`. Use `le_trans ?_ hval` and prove the remaining obligations.

Apply `EReal.coe_le_coe_iff.2` to reduce the goal to its premises. Establish `hdiv : ((Formalism.L2.Pj.DF Dw w / 2 : ℕ) : ℝ) ≤ (Formalism.L2.Pj.DF Dw w : ℝ) / 2`. Rewrite using `[le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]`. Conclude with `Nat.div_mul_le_self _ 2` after adjusting the coercions. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem chBound_ramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), IsGalois ℚ E → ∀ (p a m : ℕ), p.Prime → ¬ IsUnit (p : T.V) → ¬ p ∣ m → (NumberField.discr E).natAbs = p ^ a * m → (∀ 𝔭 : Ideal (𝓞 E), 𝔭.IsPrime → (p : 𝓞 E) ∈ 𝔭 → ∃ x ∈ 𝔭, H.bar x ∉ 𝔭) → ∀ e : ℕ, 0 < e → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ChBound C e ((vV T.V (p : T.Fr) : ℝ) / e * ((a : ℝ) / Module.finrank ℚ E) * (Formalism.L2.Pj.DF Dw w : ℝ) / 2) w n := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C hG p a m hp hpu hpm hd hmv e he w n
  refine GlobalTheory.T.harmonicValue_bound_of_column_products E H Dw l Xo c hstar T io y C e _ w n ?_
  intro k P hP f hf
  let _ := io.toAlgebra
  obtain ⟨π, _, _, cc, s, hcs, φ, ψ, hψ, heig, h21a, h21b, h21c⟩ :=
    GlobalTheory.T.exists_ramified_eigen_lifts_of_chart_directions E H Dw l Xo c hstar T io y C hG p a m hp hpu hpm hd hmv e he
  obtain ⟨hF, hA, h1, h2, hs, had, hu⟩ := C.gen.1
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  let t : CVA.IntTie (algebraMap T.V T.Fr) C.ch.B :=
    ⟨C.FT, C.actT, C.ph1T, C.ph2T, C.syT, C.adT, funext fun i => (hF i).symm, fun a => funext fun i => (hA a i).symm,
      h1.symm, h2.symm, hs.symm, fun a => (had a).symm⟩
  have huv : C.ch.uvec = fun ℓ i => algebraMap T.V T.Fr (C.uvecT ℓ i) := funext fun ℓ => funext fun i => hu ℓ i
  simp only [huv] at heig h21a h21b h21c
  set cJ : ℝ := (vV T.V (p : T.Fr) : ℝ) / e * ((a : ℝ) / Module.finrank ℚ E) with hcJ
  have hv : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) := by exact_mod_cast vV_natCast_nonneg T p hp.ne_zero
  have hcJ0 : 0 ≤ cJ := by rw [hcJ]; positivity
  have hw0 : H.w0 + star H.w0 = 1 := by rw [hstar]; exact CVA.cmHostUnit_add_conj_eq_one H
  have hpmin : ∀ mo ∈ P.support, ∑ b, TB.pairMin (fun ℓ : Lt1 Dw => cc ℓ.1) (fun ℓ => s ℓ.1)
      (colL Dw.mult n mo b) ≤ Formalism.L2.Pj.DF Dw w / 2 := fun mo hmo =>
    sum_pairMin_le Dw.mult n cc s (fun τ i => w (τ, i)) mo (hP.1.2.2 mo hmo)
  have hmem := chartValJ (isRQ_of_not_isUnit T p hp.ne_zero hpu) (Jv T e cJ) (one_mem_Jv T e hcJ0)
    (CVA.fbOf t hinj) C.ch.h (CVA.fbOf_canon t hinj C.ch.h C.ch.gauge) H.w0 hw0 k
    Dw.mult ComplexEmbedding.conjugate (fun τ => by ext x; simp) (InPsi H)
    (CVA.inPsi_or H) cc s hcs C.uvecT φ ψ hψ heig h21a h21b h21c n (fun τ i => w (τ, i)) P hP
    (Formalism.L2.Pj.DF Dw w / 2) hpmin f hf
  have hval := mem_Jv_pow T e hcJ0 _ _ hmem
  simp only [CVA.fbOf_nabVal] at hval
  rw [huv]
  refine le_trans ?_ hval
  apply EReal.coe_le_coe_iff.2
  have hdiv : ((Formalism.L2.Pj.DF Dw w / 2 : ℕ) : ℝ) ≤ (Formalism.L2.Pj.DF Dw w : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast Nat.div_mul_le_self _ 2
  nlinarith

end GlobalTheory.PlaceInt.ChartRam
