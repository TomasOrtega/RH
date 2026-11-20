import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountContinuousFromAboveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairBallsFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodHermitianLineBundlePairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeArithVolumeOfFrequentlySmallSectionsLowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMetricShiftIsNefPowTensAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoSelfIntersectionPowTensorDivPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsTwistedPowerEncardEqBallStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardSmallSectionsGeOfShiftNefStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

noncomputable section

namespace GlobalTheory.VolBr

/- English proof (translation)
Introduce `hHS hAC hNN k _ X _ p D hX L a hNF hSP hSI`. Take `⟨P, b, s, t, hPL, hG⟩` from `GlobalTheory.T.exists_good_hermitian_lineBundle_pair hAC k X p D hX L`. Substitute `hPL` using the available equality. Take `⟨α, hα, hαlim⟩` from `GlobalTheory.T.tendsto_selfIntersection_pow_tensor_div_pow hAC k X p D hX P.L P.A a hSI`. Take `⟨hRL, hRA, -⟩` from `GlobalTheory.T.represents_base_bundles_and_trivial k X p P`.

Apply `GlobalTheory.T.le_arithVolume_of_frequently_smallSections_lower k X p D P.L a` to reduce the goal to its premises. Introduce `ε hε`. Establish `hF1 : (1 : ℝ) ≤ ((D + 1).factorial : ℝ)` using `by exact_mod_cast Nat.factorial_pos _`. Establish `hε3 : 0 < ε / 3` using `by positivity`. Establish `hlim : ∀ᶠ n : ℕ in atTop, a - ε / 3 < α n / (n : ℝ) ^ (D + 1)` using `hαlim.eventually (lt_mem_nhds (by linarith))`.

Take `⟨n, hn1, hnα, hcont⟩` from `((eventually_ge_atTop 1).and (hlim.and (GlobalTheory.T.small_section_count_continuous_from_above hHS hAC k X p D hX P b s t hG (ε / 3) hε3))).exists`. Establish `hRn : P.Rep (n : ℤ) 1 ((P.L.pow n).tens P.A)`. Establish `h1` using `GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 1 0 P.L n hRL`. Establish `h2` using `GlobalTheory.T.hermPairWithSections_represents_tensor k X p P _ _ 0 1 _ P.A h1 hRA`. Simplify using `using h2`.

Take `⟨t₀, ht₀⟩` from `GlobalTheory.T.exists_metricShift_isNef_pow_tens_ample hAC hNN k X p D hX P.L P.A n hSP hNF hG.ample hG.nef`. Establish `hstep` using `GlobalTheory.T.log_card_smallSections_ge_of_shift_nef hHS hAC k X p D hX P b s t hG n 1 _ (α n) t₀ hRn (hα n) ht₀ (ε / 3) hε3`. Rewrite using `[Filter.frequently_atTop]`. Introduce `N₀`. Take `⟨m, hm, hm1, hm2⟩` from `((eventually_ge_atTop (max N₀ 1)).and (hstep.and hcont)).exists`.

Establish `hmN : N₀ ≤ m` using `le_of_max_le_left hm`. Use `⟨n * m, le_trans hmN (Nat.le_mul_of_pos_left m hn1), ?_⟩` and prove the remaining obligations. Establish `hsm` using `(GlobalTheory.T.smallSections_twistedPower_encard_eq_ball k X p P 1 0 P.L hRL 0 (n * m)).2.1`. Rewrite `hsm` using `[mul_one, mul_zero]`. Establish `hfin` using `GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hX P b s t hG ((n * m : ℕ) : ℤ) 0 1 hAC`.

Establish `hnc : (P.L.pow (n * m)).smallSec.ncard = (P.Bl ((n * m : ℕ) : ℤ) 0 1).ncard`. Rewrite using `[Set.ncard_def, Set.ncard_def, hsm]`. Use `⟨Set.encard_lt_top_iff.mp (hsm ▸ Set.encard_lt_top_iff.mpr hfin), ?_⟩` and prove the remaining obligations. Rewrite using `[hnc]`. Express the relevant statement in the definitionally equal form `_ ≤ P.lc ((n * m : ℕ) : ℤ) 0 1`.

Establish `hcast : (m : ℤ) * (n : ℤ) = ((n * m : ℕ) : ℤ)` using `by push_cast; ring`. Rewrite `hm1` using `[hcast, mul_one]`. Use `set F : ℝ := ((D + 1).factorial : ℝ)`. Use `set x : ℝ := (n : ℝ) ^ (D + 1) with hx`. Use `set y : ℝ := (m : ℝ) ^ (D + 1) with hy`.

Establish `hx1 : 1 ≤ x` using `one_le_pow₀ (by exact_mod_cast hn1)`. Establish `hy0 : 0 ≤ y` using `by positivity`. Establish `hN : ((n * m : ℕ) : ℝ) ^ (D + 1) = x * y` using `by push_cast; rw [mul_pow]`. Rewrite `hm2` using `[mul_pow]`. Rewrite using `[hN]`.

Establish `hαx : (a - ε / 3) * x ≤ α n`. Use `(lt_div_iff₀ (by linarith : (0 : ℝ) < x)).mp hnα` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hF0 : 0 < F` using `by linarith`. Establish `e1 : (a - ε / 3) * x * y / F ≤ α n / F * y`.

Rewrite using `[div_mul_eq_mul_div]`. Conclude with `div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hαx hy0) hF0.le`. Establish `e2 : ε / 3 * (x * y) / F ≤ ε / 3 * (x * y)` using `div_le_self (by positivity) hF1`. Establish `e3 : ε / 3 * y ≤ ε / 3 * (x * y)`. Establish `: y ≤ x * y` using `le_mul_of_one_le_left hy0 hx1`.

Conclude with `mul_le_mul_of_nonneg_left this hε3.le`. Establish `e4 : (a / F - ε) * (x * y) = (a - ε / 3) * x * y / F + ε / 3 * (x * y) / F - ε * (x * y)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Combine the linear relations using `[e1, e2, e3, e4, hm1, hm2]`.
-/
theorem volGe_of_hilbertSamuel :
    GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.VolGe := by
  intro hHS hAC hNN k _ X _ p D hX L a hNF hSP hSI
  obtain ⟨P, b, s, t, hPL, hG⟩ := GlobalTheory.T.exists_good_hermitian_lineBundle_pair hAC k X p D hX L
  subst hPL
  obtain ⟨α, hα, hαlim⟩ := GlobalTheory.T.tendsto_selfIntersection_pow_tensor_div_pow hAC k X p D hX P.L P.A a hSI
  obtain ⟨hRL, hRA, -⟩ := GlobalTheory.T.represents_base_bundles_and_trivial k X p P
  apply GlobalTheory.T.le_arithVolume_of_frequently_smallSections_lower k X p D P.L a
  intro ε hε
  have hF1 : (1 : ℝ) ≤ ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hε3 : 0 < ε / 3 := by positivity
  have hlim : ∀ᶠ n : ℕ in atTop, a - ε / 3 < α n / (n : ℝ) ^ (D + 1) :=
    hαlim.eventually (lt_mem_nhds (by linarith))
  obtain ⟨n, hn1, hnα, hcont⟩ := ((eventually_ge_atTop 1).and
    (hlim.and (GlobalTheory.T.small_section_count_continuous_from_above hHS hAC k X p D hX P b s t hG (ε / 3) hε3))).exists
  have hRn : P.Rep (n : ℤ) 1 ((P.L.pow n).tens P.A) := by
    have h1 := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 1 0 P.L n hRL
    have h2 := GlobalTheory.T.hermPairWithSections_represents_tensor k X p P _ _ 0 1 _ P.A h1 hRA
    simpa using h2
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.exists_metricShift_isNef_pow_tens_ample hAC hNN k X p D hX P.L P.A n hSP hNF hG.ample hG.nef
  have hstep := GlobalTheory.T.log_card_smallSections_ge_of_shift_nef hHS hAC k X p D hX P b s t hG n 1 _ (α n) t₀ hRn (hα n) ht₀ (ε / 3) hε3
  rw [Filter.frequently_atTop]
  intro N₀
  obtain ⟨m, hm, hm1, hm2⟩ := ((eventually_ge_atTop (max N₀ 1)).and (hstep.and hcont)).exists
  have hmN : N₀ ≤ m := le_of_max_le_left hm
  refine ⟨n * m, le_trans hmN (Nat.le_mul_of_pos_left m hn1), ?_⟩
  have hsm := (GlobalTheory.T.smallSections_twistedPower_encard_eq_ball k X p P 1 0 P.L hRL 0 (n * m)).2.1
  rw [mul_one, mul_zero] at hsm
  have hfin := GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hX P b s t hG ((n * m : ℕ) : ℤ) 0 1 hAC
  have hnc : (P.L.pow (n * m)).smallSec.ncard = (P.Bl ((n * m : ℕ) : ℤ) 0 1).ncard := by
    rw [Set.ncard_def, Set.ncard_def, hsm]
  refine ⟨Set.encard_lt_top_iff.mp (hsm ▸ Set.encard_lt_top_iff.mpr hfin), ?_⟩
  rw [hnc]
  change _ ≤ P.lc ((n * m : ℕ) : ℤ) 0 1
  have hcast : (m : ℤ) * (n : ℤ) = ((n * m : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, mul_one] at hm1
  set F : ℝ := ((D + 1).factorial : ℝ)
  set x : ℝ := (n : ℝ) ^ (D + 1) with hx
  set y : ℝ := (m : ℝ) ^ (D + 1) with hy
  have hx1 : 1 ≤ x := one_le_pow₀ (by exact_mod_cast hn1)
  have hy0 : 0 ≤ y := by positivity
  have hN : ((n * m : ℕ) : ℝ) ^ (D + 1) = x * y := by push_cast; rw [mul_pow]
  rw [mul_pow] at hm2
  rw [hN]
  have hαx : (a - ε / 3) * x ≤ α n := by
    have := (lt_div_iff₀ (by linarith : (0 : ℝ) < x)).mp hnα
    linarith
  have hF0 : 0 < F := by linarith
  have e1 : (a - ε / 3) * x * y / F ≤ α n / F * y := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hαx hy0) hF0.le
  have e2 : ε / 3 * (x * y) / F ≤ ε / 3 * (x * y) :=
    div_le_self (by positivity) hF1
  have e3 : ε / 3 * y ≤ ε / 3 * (x * y) := by
    have : y ≤ x * y := le_mul_of_one_le_left hy0 hx1
    exact mul_le_mul_of_nonneg_left this hε3.le
  have e4 : (a / F - ε) * (x * y) = (a - ε / 3) * x * y / F + ε / 3 * (x * y) / F - ε * (x * y) := by
    field_simp
    ring
  linarith [e1, e2, e3, e4, hm1, hm2]

end GlobalTheory.VolBr
