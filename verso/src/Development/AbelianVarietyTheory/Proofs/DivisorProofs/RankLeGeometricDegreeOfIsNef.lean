import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ManyIndependentProductsInFunctionFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorOfNefFibresAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionMemBallExpOfProjArithVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoHermLineBundleGeometricDegreePowTensDivPoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulRankLeDegreeOfIndepSmallSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxMonomialFamilyProdMemNormBallOfExponentLtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisFunctionFieldArithmeticVarieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleNefHermitianSmallSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveNonnegCombination
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfSpecializesOfFinite
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef.RankNef

/- English proof (translation)
Introduce `hAr hHS k _ X _ p D hX P hL J _ e x he hx hbox`. Establish `hcz : CharZero X.functionField`. Use `hX.charZero` as an intermediate fact. Conclude with `((X.germToFunctionField ⊤).hom.charZero_iff (X.germToFunctionField_injective ⊤)).1 this`. Establish `htb : IsTranscendenceBasis ℤ x` using `(GlobalTheory.T.isTranscendenceBasis_functionField_arithmeticVariety k X p D hX).2 x hx`.

Take `⟨A, hAamp, hAnef, s, hs, hs0⟩` from `GlobalTheory.AmpleNefSmall.exists_ample_nef_smallSec hAr k X p D hX`. Take `⟨r', hr'⟩` from `exists_isRatSec A.isLB`. Set `Q : Pair p` to `⟨P.L, A, P.r, r', P.hr, hr'⟩`. Establish `hQbox : ∀ c, boxFam e x c ∈ Q.H 1 0`. Introduce `c z i j hi _`.

Choose the witnesses or unpack the hypotheses as in `⟨j', hj'⟩ : ∃ j', z ∈ P.A.B.U j' := by`. Establish `h1 : z ∈ (⨆ j, P.A.B.U j)` using `by rw [P.A.isLB.cover]; trivial`. Conclude with `TopologicalSpace.Opens.mem_iSup.1 h1`. Establish `h2` using `hbox c z i j' hi hj'`. Simplify `h2` using `[Pair.loc, Q]`.

Establish `hbd : ∀ c, ∃ u : ℝ, 0 ≤ u ∧ boxFam e x c ∈ Q.Bl 1 0 (Real.exp u)` using `fun c => GlobalTheory.T.pairSection_mem_ball_exp_of_projArithVariety k X p D hX Q 1 0 _ (hQbox c)`. Use `choose u hu0 hu using hbd`. Use `set t₀ : ℝ := ∑ c, u c with ht₀`. Establish `ht₀0 : 0 ≤ t₀` using `Finset.sum_nonneg fun c _ => hu0 c`. Establish `hBl : ∀ c, boxFam e x c ∈ Q.Bl 1 0 (Real.exp t₀)` using `fun c => ⟨(hu c).1, fun σ y => ((hu c).2 σ y).trans (Real.exp_le_exp.2 (Finset.single_le_sum (fun c _ => hu0 c) (Finset.mem_univ c)))⟩`.

Take `⟨ε, hεinj, hεrange, hεnu, -⟩` from `RepDict.rep_dict k X p Q 0 1 Q.A (Pair.rep_base k X p Q).2.1`. Establish `hsm : ∀ w ∈ A.smallSec, ε w ∈ Q.Bl 0 1 1`. Introduce `w hw`. Use `⟨?_, fun σ y => ?_⟩` and prove the remaining obligations. Rewrite using `[← SetLike.mem_coe, ← hεrange]`.

Conclude with `⟨w, rfl⟩`. Establish `hnn : 0 ≤ Q.nu 0 1 σ y (ε w)`. Unfold `Pair.nu`. Conclude with `mul_nonneg (norm_nonneg _) (Real.exp_pos _).le`. Establish `h2 : Q.nu 0 1 σ y (ε w) ^ 2 ≤ 1` using `by rw [hεnu]; exact hw σ y`.

Conclude with `(pow_le_one_iff_of_nonneg hnn two_ne_zero).1 h2`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg, hg0⟩ : ∃ g ∈ Q.Bl 0 1 1, g ≠ 0 := by`. Distinguish the cases in `h : ε s = 0`. Use `⟨ε 0, hsm 0 (HermLB.zero_mem_smallSec _), fun h0 => hs0 ?_⟩` and prove the remaining obligations. Conclude with `(hεinj (h0.trans h.symm)).symm`.

Conclude with `⟨ε s, hsm s hs, h⟩`. Establish `key : ∀ n : ℕ, 0 < n → (D.factorial : ℝ) * ((Fintype.card J * n ^ D : ℕ) : ℝ) ≤ gdeg ((P.L.pow n).tens A) D`. Introduce `n hn`. Establish `hrep : Q.Rep (n : ℤ) 1 ((Q.L.pow n).tens Q.A)`. Establish `h1` using `Pair.rep_pow k X p Q 1 0 Q.L n (Pair.rep_base k X p Q).1`.

Establish `h2` using `Pair.rep_tens k X p Q _ _ 0 1 _ _ h1 (Pair.rep_base k X p Q).2.1`. Simplify using `using h2`. Establish `hamp : IsAmpleLB ((P.L.pow n).tens A).B` using `GlobalTheory.T.isAmple_tensor_of_nef_fibres_ample k X p D hX (P.L.pow n) A (nefFib_of_isNef (GlobalTheory.NefPow.isNef_pow hAr k X p D hX P.L n hL)) hAamp`. Establish `hsp : ((P.L.pow n).tens A).SemiPos D` using `(hL.semiPos.pow n).tens hAnef.semiPos`. Establish `hvec : ∀ m : ℕ, 0 < m → ∃ v : Fin ((Fintype.card J * n ^ D) * m ^ D) → X.functionField, LinearIndependent ℤ v ∧ ∀ i, v i ∈ Q.Bl (m * (n : ℤ)) (m * 1) (Real.exp ((t₀ * n) * m))`.

Introduce `m hm`. Take `⟨v0, hv0, hv0s⟩` from `GlobalTheory.T.exists_linearIndependent_products_function_field X.functionField D x htb J e he (n * m) (Nat.mul_pos hn hm)`. Establish `hcard : Fintype.card J * (n * m) ^ D = (Fintype.card J * n ^ D) * m ^ D` using `by rw [mul_pow]; ring`. Establish `hgm : g ^ m ∈ Q.H ((m : ℤ) * 0) ((m : ℤ) * 1)` using `(NuPow.pow_mem_H_and_nu_pow k X p Q 0 1 g hg.1 m).1`. Establish `hgm0 : g ^ m ≠ 0` using `pow_ne_zero _ hg0`.

Use `⟨fun i => v0 (Fin.cast hcard.symm i) * g ^ m, ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `hli` using `hv0.map' (LinearMap.mulRight ℤ (g ^ m)) (LinearMap.ker_eq_bot.2 (mul_left_injective₀ hgm0))`. Conclude with `hli.comp _ (Fin.cast_injective _)`. Take `⟨w, a, ha, hw⟩` from `hv0s (Fin.cast hcard.symm i)`. Establish `hprod` using `GlobalTheory.T.boxMonomialFamily_prod_mem_normBall_of_exponent_lt k X p Q D J e x 1 0 (Real.exp t₀) (Real.exp_pos _).le hBl (n * m) w a ha`.

Rewrite `hprod` using `[← hw]`. Take `⟨hmem, hnu⟩` from `NuMul.mul_mem_H_and_nu_mul k X p Q _ _ _ _ _ _ hprod.1 hgm`. Establish `e1 : (((n * m : ℕ) : ℤ) * 1 + (m : ℤ) * 0) = (m : ℤ) * n` using `by push_cast; ring`. Establish `e2 : (((n * m : ℕ) : ℤ) * 0 + (m : ℤ) * 1) = (m : ℤ) * 1` using `by push_cast; ring`. Rewrite `hmem`, `hnu` using `[e1, e2]`.

Use `⟨hmem, fun σ y => ?_⟩` and prove the remaining obligations. Rewrite using `[hnu, (NuPow.pow_mem_H_and_nu_pow k X p Q 0 1 g hg.1 m).2 σ y]`. Establish `hA1` using `hprod.2 σ y`. Establish `hB1 : Q.nu 0 1 σ y g ^ m ≤ 1`. Establish `hnn : 0 ≤ Q.nu 0 1 σ y g`.

Unfold `Pair.nu`. Conclude with `mul_nonneg (norm_nonneg _) (Real.exp_pos _).le`. Conclude with `pow_le_one₀ hnn (hg.2 σ y)`. Establish `hnn' : 0 ≤ Q.nu ((n * m : ℕ) * 1) ((n * m : ℕ) * 0) σ y (v0 (Fin.cast hcard.symm i))`. Unfold `Pair.nu`.

Conclude with `mul_nonneg (norm_nonneg _) (Real.exp_pos _).le`. Establish `hexp : Real.exp t₀ ^ (n * m) = Real.exp ((t₀ * n) * m)`. Rewrite using `[← Real.exp_nat_mul]`. Use `push_cast`. Put the polynomial expressions in normal form.

Combine the equalities or inequalities in the displayed calculation. Use `GlobalTheory.T.factorial_mul_rank_le_degree_of_indep_small_sections hAr hHS k X p D hX Q n 1 _ hrep hamp hsp (Fintype.card J * n ^ D) (t₀ * n) hvec` as an intermediate fact. Conclude with `this`. Establish `hlim` using `GlobalTheory.T.tendsto_hermLineBundleGeometricDegree_pow_tens_div_pow hAr k X p D hX P.L A`. Use `ge_of_tendsto hlim ?_` and prove the remaining obligations.

Use `filter_upwards [eventually_gt_atTop 0] with n hn`. Establish `hnD : (0 : ℝ) < (n : ℝ) ^ D` using `by positivity`. Rewrite using `[le_div_iff₀ hnD]`. Use `key n hn` as an intermediate fact. Move the coercions through the operations in `at this`.

Use polynomial arithmetic with `[this]`.
-/
theorem rank_le_gdeg_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), P.L.IsNef D → ∀ (J : Type) [Fintype J] (e : J → X.functionField) (x : Fin D → X.functionField), LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, boxFam e x c ∈ P.H 1 0) → (D.factorial : ℝ) * Fintype.card J ≤ gdeg P.L D := by
  intro hAr hHS k _ X _ p D hX P hL J _ e x he hx hbox
  have hcz : CharZero X.functionField := by
    have := hX.charZero
    exact ((X.germToFunctionField ⊤).hom.charZero_iff (X.germToFunctionField_injective ⊤)).1 this
  have htb : IsTranscendenceBasis ℤ x := (GlobalTheory.T.isTranscendenceBasis_functionField_arithmeticVariety k X p D hX).2 x hx
  obtain ⟨A, hAamp, hAnef, s, hs, hs0⟩ := GlobalTheory.AmpleNefSmall.exists_ample_nef_smallSec hAr k X p D hX
  obtain ⟨r', hr'⟩ := exists_isRatSec A.isLB
  let Q : Pair p := ⟨P.L, A, P.r, r', P.hr, hr'⟩
  have hQbox : ∀ c, boxFam e x c ∈ Q.H 1 0 := by
    intro c z i j hi _
    obtain ⟨j', hj'⟩ : ∃ j', z ∈ P.A.B.U j' := by
      have h1 : z ∈ (⨆ j, P.A.B.U j) := by rw [P.A.isLB.cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 h1
    have h2 := hbox c z i j' hi hj'
    simpa [Pair.loc, Q] using h2
  have hbd : ∀ c, ∃ u : ℝ, 0 ≤ u ∧ boxFam e x c ∈ Q.Bl 1 0 (Real.exp u) :=
    fun c => GlobalTheory.T.pairSection_mem_ball_exp_of_projArithVariety k X p D hX Q 1 0 _ (hQbox c)
  choose u hu0 hu using hbd
  set t₀ : ℝ := ∑ c, u c with ht₀
  have ht₀0 : 0 ≤ t₀ := Finset.sum_nonneg fun c _ => hu0 c
  have hBl : ∀ c, boxFam e x c ∈ Q.Bl 1 0 (Real.exp t₀) := fun c =>
    ⟨(hu c).1, fun σ y => ((hu c).2 σ y).trans
      (Real.exp_le_exp.2 (Finset.single_le_sum (fun c _ => hu0 c) (Finset.mem_univ c)))⟩
  obtain ⟨ε, hεinj, hεrange, hεnu, -⟩ := RepDict.rep_dict k X p Q 0 1 Q.A (Pair.rep_base k X p Q).2.1
  have hsm : ∀ w ∈ A.smallSec, ε w ∈ Q.Bl 0 1 1 := by
    intro w hw
    refine ⟨?_, fun σ y => ?_⟩
    · rw [← SetLike.mem_coe, ← hεrange]; exact ⟨w, rfl⟩
    · have hnn : 0 ≤ Q.nu 0 1 σ y (ε w) := by
        unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
      have h2 : Q.nu 0 1 σ y (ε w) ^ 2 ≤ 1 := by rw [hεnu]; exact hw σ y
      exact (pow_le_one_iff_of_nonneg hnn two_ne_zero).1 h2
  obtain ⟨g, hg, hg0⟩ : ∃ g ∈ Q.Bl 0 1 1, g ≠ 0 := by
    by_cases h : ε s = 0
    · refine ⟨ε 0, hsm 0 (HermLB.zero_mem_smallSec _), fun h0 => hs0 ?_⟩
      exact (hεinj (h0.trans h.symm)).symm
    · exact ⟨ε s, hsm s hs, h⟩
  have key : ∀ n : ℕ, 0 < n →
      (D.factorial : ℝ) * ((Fintype.card J * n ^ D : ℕ) : ℝ) ≤ gdeg ((P.L.pow n).tens A) D := by
    intro n hn
    have hrep : Q.Rep (n : ℤ) 1 ((Q.L.pow n).tens Q.A) := by
      have h1 := Pair.rep_pow k X p Q 1 0 Q.L n (Pair.rep_base k X p Q).1
      have h2 := Pair.rep_tens k X p Q _ _ 0 1 _ _ h1 (Pair.rep_base k X p Q).2.1
      simpa using h2
    have hamp : IsAmpleLB ((P.L.pow n).tens A).B :=
      GlobalTheory.T.isAmple_tensor_of_nef_fibres_ample k X p D hX (P.L.pow n) A
        (nefFib_of_isNef (GlobalTheory.NefPow.isNef_pow hAr k X p D hX P.L n hL)) hAamp
    have hsp : ((P.L.pow n).tens A).SemiPos D := (hL.semiPos.pow n).tens hAnef.semiPos
    have hvec : ∀ m : ℕ, 0 < m → ∃ v : Fin ((Fintype.card J * n ^ D) * m ^ D) → X.functionField,
        LinearIndependent ℤ v ∧ ∀ i, v i ∈ Q.Bl (m * (n : ℤ)) (m * 1) (Real.exp ((t₀ * n) * m)) := by
      intro m hm
      obtain ⟨v0, hv0, hv0s⟩ := GlobalTheory.T.exists_linearIndependent_products_function_field X.functionField D x htb J e he (n * m) (Nat.mul_pos hn hm)
      have hcard : Fintype.card J * (n * m) ^ D = (Fintype.card J * n ^ D) * m ^ D := by rw [mul_pow]; ring
      have hgm : g ^ m ∈ Q.H ((m : ℤ) * 0) ((m : ℤ) * 1) :=
        (NuPow.pow_mem_H_and_nu_pow k X p Q 0 1 g hg.1 m).1
      have hgm0 : g ^ m ≠ 0 := pow_ne_zero _ hg0
      refine ⟨fun i => v0 (Fin.cast hcard.symm i) * g ^ m, ?_, fun i => ?_⟩
      · have hli := hv0.map' (LinearMap.mulRight ℤ (g ^ m))
          (LinearMap.ker_eq_bot.2 (mul_left_injective₀ hgm0))
        exact hli.comp _ (Fin.cast_injective _)
      · obtain ⟨w, a, ha, hw⟩ := hv0s (Fin.cast hcard.symm i)
        have hprod := GlobalTheory.T.boxMonomialFamily_prod_mem_normBall_of_exponent_lt k X p Q D J e x 1 0 (Real.exp t₀) (Real.exp_pos _).le hBl (n * m) w a ha
        rw [← hw] at hprod
        obtain ⟨hmem, hnu⟩ := NuMul.mul_mem_H_and_nu_mul k X p Q _ _ _ _ _ _ hprod.1 hgm
        have e1 : (((n * m : ℕ) : ℤ) * 1 + (m : ℤ) * 0) = (m : ℤ) * n := by push_cast; ring
        have e2 : (((n * m : ℕ) : ℤ) * 0 + (m : ℤ) * 1) = (m : ℤ) * 1 := by push_cast; ring
        rw [e1, e2] at hmem hnu
        refine ⟨hmem, fun σ y => ?_⟩
        rw [hnu, (NuPow.pow_mem_H_and_nu_pow k X p Q 0 1 g hg.1 m).2 σ y]
        have hA1 := hprod.2 σ y
        have hB1 : Q.nu 0 1 σ y g ^ m ≤ 1 := by
          have hnn : 0 ≤ Q.nu 0 1 σ y g := by
            unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
          exact pow_le_one₀ hnn (hg.2 σ y)
        have hnn' : 0 ≤ Q.nu ((n * m : ℕ) * 1) ((n * m : ℕ) * 0) σ y (v0 (Fin.cast hcard.symm i)) := by
          unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
        have hexp : Real.exp t₀ ^ (n * m) = Real.exp ((t₀ * n) * m) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
        calc _ ≤ Real.exp t₀ ^ (n * m) * 1 := mul_le_mul hA1 hB1 (pow_nonneg (by unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) _) (pow_nonneg (Real.exp_pos _).le _)
          _ = _ := by rw [mul_one, hexp]
    have := GlobalTheory.T.factorial_mul_rank_le_degree_of_indep_small_sections hAr hHS k X p D hX Q n 1 _ hrep hamp hsp (Fintype.card J * n ^ D) (t₀ * n) hvec
    exact this
  have hlim := GlobalTheory.T.tendsto_hermLineBundleGeometricDegree_pow_tens_div_pow hAr k X p D hX P.L A
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnD : (0 : ℝ) < (n : ℝ) ^ D := by positivity
  rw [le_div_iff₀ hnD]
  have := key n hn
  push_cast at this
  nlinarith [this]

end GlobalTheory.HSNef.RankNef
