import Formalism.SizeWindowBrackets.SBrDiv
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
import Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize

open Module NumberField IsDedekindDomain
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LBrDiv

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2

/- English proof (authored)
The placewise identity says every embedding average equals the stored period, so that period satisfies the mean condition. If the same averages equal another proposed period, choose any place using nonemptiness. Its two equalities identify the proposed period with the stored one.
-/
theorem periodicity_of_text : PerOfText := by
  intro U0 W Top m f D Pl Emb _ hne logOmτ logOm hT
  refine ⟨fun hM => ?_, fun ρ => hT ρ⟩
  obtain ⟨ρ⟩ := hne
  exact (hM ρ).symm.trans (hT ρ)

/- English proof (authored)
The divisibility bound is the free-parameter bound evaluated at the period stored in the data. Thus both sides express the same inequality.
-/
theorem divisibility_iff_free : DivIffFree := by
  intro U0 W Top _ m f D C
  exact Iff.rfl

/- English proof (authored)
The period condition equates the free logarithmic period with the stored period. Substitute this equality into the free-parameter divisibility bound.
-/
theorem divisibility_of_free : DivOfFree := by
  intro U0 W Top _ m f D C logOm h hp
  have e : logOm = D.logOm := hp
  subst e
  exact h

/- English proof (authored)
Subtract the principal sums at the two logarithmic periods. All terms independent of the period cancel. The remaining difference at each place is its weight times m times the difference of the periods. Factor out the common scalars and sum the weights.
-/
theorem divisibility_principal_shift : DivMainShift := by
  intro Top _ m aT logT Om Om'
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

/- English proof (authored)
Use the principal-sum shift identity at each word. It replaces the original logarithmic period in the main sum by the new one and adds m times the total weight times the difference of the logarithmic periods. The other terms of the divisibility bound are identical, so substitution gives the equivalence.
-/
theorem divisibility_free_shift : DivFreeShift := by
  intro U0 W Top _ m f D C logOm logOm'
  have key : ∀ u0 (u : W u0),
      (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * logOm) - D.aT t * Real.log (D.T u0 u)))
        = (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * logOm') - D.aT t * Real.log (D.T u0 u)))
          + (m : ℝ) * D.sumA * (logOm' - logOm) := by
    intro u0 u
    have := divisibility_principal_shift Top (m : ℝ) D.aT (Real.log (D.T u0 u)) logOm' logOm
    rw [this]
    unfold Data.sumA
    ring
  constructor
  · intro h u0 u
    have := h u0 u
    rw [key u0 u] at this
    linarith
  · intro h u0 u
    have := h u0 u
    rw [key u0 u]
    linarith

/- English proof (authored)
Shift the free bound to the stored period. The total weight is nonnegative, and the stored period is at most the free period. Therefore the added correction is nonpositive. Dropping it gives the required bound.
-/
theorem divisibility_of_free_le : DivOfFreeLe := by
  intro U0 W Top _ m f D C logOm ha h hp
  have h2 := (divisibility_free_shift U0 W Top m f D C logOm D.logOm).mp h
  intro u0 u
  have h3 := h2 u0 u
  have hs : 0 ≤ D.sumA := Finset.sum_nonneg fun t _ => ha t
  have hle : D.logOm - logOm ≤ 0 := by
    have : D.logOm ≤ logOm := hp
    linarith
  have hm : 0 ≤ (m : ℝ) * D.sumA := mul_nonneg (Nat.cast_nonneg m) hs
  have : (m : ℝ) * D.sumA * (D.logOm - logOm) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm hle
  linarith

/- English proof (authored)
Express the logarithmic period as the sum of the gamma term and log(π/v), minus the remaining scale term. The triangle inequality bounds its absolute value by the sum of the three separate limits, which is at most the allowed size.
-/
theorem omega_size_of_periodicity : OmSizeOfPer := by
  intro U0 W Top m f D logOm A B hp hg hA hB hL
  have hp' : logOm = D.gam + Real.log (Real.pi / D.v) - D.LpL := hp
  rw [hp']
  have h1 := abs_le.mp hg
  have h2 := abs_le.mp hA
  have h3 := abs_le.mp hB
  exact abs_le.mpr ⟨by linarith [h1.1, h2.1, h3.2], by linarith [h1.2, h2.2, h3.1]⟩

/- English proof (authored)
Use positivity of v and π to expand log(π/v) as log(π) minus log(v). Solve the period equation for log(v) and exponentiate to obtain the formula. Conversely take the logarithm of that positive formula and rearrange to recover the period equation.
-/
theorem periodicity_iff_v : PerIffV := by
  intro U0 W Top m f D logOm hv
  unfold Per
  rw [Real.log_div Real.pi_pos.ne' hv.ne']
  constructor
  · intro h
    have h1 : Real.log D.v = Real.log Real.pi + (D.gam - D.LpL - logOm) := by linarith
    calc D.v = Real.exp (Real.log D.v) := (Real.exp_log hv).symm
      _ = Real.pi * Real.exp (D.gam - D.LpL - logOm) := by
        rw [h1, Real.exp_add, Real.exp_log Real.pi_pos]
  · intro h
    have h1 : Real.log D.v = Real.log Real.pi + (D.gam - D.LpL - logOm) := by
      rw [h, Real.log_mul Real.pi_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
    linarith

/- English proof (authored)
Choose v equal to π times exp(γ − LₚL − log Ω). Both factors are positive. Taking logarithms in the period expression and substituting this v makes all terms except log Ω cancel.
-/
theorem periodicity_solvable : PerSolvable := by
  intro gam LpL logOm
  refine ⟨Real.pi * Real.exp (gam - LpL - logOm), mul_pos Real.pi_pos (Real.exp_pos _), ?_⟩
  rw [Real.log_div Real.pi_pos.ne' (mul_pos Real.pi_pos (Real.exp_pos _)).ne',
    Real.log_mul Real.pi_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/- English proof (authored)
Expand each log(wv/π) using the positive factors. The period equation identifies log(v) minus log(π) with γ − LₚL − log Ω. Substituting this into every term gives exactly the count condition with the scale v eliminated.
-/
theorem free_count_of_count : CountFreeOfCount := by
  intro U0 W Top _ m f D C logOm hv hw hp
  have e : ∀ u0 j ρ, Real.log (D.w u0 j ρ * D.v / Real.pi)
      = Real.log (D.w u0 j ρ) + (D.gam - D.LpL - logOm) := by
    intro u0 j ρ
    have hp' : logOm = D.gam + Real.log (Real.pi / D.v) - D.LpL := hp
    rw [Real.log_div Real.pi_pos.ne' hv.ne'] at hp'
    rw [Real.log_div (mul_pos (hw u0 j ρ) hv).ne' Real.pi_pos.ne',
      Real.log_mul (hw u0 j ρ).ne' hv.ne']
    linarith
  unfold CountFree
  simp only [e]

/- English proof (authored)
Given a positive scale v satisfying the divisibility and count conditions, take its stored logarithmic period. Use the count identity to write the first count bound in terms of the period, and carry over the upper and variation bounds. Conversely, given a period with the three bounds, choose the positive v that solves the period equation. The divisibility and count identities recover the corresponding conditions for this v.
-/
theorem v_elimination : VElim := by
  intro U0 W Top _ m f D C hw
  constructor
  · rintro ⟨v, hv, hD, hC⟩
    refine ⟨(withV D v).logOm, fun u0 u => hD u0 u, ?_, fun u0 u => ⟨(hC u0 u).2.1, (hC u0 u).2.2⟩⟩
    have h := (free_count_of_count U0 W Top m f (withV D v) C (withV D v).logOm hv hw rfl).mpr
      (fun u0 u => (hC u0 u).1)
    exact h
  · rintro ⟨logOm, h1, h2, h3⟩
    obtain ⟨v, hv, hp⟩ := periodicity_solvable D.gam D.LpL logOm
    refine ⟨v, hv, divisibility_of_free U0 W Top m f (withV D v) C logOm h1 hp, ?_⟩
    intro u0 u
    exact ⟨(free_count_of_count U0 W Top m f (withV D v) C logOm hv hw hp).mp h2 u0 u,
      (h3 u0 u).1, (h3 u0 u).2⟩

/- English proof (authored)
Both instances of the principal weight function are the same defining expression, so their values at the given input agree.
-/
lemma ph_eq (y : ℝ) : Formalism.LatticeIndexTer.ph y = ph y := rfl

/- English proof (authored)
Reindex the theorem's principal sum along the given embedding of top indices and replace each weight by its data value. The embedding preserves cardinality. Substitute the equality for the positive correction term. Both factors that multiply the theorem's error constant are nonnegative under the size hypotheses, so increasing that constant to the data bound preserves the inequality.
-/
theorem divisibility_of_conclusion : DivOfConcl := by
  intro U0 W Top _ m f D C logOm C0 Pl e aP FoP haP hFo hC ha hLa hB hx h u0 u
  have h1 := h u0 u
  unfold ThmConcl at h1
  rw [Finset.sum_map, Finset.card_map, Finset.card_univ] at h1
  simp only [haP, ph_eq] at h1
  rw [hFo u0]
  have hX : 0 ≤ (Fintype.card Top : ℝ) * D.a * D.La :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ha) hLa
  have hY : 0 ≤ (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) (Real.rpow_nonneg hx _)
  have h2 := mul_le_mul_of_nonneg_right hC (add_nonneg hX hY)
  have e1 : C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε)
      = C.cDiv * ((Fintype.card Top : ℝ) * D.a * D.La + (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε)) := by
    unfold Data.nT
    ring
  linarith

/- English proof (authored)
The model parameters give nonnegativity of the main size, the logarithmic size, and the sum of the auxiliary sizes. At each word the step conditions and the parameter conditions are exactly the inputs of the divisibility theorem, with its positive correction equal to half the data correction. Apply it to that word and then use the conclusion-to-divisibility estimate to transfer the bound.
-/
theorem divisibility_of_theorem : DivOfThm := by
  intro T U0 W Top _ m f D C P logOm Pl _ e _ aP St haP hFo hC hP hS
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21,
    p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33⟩ := hP
  have hb : 0 < D.b := by rw [p4]; exact Real.exp_pos _
  have hx0 : 0 ≤ D.x := by linarith
  have ha : 0 ≤ D.a := by rw [p5]; exact mul_nonneg hx0 hb.le
  have hLa : 0 ≤ D.La := le_trans (abs_nonneg _) p22
  have hB0 : 0 ≤ D.B0 := by
    rw [p10]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hb.le) (Real.rpow_nonneg hx0 _)
  refine divisibility_of_conclusion U0 W Top m f D C logOm P.C0 Pl e aP (fun u0 => D.Fo u0 / 2) haP
    (fun u0 => by ring) hC.ge ha hLa (by linarith) hx0 ?_
  intro u0 u
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17⟩ := hS u0 u
  have hF : D.Fo u0 / 2 = (St u0 u).FoP := by rw [hFo u0 u]; ring
  rw [hF]
  exact T (Fin m) Pl (Finset.univ.map e) (D.muCC u0) (St u0 u).mu0 (St u0 u).FoP (D.h u0 u) (St u0 u).hP
    (St u0 u).mlam (Real.log (D.T u0 u)) (St u0 u).hK aP (St u0 u).phν (St u0 u).nν (St u0 u).fa
    D.x D.ε D.L D.b D.a P.rd D.La D.B0 D.Nc (D.x ^ (C.eDiv * D.ε)) (m : ℝ) P.f D.k P.N P.S P.tt P.η P.w'' D.b'
    P.dC P.lam0 P.C0 (St u0 u).Lpass (St u0 u).Eb (St u0 u).e6 (St u0 u).eP logOm (St u0 u).eK (St u0 u).pq
    (St u0 u).w (St u0 u).eE (St u0 u).δ
    s1 s2 s3 s4 s5 s6 s7 s8 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 (by simp) p13 p14 p15 p16 p17 p18 p19 p20 p21
    s9 s10 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 s11 s12 s13 s14 s15 s16 s17

/- English proof (authored)
Since the divisor exponent is at least one and ε is positive, its product with ε is at least ε. For a base x ≥ 1, the real power increases with the exponent.
-/
theorem exponent_of_divisibility : XeOfEDiv := by
  intro x ε eDiv hx hε he
  exact Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)

/- English proof (authored)
Taking the logarithm of the defining exponential gives L equal to x to the power ε. The formulas for b, a and the main auxiliary size then follow by substitution. The ambient group has four times the cardinality of H, and the selected half has half of that size. The quotient defining the remaining auxiliary size is nonnegative because every factor in its numerator and denominator is nonnegative. The number of top indices is the cardinality of the top set.
-/
theorem construct_parameter_definitions : MkParDefs := by
  intro H _ _ _ W _ m G cHH D ell N TT T2 a w Fm
  have hL : (mkData G cHH D ell N TT T2 a w Fm).L = G.x ^ G.ε := by
    show Real.log (bTx G.x G.ε) = _
    unfold bTx
    rw [Real.log_exp]
  refine ⟨hL, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · rw [hL]; rfl
  · have h1 : (Fintype.card (E0 × H) : ℂ) = 2 * ((PhiSet (H := H)).card : ℂ) := Formalism.D5.Bal.card_G_eq
    have h2 : Fintype.card (E0 × H) = 2 * (PhiSet (H := H)).card := by exact_mod_cast h1
    have h3 : Fintype.card (E0 × H) = 4 * Fintype.card H := by
      simp [Fintype.card_prod]
    have h4 : (PhiSet (H := H)).card = 2 * Fintype.card H := by omega
    exact_mod_cast h4
  · intro hx hk
    show 0 ≤ (T2.card : ℝ) * G.k * bTx G.x G.ε * G.x ^ G.ε
      / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * G.x ^ (-G.ε)))
    have hb : 0 ≤ bTx G.x G.ε := (Real.exp_pos _).le
    exact div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hk) hb) (Real.rpow_nonneg hx _))
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hx _)))
  · show (Fintype.card TT : ℝ) = _
    rw [Fintype.card_coe]

/- English proof (authored)
Reindex the weights on the image of the top set to recover the total weight in the data. Use the assumed identifications of the local exponent contributions at each index. Summing those equalities gives the full exponent, with the factor of two from its definition. Then enlarge the error constant in both the local and total deviation bounds. The multiplying factors are nonnegative, so the inequalities are preserved.
-/
theorem exponent_comparison_of_constant : TypePrimeCostOfDeviationBound := by
  intro U0 W Top _ m f D C C0 Pl e aP sE haP hE hC hB h
  have hsum : (∑ t ∈ Finset.univ.map e, aP t) = D.sumA := by
    rw [Finset.sum_map]
    simp only [haP]
    rfl
  constructor
  · intro u0 u j
    have h1 := (h u0 u).1 j
    rw [hsum] at h1
    rw [hE u0 u j]
    exact h1.trans (mul_le_mul_of_nonneg_right hC hB)
  · intro u0 u
    have h1 := (h u0 u).2
    rw [hsum] at h1
    have e1 : D.Ee u0 u = 2 * ∑ j, sE u0 u j := by
      unfold Data.Ee
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => hE u0 u j
    rw [e1]
    have e2 : (m : ℝ) * D.sumA * D.lg = (m : ℝ) * (D.sumA * D.lg) := by ring
    rw [e2]
    have hmB : 0 ≤ (m : ℝ) * D.B0 := mul_nonneg (Nat.cast_nonneg _) hB
    calc _ ≤ (9 * C0 ^ 2 + 6 * C0 + 20) * ((m : ℝ) * D.B0) := h1
      _ ≤ C.cE * ((m : ℝ) * D.B0) := mul_le_mul_of_nonneg_right hC hmB
      _ = C.cE * (m : ℝ) * D.B0 := by ring

/- English proof (authored)
Reindex the two weighted count sums and use the cardinality equality for the embedded top set. The normalized size factor in the deviation bound is nonnegative because its size parameters and cardinalities are nonnegative. Replace the original error constant by the assumed larger one.
-/
theorem height_comparison_of_constant : HeightVariationOfCorrectedHeightBound := by
  intro U0 W Top _ m f D C C0 Pl e aP haP hC ha hLa hB h u0 u u'
  have h1 := h u0 u u'
  rw [Finset.sum_map, Finset.sum_map, Finset.card_map, Finset.card_univ] at h1
  simp only [haP] at h1
  have hX : 0 ≤ (Fintype.card Top : ℝ) * D.a * D.La + (m : ℝ) * D.B0 :=
    add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ha) hLa) (mul_nonneg (Nat.cast_nonneg _) hB)
  exact h1.trans (mul_le_mul_of_nonneg_right hC hX)

/- English proof (authored)
The duality relation identifies the row maximal slope with minus the ambient minimal slope. Thus the assumed bound on the row maximal slope plus the mean gives the required height lower comparison. The positivity and upper size comparisons are already part of the function bound.
-/
theorem height_bound_of_function : HHOfFun := by
  intro U0 W _ Top m f D C muMaxRR hF hD u0
  obtain ⟨h1, h2, h3⟩ := hF u0
  have h4 := hD u0
  exact ⟨by linarith, h2, h3⟩

/- English proof (authored)
Add the two bounds at a fixed unit. The shift c cancels, leaving the row maximal slope plus the mean bounded by (p₁ + p₂)b. Since b is positive, the sum bound on p₁ and p₂ makes this at most the prescribed height. That height is positive because x and b are positive, and it equals its asserted upper bound.
-/
theorem function_of_parts : FunOfParts := by
  intro U0 W _ Top m f D C muMaxRR c p1 p2 hx hb h1 h2 hp hH u0
  rw [hH u0]
  refine ⟨?_, mul_pos (Real.rpow_pos_of_pos hx _) hb, le_rfl⟩
  have := mul_le_mul_of_nonneg_right hp hb.le
  have a1 := h1 u0
  have a2 := h2 u0
  nlinarith

/- English proof (authored)
At each unit, the shift subtracts c from each height and adds c to the ambient slopes. Since the positive weights have a positive sum, adding the same c inside the mean adds exactly c to the mean. In the divisibility bounds the ambient shift cancels the height shift. In the height variation the common shift cancels between the two words. In the height comparison the shifted mean and shifted minimal slope both gain c, so their difference remains the same. These identities give all the stated equivalences.
-/
theorem scale_free : ScaleFree := by
  intro U0 W _ Top _ m f D C c logOm hd hne
  have hs : ∀ u0, (shiftRows D c).s u0 = D.s u0 + c u0 := by
    intro u0
    have := hne u0
    have hpos : 0 < ∑ u, D.d u0 u := Finset.sum_pos (fun u _ => hd u0 u) Finset.univ_nonempty
    show wmean (D.d u0) (fun u => D.muN u0 u - (D.h u0 u - c u0))
      = wmean (D.d u0) (fun u => D.muN u0 u - D.h u0 u) + c u0
    unfold wmean
    rw [eq_comm, div_add' _ _ _ hpos.ne']
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  have e1 : ∀ u0 (u : W u0), (D.muCC u0 + c u0) + (D.h u0 u - c u0) - D.Fo u0
      = D.muCC u0 + D.h u0 u - D.Fo u0 := fun u0 u => by ring
  refine ⟨?_, ?_, ?_, ?_, hs⟩
  · constructor
    · intro h u0 u
      have := h u0 u
      rw [← e1 u0 u]
      exact this
    · intro h u0 u
      have := h u0 u
      rw [← e1 u0 u] at this
      exact this
  · constructor
    · intro h u0 u
      have := h u0 u
      rw [← e1 u0 u]
      exact this
    · intro h u0 u
      have := h u0 u
      rw [← e1 u0 u] at this
      exact this
  · have e2 : ∀ u0 (u u' : W u0),
        ((D.h u0 u - c u0) + ∑ t, D.aT t * Real.log (D.T u0 u))
          - ((D.h u0 u' - c u0) + ∑ t, D.aT t * Real.log (D.T u0 u'))
        = (D.h u0 u + ∑ t, D.aT t * Real.log (D.T u0 u))
          - (D.h u0 u' + ∑ t, D.aT t * Real.log (D.T u0 u')) := fun u0 u u' => by ring
    constructor
    · intro h u0 u u'
      have := h u0 u u'
      rw [← e2 u0 u u']
      exact this
    · intro h u0 u u'
      have := h u0 u u'
      rw [← e2 u0 u u'] at this
      exact this
  · have e3 : ∀ u0, (shiftRows D c).s u0 - (D.muMinCC u0 + c u0) = D.s u0 - D.muMinCC u0 := by
      intro u0
      rw [hs u0]
      ring
    constructor
    · intro h u0
      have := h u0
      rw [← e3 u0]
      exact this
    · intro h u0
      have := h u0
      rw [← e3 u0] at this
      exact this

/- English proof (authored)
If the integral lattice were zero, its field span would be zero. Since this span is the entire space, every basis vector would be zero. A basis vector exists by nonemptiness and is nonzero, a contradiction.
-/
lemma ne_bot_of_span {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [Nonempty ι]
    (b : Basis ι K V) (A : Submodule (𝓞 K) V) (hsp : Submodule.span K (A : Set V) = ⊤) : A ≠ ⊥ := by
  rintro rfl
  have h0 : Submodule.span K (((⊥ : Submodule (𝓞 K) V) : Set V)) = ⊥ := by simp
  rw [h0] at hsp
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have : b i ∈ (⊥ : Submodule K V) := by rw [hsp]; trivial
  exact b.ne_zero i (by simpa using this)

/- English proof (authored)
The dual polygon identity gives the dual lattice's full span, finite generation, and the inverse relation for its size and extreme polygon quantities. Both lattices are nonzero because they span and the basis is nonempty. The slope characterization expresses the mean through the logarithm of the size, so inversion negates the mean. For the extremes, substitute the corresponding exponential slope formulas into the inverse relations. Injectivity of the real exponential and the normalizing discriminant terms give the dual minimal slope as minus the original maximal slope, and the dual maximal slope as minus the original minimal slope.
-/
theorem dual_slopes : DualSlopes := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ _ b X hX A hA hsp
  obtain ⟨dfg, dsp, _, dsize, dleast, dlargest, _⟩ := dual_polygon_identity K V ι b X hX A hA hsp
  have hX' := Formalism.HN.DualPolygon.dualFrame_unit X hX
  have hA0 : A ≠ ⊥ := ne_bot_of_span b A hsp
  have hD0 : dualLat A ≠ ⊥ := ne_bot_of_span b.dualBasis (dualLat A) dsp
  obtain ⟨_, a2, _, a4, a5, _⟩ := size_maximal_slope K V ι b X hX A hA hA0
  obtain ⟨_, d2, _, d4, d5, _⟩ :=
    size_maximal_slope K (Module.Dual K V) ι b.dualBasis (dualFrame X) hX' (dualLat A) dfg hD0
  refine ⟨?_, ?_, ?_⟩
  · rw [d2, a2, dsize, Real.log_inv]
    ring
  · rw [d5, a4, ← Real.exp_neg] at dlargest
    have h := Real.exp_injective dlargest
    unfold muMinDef muMaxDef
    have e : logDisc K / (2 * (Module.finrank ℚ K : ℝ)) = logDisc K / (Module.finrank ℚ K : ℝ) / 2 := by ring
    rw [e] at h
    linarith
  · rw [d4, a5, ← Real.exp_neg] at dleast
    have h := Real.exp_injective dleast
    unfold muMinDef muMaxDef
    have e : logDisc K / (2 * (Module.finrank ℚ K : ℝ)) = logDisc K / (Module.finrank ℚ K : ℝ) / 2 := by ring
    rw [e] at h
    linarith

/- English proof (authored)
Full span makes the field rank of the lattice equal to D, which is positive. The height is positive. Substitute the definition of the normalized covolume into the size-and-slope identity, then take the logarithm of its height power. Using that the field degree is twice the number of infinite places, simplify to minus the logarithmic covolume divided by D.
-/
theorem mu_log_conductor : MuLcv := by
  intro K _ _ _ _ D hD X hX R hR
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  have hR0 : R ≠ ⊥ := ne_bot_of_span (Pi.basisFun K (Fin D)) R hR.span_eq_top
  obtain ⟨_, a2, _⟩ := size_maximal_slope K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) X hX R hR.fg hR0
  have hpos : 0 < ht (Pi.basisFun K (Fin D)) X R :=
    (place_lattice_structure K _ (Fin D) (Pi.basisFun K (Fin D)) X hX R hR.fg).2.2
  have hrk : rkK R = D := by
    unfold rkK
    rw [hR.span_eq_top, finrank_top]
    simp
  have hn : (Module.finrank ℚ K : ℝ) = 2 * (nPl K : ℝ) := by
    have := sizeMu_finrank_eq K
    exact_mod_cast this
  rw [a2]
  unfold size lcv
  rw [Real.log_rpow hpos, hrk, hn]
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hnp : (nPl K : ℝ) ≠ 0 := by
    have h1 : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
    intro h0
    rw [hn, h0] at h1
    simp at h1
  field_simp

/- English proof (authored)
The given injective map preserves the norms and realizes the target lattice as the image of the row dual lattice. Therefore its mean and minimal slopes agree with those of the dual. The dual-slope formulas express them as minus the original row mean and minus the row maximal slope. The formula for the row mean then gives the covolume divided by D for the first assertion.
-/
theorem mu_constant_of_blocks : MuCCOfRows := by
  intro I m F D hD XE hXE hX' R hR ψ hψ
  obtain ⟨hinj, hnorm, hcc⟩ := hψ
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  obtain ⟨dfg, _⟩ := dual_polygon_identity F.K (Fin D → F.K) (Fin D) (Pi.basisFun F.K (Fin D)) XE hXE R hR.fg
    hR.span_eq_top
  obtain ⟨_, _, r3, _, r5, _⟩ := lattice_rerealization F.K (Module.Dual F.K (Fin D → F.K)) (Fin D) F.Wd F.κ
    (Pi.basisFun F.K (Fin D)).dualBasis (dualFrame XE) F.b' F.X' ψ (Formalism.HN.DualPolygon.dualFrame_unit XE hXE) hX' hinj hnorm
    (dualLat R) dfg
  obtain ⟨s1, s2, _⟩ := dual_slopes F.K (Fin D → F.K) (Fin D) (Pi.basisFun F.K (Fin D)) XE hXE R hR.fg
    hR.span_eq_top
  have m1 := mu_log_conductor F.K D hD XE hXE R hR
  constructor
  · rw [hcc]
    have : muDef F.b' F.X' ((dualLat R).map (ψ.restrictScalars (𝓞 F.K)))
        = muDef (Pi.basisFun F.K (Fin D)).dualBasis (dualFrame XE) (dualLat R) := by
      unfold muDef
      rw [r3]
    rw [this, s1, m1]
    ring
  · rw [hcc]
    have : muMinDef F.b' F.X' ((dualLat R).map (ψ.restrictScalars (𝓞 F.K)))
        = muMinDef (Pi.basisFun F.K (Fin D)).dualBasis (dualFrame XE) (dualLat R) := by
      unfold muMinDef
      rw [r5]
    rw [this, s2]

/- English proof (authored)
Two height-one primes with the same associated finite place have the same underlying ideal, hence are equal. Conversely the ideal of a finite place is maximal and prime. It is nonzero because the ring of integers is not a field. It therefore defines a height-one prime mapping to that place.
-/
lemma plOf_bijective (K : Type) [Field K] [NumberField K] :
    Function.Bijective (plOf : HeightOneSpectrum (𝓞 K) → slopeLatticeData.FinPl K) := by
  constructor
  · intro w w' h
    have : w.asIdeal = w'.asIdeal := congrArg Subtype.val h
    exact HeightOneSpectrum.ext this
  · intro p
    refine ⟨⟨p.1, p.2.isPrime, ?_⟩, rfl⟩
    exact Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField K)

/- English proof (authored)
The map from height-one primes to finite places is a bijection. Because the summand vanishes outside the inverse image of S, its support is finite. Reindex the sum by finite places, restrict it to S, and combine each logarithmic weight with its ramification factor to obtain the stated coefficient.
-/
theorem sum_over_places : SumOverPlaces := by
  intro K _ _ S φ
  have hb := plOf_bijective K
  constructor
  · refine (S.finite_toSet.preimage hb.1.injOn).subset ?_
    intro w hw
    by_contra hn
    apply hw
    have : plOf w ∉ S := hn
    simp [this]
  · set g : slopeLatticeData.FinPl K → ℝ := fun v => slopeLatticeData.ell v * (if v ∈ S then ramE v * φ v else 0) with hg
    have h1 : (∑ᶠ w : HeightOneSpectrum (𝓞 K),
        lw w * (if plOf w ∈ S then ramE (plOf w) * φ (plOf w) else 0)) = ∑ᶠ v, g v :=
      finsum_comp_equiv (Equiv.ofBijective plOf hb) (f := g)
    rw [h1, finsum_eq_sum_of_support_subset (s := S)]
    · refine Finset.sum_congr rfl fun w hw => ?_
      simp only [hg, hw, if_true, lE]
      ring
    · intro v hv
      by_contra hn
      apply hv
      have : v ∉ S := hn
      simp [hg, this]

/- English proof (authored)
For each factor index use the finite-place reindexing formula on its local function. Summing these identities over the factors and multiplying by two gives the claimed equality.
-/
theorem function_of_places : FoOfPlaces := by
  intro I m F
  show 2 * ∑ j ∈ Finset.univ, ∑ w ∈ F.S, lE w * F.Fj j w = _
  congr 1
  exact Finset.sum_congr rfl fun j _ => (sum_over_places F.K F.S (F.Fj j)).2

/- English proof (authored)
Apply the finite-place reindexing formula to the local exponent function at the chosen word and factor. Multiplying the two equal sums by two gives the equality.
-/
theorem exponent_of_places : EeJOfPlaces := by
  intro I m F u j
  show 2 * ∑ w ∈ F.S, lE w * F.Ej u j w = _
  congr 1
  exact (sum_over_places F.K F.S (F.Ej u j)).2

/- English proof (authored)
Apply the free-period divisibility transfer to the data constructed from the given arithmetic parameters. The free bound and period equality are its two hypotheses.
-/
theorem construct_divisibility_of_free : MkDivOfFree := by
  intro H _ _ _ W _ m G C D ell N TT T2 a w Fm logOm h hp
  exact divisibility_of_free H W TT m _ (mkData G C.cHH D ell N TT T2 a w Fm) C logOm h hp

/- English proof (authored)
The fixed-period divisibility condition and the free-parameter condition at that period have identical summands and bounds, so they are equivalent.
-/
theorem divisibility_free_at : DivFreeIsDivAt := by
  intro U0 W Top _ m f D C logOm
  exact Iff.rfl

/- English proof (authored)
Substitute the specified scale into the constructed period equation. It becomes the host period equation with the same logarithmic terms.
-/
theorem construct_periodicity_of_modulus : PerMkOfHost := by
  intro e q d _ _ G logOm hv
  unfold PerHost PerMk
  rw [hv]

/- English proof (authored)
For each word, reindex the divisibility conclusion from the embedded top places back to the top set. Use the row-duality identity for the ambient mean and the place-sum identity for the positive correction. The two expressions multiplying the theorem's error constant are nonnegative. This follows from the positivity of the exponential and the auxiliary-size nonnegativity, together with the size hypotheses. Consequently the assumed larger constant gives the required bound for the constructed data.
-/
theorem construct_divisibility_of_conclusion : MkDivOfConcl := by
  intro H _ _ _ W _ m G C D ell N TT T2 a w Fm logOm C0 Dd XE R ψ hD hXE hX' hR hψ hC hx hk hLa h u0 u
  have h1 := h u0 u
  unfold ThmConcl at h1
  rw [Finset.sum_map, Finset.card_map] at h1
  have hmu := (mu_constant_of_blocks (W u0) m (Fm u0) (Dd u0) (hD u0) (XE u0) (hXE u0) (hX' u0) (R u0) (hR u0)
    (ψ u0) (hψ u0)).1
  have hFo := function_of_places (W u0) m (Fm u0)
  rw [← hmu, ← hFo] at h1
  have hNc : 0 ≤ (mkData G C.cHH D ell N TT T2 a w Fm).Nc :=
    (construct_parameter_definitions H W m G C.cHH D ell N TT T2 a w Fm).2.2.2.2.2.1 hx hk
  set Nc := (mkData G C.cHH D ell N TT T2 a w Fm).Nc with hNcdef
  show muDef (Fm u0).b' (Fm u0).X' (Fm u0).cc + (Fm u0).h u - (Fm u0).Fo ≤
    (∑ t : TT, ((m : ℝ) * (ph (a t) - a t * logOm) - a t * Real.log ((Fm u0).T u : ℝ)))
      + C.cDiv * (Fintype.card TT : ℝ) * (G.x * Real.exp (G.x ^ G.ε)) * G.La
      + C.cDiv * (m : ℝ) * ((2 * (Fintype.card H : ℝ)) * m * Real.exp (G.x ^ G.ε) * G.x ^ G.ε + Nc)
        * G.x ^ (C.eDiv * G.ε)
  rw [Finset.sum_coe_sort TT
    (fun t => (m : ℝ) * (ph (a t) - a t * logOm) - a t * Real.log ((Fm u0).T u : ℝ)), Fintype.card_coe]
  have hsum : (∑ t ∈ TT, ((m : ℝ) * (Formalism.LatticeIndexTer.ph ((fun ρ : E0 × H => a ρ.2) (topEmb H t))
        - (fun ρ : E0 × H => a ρ.2) (topEmb H t) * logOm)
        - (fun ρ : E0 × H => a ρ.2) (topEmb H t) * Real.log ((Fm u0).T u : ℝ)))
      = ∑ t ∈ TT, ((m : ℝ) * (ph (a t) - a t * logOm) - a t * Real.log ((Fm u0).T u : ℝ)) := rfl
  rw [hsum] at h1
  have he : 0 ≤ Real.exp (G.x ^ G.ε) := (Real.exp_pos _).le
  have hX : 0 ≤ (TT.card : ℝ) * (G.x * Real.exp (G.x ^ G.ε)) * G.La :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hx he)) hLa
  have hB : 0 ≤ (2 * (Fintype.card H : ℝ)) * m * Real.exp (G.x ^ G.ε) * G.x ^ G.ε :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) he)
      (Real.rpow_nonneg hx _)
  have hY : 0 ≤ (m : ℝ) * ((2 * (Fintype.card H : ℝ)) * m * Real.exp (G.x ^ G.ε) * G.x ^ G.ε + Nc)
      * G.x ^ (C.eDiv * G.ε) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg hB hNc)) (Real.rpow_nonneg hx _)
  have h2 := mul_le_mul_of_nonneg_right hC (add_nonneg hX hY)
  nlinarith [h1, h2]

/- English proof (authored)
The universal finite set of elements of the subtype of TT maps to TT under the subtype inclusion. Composing with the top embedding therefore has the same image as mapping TT directly.
-/
lemma univ_map_top {H : Type} [AddCommGroup H] (TT : Finset H) :
    (Finset.univ : Finset TT).map ((Function.Embedding.subtype _).trans (topEmb H)) = TT.map (topEmb H) := by
  rw [← Finset.map_map, Finset.univ_eq_attach, Finset.attach_map_val]

/- English proof (authored)
Each factor is nonnegative. The group cardinality and m are nonnegative, the exponential is positive, and a real power of the nonnegative base is nonnegative.
-/
lemma threshold_constant_nonneg {H : Type} [Fintype H] (m : ℕ) (x ε : ℝ) (hx : 0 ≤ x) :
    0 ≤ (2 * (Fintype.card H : ℝ)) * (m : ℝ) * Real.exp (x ^ ε) * x ^ ε :=
  mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    (Real.exp_pos _).le) (Real.rpow_nonneg hx _)

/- English proof (authored)
Apply the general exponent comparison to the constructed parameters. Identify the embedded top set with the image of the actual top set and use the place-sum formula for each local exponent. The explicit threshold factor is nonnegative, so the available constant comparison supplies the corresponding error bounds.
-/
theorem construct_exponent_comparison : TypePrimeCostOfDeviationBoundArith := by
  intro H _ _ _ W _ m G C D ell N TT T2 a w Fm C0 g hg hC hx h
  refine exponent_comparison_of_constant H W TT m _ (mkData G C.cHH D ell N TT T2 a w Fm) C C0 (E0 × H)
    ((Function.Embedding.subtype _).trans (topEmb H)) (fun ρ => a ρ.2)
    (fun u0 u j => ∑ᶠ z : HeightOneSpectrum (𝓞 (Fm u0).K),
        lw z * (if plOf z ∈ (Fm u0).S then ramE (plOf z) * (Fm u0).Ej u j (plOf z) else 0))
    (fun t => rfl) (fun u0 u j => exponent_of_places (W u0) m (Fm u0) u j) hC
    (threshold_constant_nonneg (H := H) m G.x G.ε hx) ?_
  intro u0 u
  rw [univ_map_top]
  have h1 := h u0 u
  rw [← hg] at h1
  exact h1

/- English proof (authored)
Reindex the top set in the corrected-height estimate using its embedding. The main size is nonnegative by its exponential formula, and the explicit threshold factor is nonnegative. The general height comparison now applies with the assumed constant bound.
-/
theorem construct_height_comparison : HeightVariationOfCorrectedHeightBoundArith := by
  intro H _ _ _ W _ m G C D ell N TT T2 a w Fm C0 hC hx hLa h
  refine height_comparison_of_constant H W TT m _ (mkData G C.cHH D ell N TT T2 a w Fm) C C0 (E0 × H)
    ((Function.Embedding.subtype _).trans (topEmb H)) (fun ρ => a ρ.2) (fun t => rfl) hC
    (mul_nonneg hx (Real.exp_pos _).le) hLa (threshold_constant_nonneg (H := H) m G.x G.ε hx) ?_
  intro u0
  rw [univ_map_top]
  exact h u0

/- English proof (authored)
The row-duality formula makes the ambient minimal slope the negative of the row maximal slope. Replace it in the height comparison. The assumed bound for the sum of the mean and the row maximal slope then gives the stated inequality.
-/
theorem construct_height_bound : MkHHOfFun := by
  intro H _ _ _ W _ m G C D ell N TT T2 a w Fm Dd XE R ψ hD hXE hX' hR hψ h u0
  have hmu := (mu_constant_of_blocks (W u0) m (Fm u0) (Dd u0) (hD u0) (XE u0) (hXE u0) (hX' u0) (R u0) (hR u0)
    (ψ u0) (hψ u0)).2
  have h1 := h u0
  rw [hmu]
  linarith

def satD : Data Unit (fun _ => Unit) (Fin 1) 1 1 where
  x := 1
  ε := 1 / 52
  a := Real.exp 1
  b := Real.exp 1
  b' := 1
  k := 1
  L := 1
  La := 1
  B0 := Real.exp 1
  Nc := 0
  gam := 0
  LpL := 0
  v := Real.pi * Real.exp (-1)
  lg := 0
  logGam := 0
  aT := fun _ => 0
  w := fun _ _ _ => 1
  d := fun _ _ => 1
  T := fun _ _ => 1
  muN := fun _ _ => 0
  muMaxN := fun _ _ => 0
  h := fun _ _ => 4
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun _ => 3 + Real.exp 1
  muMinCC := fun _ => 0
  Fo := fun _ => 0
  Ga := fun _ => 0
  Ta := fun _ => 0
  ASK := fun _ => 0
  IO := fun _ => 0
  HH := fun _ => 1
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := 0
  eBar := 0

def satC : Consts where
  cDiv := 60
  eDiv := 1
  cE := 0
  cH := 0
  cCount := 0
  cSlope := 0
  cSl1 := 0
  cLoss := 0
  eLoss := 0
  cHH := 0

def satP : ParNums where
  rd := 1
  f := 1
  N := 1
  S := 0
  tt := 0
  η := 0
  w'' := 0
  dC := 1
  lam0 := 1
  C0 := 1

def satSt : StepNums (Fin 1) (Fin 1) where
  mu0 := 1 + Real.exp 1
  FoP := 0
  hP := 2
  mlam := -1
  hK := fun _ => 1
  phν := fun _ _ => 2
  nν := fun _ _ => 4
  fa := fun _ _ => 0
  Lpass := 2
  Eb := Real.exp 1
  e6 := 1
  eP := 2
  eK := fun _ => 3
  pq := fun _ => 1
  w := fun _ _ => 1
  eE := fun _ _ => 2
  δ := fun _ _ => 3

/- English proof (authored)
Substitute the explicit single-index data, parameters and step values. The two groups of inequalities reduce to numerical comparisons, using exp(1) ≥ 2 from the exponential tangent bound. The scale is π times a positive exponential. Taking its logarithm in the period equation gives the chosen period one. The divisor constant and the correction equality follow by evaluating their specified values.
-/
theorem joint_sat :
    ParHyp satD satP 1 (satD.x ^ (satC.eDiv * satD.ε)) (Fintype.card (Fin 1) : ℝ) ∧
    StepHyp satD satP 1 (satD.x ^ (satC.eDiv * satD.ε))
      (Finset.univ.map (Function.Embedding.refl (Fin 1))) (fun _ => 0) () () satSt ∧
    Per satD 1 ∧ 0 < satD.v ∧ satC.cDiv = 50 * satP.C0 + 10 ∧ satD.Fo () = 2 * satSt.FoP := by
  have e2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ParHyp, satD, satP, satC]
    norm_num
    repeat' apply And.intro
    all_goals linarith
  · simp only [StepHyp, satD, satP, satC, satSt, Formalism.LatticeIndexTer.ph]
    norm_num
    repeat' apply And.intro
    all_goals linarith
  · simp only [Per, satD]
    rw [Real.log_div Real.pi_pos.ne' (mul_pos Real.pi_pos (Real.exp_pos _)).ne',
      Real.log_mul Real.pi_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  · exact mul_pos Real.pi_pos (Real.exp_pos _)
  · simp only [satC, satP]; norm_num
  · simp only [satD, satSt]; norm_num

end Formalism.LFunctionChainParameters.LBrDiv
