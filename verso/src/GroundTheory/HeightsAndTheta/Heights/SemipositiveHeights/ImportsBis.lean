import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsSmallOfArVolPPos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTopConstantTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalModelExists
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionPointHeight
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionOrderAtPoint
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCurvePointsFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.LatticeWithoutBigness

noncomputable section

/- English proof (translation)
Establish `hG : ArithmeticVolumeBig.Statement` using `ArithmeticVolumeBig.of_moriwakiBig NefOnGenericOfSemipos.proof hMo`. Establish `hT : TopConstantTwist.Statement` using `TopConstantTwist.proof`. Establish `hM : BirationalModelExists.Statement` using `BirationalModelExists.proof`. Establish `hS : SmallSectionPointHeight.Statement` using `SmallSectionPointHeight.proof SectionOrderAtPoint.proof`. Establish `hfin : CurvePointsFinite.Statement` using `CurvePointsFinite.proof`.

Introduce `K _ ι _ P P0 D A e' F II hII har hP0 hsemi hnef hconj hF hdense`. Establish `hA : IsSmoothHerm A` using `hsemi.1`. Establish `: Nonempty K` using `har.1`. Establish `hdeg : ∀ W : Ideal (MRing ι), IsArithVar W 1 → (0 : ℝ) < degC W`. Introduce `W hW`.

Establish `: Finite (projPts W)` using `hfin K ι W hW`. Take `⟨z, hz⟩` from `IndefiniteRowSideFullHecke.HeightsSet.CurveComplexPoint.full K ι W hW`. Establish `: Nonempty (projPts W)` using `⟨Quot.mk _ ⟨z, hz⟩⟩`. Establish `: 0 < Nat.card (projPts W)` using `Nat.card_pos`. Conclude with `this` after adjusting the coercions.

Establish `hmc : ∀ W : Ideal (MRing ι), IsArithVar W 1 → ∀ c : ℝ, II K ι W 1 ![A.tensor (constLine c)] = II K ι W 1 ![A] - ptsIntegral (e` using `0) W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)) (fun _ => c) := by`. Introduce `W hW c`. Establish `h` using `metricChange K ι (II K ι) (hII K ι) W 0 ![] A (fun _ => c) (fun _ _ _ => rfl) hW (fun j => j.elim0) hA contDiffOn_const`. Establish `e1 : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (Fin.snoc (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) B : Fin (0 + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = ![B]` using `fun B => by`. Use function extensionality and compare the values at `i`.

Use `fin_cases i`. Both sides reduce to the same expression. Rewrite `h` using `[e1, e1]`. Conclude with `h`. Establish `hlow : ∀ W : Ideal (MRing ι), IsArithVar W 1 → ∀ c : ℝ, c * degC W ≤ ptsIntegral (e` using `0) W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)) (fun _ => c) := by`.

Introduce `W hW c`. Conclude with `PtsIntegralZeroLowerNE.proof K ι W _ (fun _ => c) c hW.2.1.2.1 (hfin K ι W hW) (fun _ _ _ _ => rfl) (fun _ _ => le_rfl)`. Establish `h1P : (1 : MRing ι) ∉ P` using `fun h => har.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)`. Establish `hfun : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (fun _ : Fin 1 => B) = ![B]` using `fun B => by`. Use function extensionality and compare the values at `i`.

Use `fin_cases i`. Both sides reduce to the same expression. Break down `Nat.eq_zero_or_pos D with hD | hD` into its components or cases. Substitute `hD` using the available equality. Take `⟨W, hWF, -⟩` from `hdense 1 ⟨fun _ => 0, ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_one⟩ h1P`.

Take `⟨hW, hPW, hle⟩` from `hF W hWF`. Establish `: P.IsPrime` using `har.2.1.1`. Establish `hWP : P = W` using `CurveIsOrbit.eq_of_le_of_ringKrullDim_eq (d := 1 + Fintype.card K) hPW har.2.2.2 hW.2.2.2`. Rewrite `hle` using `[← hWP]`. Establish `htw : II K ι P 1 (fun _ => A.tensor (constLine e')) = II K ι P 1 (fun _ => A) - ((1 : ℕ) : ℝ) * e' * geomDeg P A 0` using `hT K ι P 0 A e' II hII har hA`.

Rewrite `htw` using `[hfun, hfun]`. Establish `hm` using `hmc P har e'`. Establish `hl` using `hlow P har e'`. Use `show II K ι P 1 (fun _ => A) ≤ ((1 : ℕ) : ℝ) * e' * geomDeg P A 0`. Rewrite using `[hfun]`.

Move the coercions through the operations in `at htw ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨Ω, _, y, hyP, hbir⟩` from `hM K ι P (D + 1) har`. Substitute `hyP` using the available equality. Assume the negation of the conclusion as `hlt`.

Use `push Not at hlt`. Take `⟨e'', hgt, htop⟩` from `exists_gt_of_lt (N := ((D + 1 : ℕ) : ℝ)) (by positivity) hlt`. Establish `htw` using `hT K ι (mCoordIdeal y) D A e'' II hII har hA`. Establish `hvol` using `hG K ι Ω y D (A.tensor (constLine e'')) P0 II hD hII har hbir hP0 (isSemipositiveRel_twist hsemi e'') (nefOnFibres_twist hnef e'') (isConjInvariantH_twist hconj e'')`. Establish `hpos : 0 < arVolP (IsSmallH (mCoordIdeal y) y (A.tensor (constLine e''))) (chartLat y (A.tensor (constLine e'')).a) 1 D`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨τ, hτ, s, hsL, hs0, hsm⟩` from `exists_small_section_of_arithmeticVolume_pos hpos`. Take `⟨f, hfh, hfP, hfW⟩` from `hS K ι Ω y D (A.tensor (constLine e'')) τ s II hII har hbir (isSmoothHerm_twist hA e'') hτ (SmallSectionPointHeight.chartLat_le_chartLatNm _ _ _ hsL) hs0 hsm`. Take `⟨W, hWF, hfW'⟩` from `hdense f hfh hfP`. Take `⟨hW, hPW, hle⟩` from `hF W hWF`.

Establish `h0` using `hfW W hW hPW hfW'`. Establish `hm` using `hmc W hW e''`. Establish `hl` using `hlow W hW e''`. Establish `hd` using `hdeg W hW`. Use polynomial arithmetic with `[mul_pos (sub_pos.mpr hgt) hd]`.
-/
theorem Z2.proof (hMo : MoriwakiBigStatement) : SuccessiveMinimaUpperBound := by
  have hG : ArithmeticVolumeBig.Statement := ArithmeticVolumeBig.of_moriwakiBig NefOnGenericOfSemipos.proof hMo
  have hT : TopConstantTwist.Statement := TopConstantTwist.proof
  have hM : BirationalModelExists.Statement := BirationalModelExists.proof
  have hS : SmallSectionPointHeight.Statement := SmallSectionPointHeight.proof SectionOrderAtPoint.proof
  have hfin : CurvePointsFinite.Statement := CurvePointsFinite.proof
  intro K _ ι _ P P0 D A e' F II hII har hP0 hsemi hnef hconj hF hdense
  have hA : IsSmoothHerm A := hsemi.1
  have : Nonempty K := har.1

  have hdeg : ∀ W : Ideal (MRing ι), IsArithVar W 1 → (0 : ℝ) < degC W := by
    intro W hW
    have : Finite (projPts W) := hfin K ι W hW
    obtain ⟨z, hz⟩ := IndefiniteRowSideFullHecke.HeightsSet.CurveComplexPoint.full K ι W hW
    have : Nonempty (projPts W) := ⟨Quot.mk _ ⟨z, hz⟩⟩
    have : 0 < Nat.card (projPts W) := Nat.card_pos
    exact_mod_cast this

  have hmc : ∀ W : Ideal (MRing ι), IsArithVar W 1 → ∀ c : ℝ, II K ι W 1 ![A.tensor (constLine c)] =
      II K ι W 1 ![A] - ptsIntegral (e := 0) W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι))
        (fun _ => c) := by
    intro W hW c
    have h := metricChange K ι (II K ι) (hII K ι) W 0 ![] A (fun _ => c) (fun _ _ _ => rfl) hW
      (fun j => j.elim0) hA contDiffOn_const
    have e1 : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι,
        (Fin.snoc (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) B : Fin (0 + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
          = ![B] := fun B => by
      funext i
      fin_cases i
      rfl
    rw [e1, e1] at h
    exact h
  have hlow : ∀ W : Ideal (MRing ι), IsArithVar W 1 → ∀ c : ℝ,
      c * degC W ≤ ptsIntegral (e := 0) W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)) (fun _ => c) := by
    intro W hW c
    exact PtsIntegralZeroLowerNE.proof K ι W _ (fun _ => c) c hW.2.1.2.1 (hfin K ι W hW)
      (fun _ _ _ _ => rfl) (fun _ _ => le_rfl)
  have h1P : (1 : MRing ι) ∉ P := fun h => har.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  have hfun : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (fun _ : Fin 1 => B) = ![B] := fun B => by
    funext i
    fin_cases i
    rfl
  rcases Nat.eq_zero_or_pos D with hD | hD
  ·
    subst hD
    obtain ⟨W, hWF, -⟩ := hdense 1 ⟨fun _ => 0, ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_one⟩ h1P
    obtain ⟨hW, hPW, hle⟩ := hF W hWF
    have : P.IsPrime := har.2.1.1
    have hWP : P = W :=
      CurveIsOrbit.eq_of_le_of_ringKrullDim_eq (d := 1 + Fintype.card K) hPW har.2.2.2 hW.2.2.2
    rw [← hWP] at hle
    have htw : II K ι P 1 (fun _ => A.tensor (constLine e')) =
        II K ι P 1 (fun _ => A) - ((1 : ℕ) : ℝ) * e' * geomDeg P A 0 := hT K ι P 0 A e' II hII har hA
    rw [hfun, hfun] at htw
    have hm := hmc P har e'
    have hl := hlow P har e'
    show II K ι P 1 (fun _ => A) ≤ ((1 : ℕ) : ℝ) * e' * geomDeg P A 0
    rw [hfun]
    push_cast at htw ⊢
    linarith
  ·
    obtain ⟨Ω, _, y, hyP, hbir⟩ := hM K ι P (D + 1) har
    subst hyP
    by_contra hlt
    push Not at hlt
    obtain ⟨e'', hgt, htop⟩ := exists_gt_of_lt (N := ((D + 1 : ℕ) : ℝ)) (by positivity) hlt
    have htw := hT K ι (mCoordIdeal y) D A e'' II hII har hA
    have hvol := hG K ι Ω y D (A.tensor (constLine e'')) P0 II hD hII har hbir hP0
      (isSemipositiveRel_twist hsemi e'') (nefOnFibres_twist hnef e'') (isConjInvariantH_twist hconj e'')
    have hpos : 0 < arVolP (IsSmallH (mCoordIdeal y) y (A.tensor (constLine e'')))
        (chartLat y (A.tensor (constLine e'')).a) 1 D := by
      linarith
    obtain ⟨τ, hτ, s, hsL, hs0, hsm⟩ := exists_small_section_of_arithmeticVolume_pos hpos
    obtain ⟨f, hfh, hfP, hfW⟩ := hS K ι Ω y D (A.tensor (constLine e'')) τ s II hII har hbir
      (isSmoothHerm_twist hA e'') hτ (SmallSectionPointHeight.chartLat_le_chartLatNm _ _ _ hsL) hs0 hsm
    obtain ⟨W, hWF, hfW'⟩ := hdense f hfh hfP
    obtain ⟨hW, hPW, hle⟩ := hF W hWF
    have h0 := hfW W hW hPW hfW'
    have hm := hmc W hW e''
    have hl := hlow W hW e''
    have hd := hdeg W hW
    nlinarith [mul_pos (sub_pos.mpr hgt) hd]

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
