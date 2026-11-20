import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.PointEvaluationMultiplicativeTsum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideQuadraticFormIdentity
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.DerivSimilitudeCharAtOneEqTrace
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum

/- English proof (translation)
Establish `hT : Th L g' = Th L g` using `hR`. Establish `hm : ∀ P, mean L P g' = mean L P g` using `fun P => by`. Unfold `mean`. Rewrite using `[hT, hC]`. Establish `hmom : mom L g' = mom L g`.

Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `i j w`. Conclude with `hm _`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `fn`.

Rewrite using `[hT]`. Unfold `dev`. Rewrite using `[hmom]`.
-/
private theorem gauss_sum_determines_value_and_deviation {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (L : AddSubgroup (Fin a → Af E)) (g g' : GA E a)
    (hR : gsum L gauss g' = gsum L gauss g)
    (hC : ∀ F : (Fin a → Cinf E) → ℂ, gsum L F g' = gsum L F g) :
    fn L g' = fn L g ∧ dev L g' = dev L g := by
  have hT : Th L g' = Th L g := hR
  have hm : ∀ P, mean L P g' = mean L P g := fun P => by
    unfold mean
    rw [hT, hC]
  have hmom : mom L g' = mom L g := by
    apply Subtype.ext
    ext i j w
    exact hm _
  refine ⟨?_, ?_⟩
  · unfold fn
    rw [hT]
  · unfold dev
    rw [hmom]

/- English proof (translation)
Introduce `E _ _ _ a ha L`. Use `⟨fun γ t g => gauss_sum_determines_value_and_deviation L _ _ ((UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℝ gauss).1 γ t g) (fun F => (UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℂ F).1 γ t g), fun U hU hL u hu g => gauss_sum_determines_value_and_devi …` and prove the remaining obligations. Establish `h1` using `(UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℝ gauss).2.1 g (Unitary.toUnits k)`. Establish `hk : (Unitary.toUnits k : GL (Fin a) (Cinf E)).val = k.1` using `rfl`. Establish `hs : sc k.1 = 1` using `(UpperTheory.deriv_similitudeChar_at_one_eq_trace E a).2.2.2.2 k`.

Establish `hq` using `UpperTheory.geometric_side_quadraticForm_identity E a`. Unfold `Th`. Rewrite using `[h1]`. Unfold `gsum`. Use `tsum_congr fun v => ?_` and prove the remaining obligations.

Rewrite using `[hk, hs, one_smul]`. Unfold `gauss`. Rewrite using `[hq.2.2.1, (Unitary.mem_iff.1 k.2).2, hq.1]`.
-/
theorem UpperTheory.lattice_point_count_bound :
    FnInv := by
  intro E _ _ _ a ha L
  refine ⟨fun γ t g => gauss_sum_determines_value_and_deviation L _ _ ((UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℝ gauss).1 γ t g)
      (fun F => (UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℂ F).1 γ t g),
    fun U hU hL u hu g => gauss_sum_determines_value_and_deviation L _ _ ((UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℝ gauss).2.2 U hU hL u hu g)
      (fun F => (UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℂ F).2.2 U hU hL u hu g), fun k g => ?_⟩
  have h1 := (UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℝ gauss).2.1 g (Unitary.toUnits k)
  have hk : (Unitary.toUnits k : GL (Fin a) (Cinf E)).val = k.1 := rfl
  have hs : sc k.1 = 1 := (UpperTheory.deriv_similitudeChar_at_one_eq_trace E a).2.2.2.2 k
  have hq := UpperTheory.geometric_side_quadraticForm_identity E a
  unfold Th
  rw [h1]
  unfold gsum
  refine tsum_congr fun v => ?_
  rw [hk, hs, one_smul]
  unfold gauss
  rw [hq.2.2.1, (Unitary.mem_iff.1 k.2).2, hq.1]
