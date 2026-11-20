import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.InertPlacesGoodSet
import Formalism.SharpRestriction.LevelLetterCocycles.MemPrimesOverOfMem
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.IsTwistedDualOfGaloisRep
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfCrystallineLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowBoundAtPlaceOfLatticeColengthBoundStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.RowBLong

/- English proof (translation)
Establish `hl' : (11 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hlog : 1 ≤ Real.log l`. Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1` using `Real.log_le_sub_one_of_pos hy`. Unfold `Real.logb`. Break down `le_or_gt 0 (Real.log y) with h | h` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Establish `: Real.log y / Real.log l < 0` using `div_neg_of_neg_of_pos h (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem logb_le_self {l : ℕ} (hl : 11 ≤ l) {y : ℝ} (hy : 0 < y) : Real.logb l y ≤ y := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hlog : 1 ≤ Real.log l := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have h1 := Real.log_le_sub_one_of_pos hy
  unfold Real.logb
  rcases le_or_gt 0 (Real.log y) with h | h
  · calc Real.log y / Real.log l ≤ Real.log y := div_le_self h hlog
      _ ≤ y := by linarith
  · have : Real.log y / Real.log l < 0 := div_neg_of_neg_of_pos h (by linarith)
    linarith

/- English proof (translation)
Establish `hl' : (11 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hm : 0 < ((l : ℝ) - 1) ^ (j + 1)` using `pow_pos (by linarith) _`. Establish `hl1 : (1 : ℝ) < l` using `by linarith`. Break down `hH.eq_or_lt with h0 | hpos` into its components or cases. Rewrite using `[← h0]`.

Simplify using the standard rewrite rules. Check the signs of the components of the expression. Establish `hsplit : Real.logb l H = Real.logb l (H / ((l : ℝ) - 1) ^ (j + 1)) + Real.logb l (((l : ℝ) - 1) ^ (j + 1))`. Rewrite using `[Real.logb_div hpos.ne' hm.ne']`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : Real.logb l (((l : ℝ) - 1) ^ (j + 1)) ≤ (j : ℝ) + 1`. Rewrite using `[Real.logb_pow]`. Establish `h3 : Real.logb l ((l : ℝ) - 1) ≤ 1`. Use `Real.logb_le_logb_of_le hl1 (by linarith : (0:ℝ) < l - 1) (by linarith : (l:ℝ) - 1 ≤ l)` as an intermediate fact. Rewrite `this` using `[Real.logb_self_eq_one hl1]`. Then use the resulting hypothesis.

Use `push_cast`. Establish `: (0:ℝ) ≤ (j:ℝ) + 1` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hsplit]`. Use `logb_le_self hl (div_pos hpos hm)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem logb_le_split {l : ℕ} (hl : 11 ≤ l) (j : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    Real.logb l H ≤ H / ((l : ℝ) - 1) ^ (j + 1) + ((j : ℝ) + 1) := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hm : 0 < ((l : ℝ) - 1) ^ (j + 1) := pow_pos (by linarith) _
  have hl1 : (1 : ℝ) < l := by linarith
  rcases hH.eq_or_lt with h0 | hpos
  · rw [← h0]; simp; positivity
  have hsplit : Real.logb l H = Real.logb l (H / ((l : ℝ) - 1) ^ (j + 1)) + Real.logb l (((l : ℝ) - 1) ^ (j + 1)) := by
    rw [Real.logb_div hpos.ne' hm.ne']; ring
  have h2 : Real.logb l (((l : ℝ) - 1) ^ (j + 1)) ≤ (j : ℝ) + 1 := by
    rw [Real.logb_pow]
    have h3 : Real.logb l ((l : ℝ) - 1) ≤ 1 := by
      have := Real.logb_le_logb_of_le hl1 (by linarith : (0:ℝ) < l - 1) (by linarith : (l:ℝ) - 1 ≤ l)
      rwa [Real.logb_self_eq_one hl1] at this
    push_cast
    have : (0:ℝ) ≤ (j:ℝ) + 1 := by positivity
    nlinarith
  rw [hsplit]
  have := logb_le_self hl (div_pos hpos hm)
  linarith

/- English proof (translation)
Establish `hl' : (11 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hm1 : 1 ≤ ((l : ℝ) - 1) ^ (j + 1)` using `one_le_pow₀ (by linarith)`. Establish `hm : 0 < ((l : ℝ) - 1) ^ (j + 1)` using `by linarith`. Establish `hlog` using `logb_le_split hl j hH0`. Establish `hj : (0 : ℝ) ≤ (j : ℝ) + 1` using `by positivity`.

Establish `hBm : 0 ≤ hB / ((l : ℝ) - 1) ^ (j + 1)` using `div_nonneg hB0 hm.le`. Establish `hGj : (G0 + 1) * ((j : ℝ) + 1) ≤ (GP + 1) * ((j : ℝ) + 1)` using `by nlinarith`. Establish `hj1 : (j : ℝ) + 1 ≤ (GP + 1) * ((j : ℝ) + 1)` using `by nlinarith`. Break down `hH with h | h` into its components or cases. Establish `: H / ((l : ℝ) - 1) ^ (j + 1) ≤ hB / ((l : ℝ) - 1) ^ (j + 1)` using `div_le_div_of_nonneg_right h hm.le`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h1 : H / ((l : ℝ) - 1) ^ (j + 1) ≤ H` using `div_le_self hH0 hm1`. Establish `h2 : 2 * G0 + (j : ℝ) + 1 ≤ 2 * (G0 + 1) * ((j : ℝ) + 1)` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem bracket_le {l : ℕ} (hl : 11 ≤ l) (j : ℕ) {H G0 hB GP large₂ : ℝ} (hH0 : 0 ≤ H) (hG0 : 0 ≤ G0)
    (hGP : G0 ≤ GP) (hB0 : 0 ≤ hB) (hLg : 0 ≤ large₂) (hH : H ≤ hB ∨ H ≤ G0) :
    H / ((l : ℝ) - 1) ^ (j + 1) + (G0 + 1) * ((j : ℝ) + 1) + Real.logb l H ≤
      3 * (hB / ((l : ℝ) - 1) ^ (j + 1) + (GP + 1) * ((j : ℝ) + 1) + large₂) := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hm1 : 1 ≤ ((l : ℝ) - 1) ^ (j + 1) := one_le_pow₀ (by linarith)
  have hm : 0 < ((l : ℝ) - 1) ^ (j + 1) := by linarith
  have hlog := logb_le_split hl j hH0
  have hj : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  have hBm : 0 ≤ hB / ((l : ℝ) - 1) ^ (j + 1) := div_nonneg hB0 hm.le
  have hGj : (G0 + 1) * ((j : ℝ) + 1) ≤ (GP + 1) * ((j : ℝ) + 1) := by nlinarith
  have hj1 : (j : ℝ) + 1 ≤ (GP + 1) * ((j : ℝ) + 1) := by nlinarith
  rcases hH with h | h
  · have : H / ((l : ℝ) - 1) ^ (j + 1) ≤ hB / ((l : ℝ) - 1) ^ (j + 1) := div_le_div_of_nonneg_right h hm.le
    nlinarith
  · have h1 : H / ((l : ℝ) - 1) ^ (j + 1) ≤ H := div_le_self hH0 hm1
    have h2 : 2 * G0 + (j : ℝ) + 1 ≤ 2 * (G0 + 1) * ((j : ℝ) + 1) := by nlinarith
    nlinarith

end GlobalTheory.RowBLong

namespace GlobalTheory.RowBLong

open Formalism.MainNotions.N in
/- English proof (translation)
Establish `hK : K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1` using `inf_eq_left.mpr hb.unram`. Establish `h1 : nLet i w hw = Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1` using `(IntermediateField.equivOfEq hK).toLinearEquiv.finrank_eq`. Rewrite using `[h1]`. Conclude with `hb.deg`.
-/
theorem nLet_eq_nLam {D : D7} {L : SizeData₂ D} {HW : HWOf D.loc} {i : D.nd.Loc}
    {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
    {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    {Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw} {hG : Good (D.nbr i w hw).Kw 1 Cx.LL} {Wd : WordDat (nLet i w hw)}
    (hb : WordBase L HW i r ρ π w hw Cx hG Wd) : nLet i w hw = Formalism.MainNotions.TwistedPlaces.nLam D w := by
  have hK : K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 := inf_eq_left.mpr hb.unram
  have h1 : nLet i w hw = Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 :=
    (IntermediateField.equivOfEq hK).toLinearEquiv.finrank_eq
  rw [h1]
  exact hb.deg

end GlobalTheory.RowBLong

namespace GlobalTheory.RowBLong

attribute [local instance] Formalism.MainNotions.N.nLet_neZero

/- English proof (translation)
Introduce `D L P HW C₂ i r ρ π dc hA hC _ h11 hJ`. Introduce `w hw _ C hCg`. Take `⟨hur, hWd⟩` from `hJ w hw`. Establish `hg : Good (D.nbr i w hw).Kw 1 C.LL` using `hCg.good_one (by omega) (le_trans (le_inf le_rfl hur) le_sup_left)`. Take `⟨Wd, hb, hB⟩` from `hWd C hg`.

Establish `hrow` using `GlobalTheory.Survey.InertPlacesGoodSet.rowL_of_wordsB hA h11 hb hB`. Use `GlobalTheory.T.rowBound_at_place_of_latticeColengthBound D i r ρ π w hw C _ _ hrow ?_` and prove the remaining obligations. Establish `hn : ((nLet i w hw : ℕ) : ℝ) = (Formalism.MainNotions.TwistedPlaces.nLam D w : ℝ)`. Conclude with `nLet_eq_nLam hb` after adjusting the coercions. Establish `hl' : (11 : ℝ) ≤ D.nd.l i` using `by exact_mod_cast h11`.

Establish `hbr` using `bracket_le h11 (Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i)) (H := (WachCoordinates.hCor Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ)) (G0 := ((Wd.w + Wd.S + Wd.η : ℕ) : ℝ)) (hB := Formalism.MainNotions.TwistedPlaces.hB L) (GP := Formalism.MainNotions.TwistedPlaces.GP L) (large₂ := For …`. Unfold `Formalism.MainNotions.TwistedPlaces.GP`. Use `hb.w_le` as an intermediate fact. Use `hb.S_le` as an intermediate fact. Use `hb.η_le` as an intermediate fact.

Use `push_cast`. Use the proof step `linarith)`. Use the proof step `(by linarith [Formalism.MainNotions.TwistedPlaces.one_le_hB L]) (Formalism.MainNotions.TwistedPlaces.Lg_nonneg L)`. Use the proof step `(by`. Unfold `WachCoordinates.hCor`.

Use `split_ifs`. Use `left`. Use `hb.h_le` as an intermediate fact. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `right`. Conclude with `le_rfl)`. Establish `key : C₂ * (((nLet i w hw : ℕ) : ℝ) + 1) * D.R.r * ((WachCoordinates.hCor Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ) / ((D.nd.l i : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) + 1) + (((Wd.w + Wd.S + Wd.η : ℕ) : ℝ) + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l …`. Unfold `coreB`. Rewrite using `[hn]`.

Establish `h0 : 0 ≤ C₂ * ((Formalism.MainNotions.TwistedPlaces.nLam D w : ℝ) + 1) * D.R.r`. Establish `: (0:ℝ) ≤ C₂` using `by linarith`. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation. Unfold `lenRowB ratIn`.

Use `split_ifs with hlt`. Use `(exists_rat_btwn hlt).choose_spec` as an intermediate fact. Combine the linear relations using `[this.1]`. Use `push_neg at hlt`. Establish `hc0 : coreB L (D.nd.l i) w ≤ 0` using `by linarith`.

Establish `: 3 * C₂ * coreB L (D.nd.l i) w ≤ 0`. Establish `: (0:ℝ) ≤ 3 * C₂` using `by linarith`. Use the polynomial consequences of the given equalities and inequalities. Simplify using `only [Rat.cast_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), WachCoordinates.Conclusion2 D C₂ → 1 ≤ C₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → LocalRepresentationBoundCondition L HW C₂ i r ρ π → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc (lenRowB L C₂ (D.nd.l i)) := by
  intro D L P HW C₂ i r ρ π dc hA hC _ h11 hJ
  intro w hw _ C hCg
  obtain ⟨hur, hWd⟩ := hJ w hw
  have hg : Good (D.nbr i w hw).Kw 1 C.LL := hCg.good_one (by omega) (le_trans (le_inf le_rfl hur) le_sup_left)
  obtain ⟨Wd, hb, hB⟩ := hWd C hg
  have hrow := GlobalTheory.Survey.InertPlacesGoodSet.rowL_of_wordsB hA h11 hb hB
  refine GlobalTheory.T.rowBound_at_place_of_latticeColengthBound D i r ρ π w hw C _ _ hrow ?_
  have hn : ((nLet i w hw : ℕ) : ℝ) = (Formalism.MainNotions.TwistedPlaces.nLam D w : ℝ) := by
    exact_mod_cast nLet_eq_nLam hb
  have hl' : (11 : ℝ) ≤ D.nd.l i := by exact_mod_cast h11
  have hbr := bracket_le h11 (Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i))
    (H := (WachCoordinates.hCor Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ)) (G0 := ((Wd.w + Wd.S + Wd.η : ℕ) : ℝ))
    (hB := Formalism.MainNotions.TwistedPlaces.hB L) (GP := Formalism.MainNotions.TwistedPlaces.GP L) (large₂ := Formalism.MainNotions.TwistedPlaces.large₂ L)
    (by positivity) (by positivity)
    (by
      unfold Formalism.MainNotions.TwistedPlaces.GP
      have := hb.w_le; have := hb.S_le; have := hb.η_le
      push_cast; linarith)
    (by linarith [Formalism.MainNotions.TwistedPlaces.one_le_hB L]) (Formalism.MainNotions.TwistedPlaces.Lg_nonneg L)
    (by
      unfold WachCoordinates.hCor
      split_ifs
      · left; have := hb.h_le; push_cast; linarith
      · right; exact le_rfl)
  have key : C₂ * (((nLet i w hw : ℕ) : ℝ) + 1) * D.R.r *
      ((WachCoordinates.hCor Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ) / ((D.nd.l i : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) + 1) +
        (((Wd.w + Wd.S + Wd.η : ℕ) : ℝ) + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) +
        Real.logb (D.nd.l i) (WachCoordinates.hCor Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ)) ≤
      3 * C₂ * coreB L (D.nd.l i) w := by
    unfold coreB
    rw [hn]
    have h0 : 0 ≤ C₂ * ((Formalism.MainNotions.TwistedPlaces.nLam D w : ℝ) + 1) * D.R.r := by
      have : (0:ℝ) ≤ C₂ := by linarith
      positivity
    calc _ ≤ C₂ * ((Formalism.MainNotions.TwistedPlaces.nLam D w : ℝ) + 1) * D.R.r *
          (3 * (Formalism.MainNotions.TwistedPlaces.hB L / ((D.nd.l i : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) + 1) +
            (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) + Formalism.MainNotions.TwistedPlaces.large₂ L)) :=
          mul_le_mul_of_nonneg_left hbr h0
      _ = _ := by ring
  unfold lenRowB ratIn
  split_ifs with hlt
  · have := (exists_rat_btwn hlt).choose_spec
    linarith [this.1]
  · push_neg at hlt
    have hc0 : coreB L (D.nd.l i) w ≤ 0 := by linarith
    have : 3 * C₂ * coreB L (D.nd.l i) w ≤ 0 := by
      have : (0:ℝ) ≤ 3 * C₂ := by linarith
      nlinarith
    simp only [Rat.cast_zero]
    linarith

end GlobalTheory.RowBLong
