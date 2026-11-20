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
import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.RowNT

/- English proof (translation)
Break down `hx0.eq_or_lt with h | hpos` into its components or cases. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogl : 1 ≤ Real.log l`.

Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : Real.log x ≤ Real.log 4 + large₂`. Use `Real.log_le_log hpos hx` as an intermediate fact.

Rewrite `this` using `[Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]`. Then use the resulting hypothesis. Establish `h43 : Real.log 4 ≤ 3` using `by have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith`. Unfold `Real.logb`. Break down `le_or_gt (Real.log x) 0 with hn | hp` into its components or cases. Establish `: Real.log x / Real.log l ≤ 0` using `div_nonpos_of_nonpos_of_nonneg hn (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `: Real.log x / Real.log l ≤ Real.log x` using `div_le_self hp.le hlogl`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem logb_le_of_le_four_exp {l x large₂ : ℝ} (hl : 11 ≤ l) (hLg : 0 ≤ large₂) (hx0 : 0 ≤ x)
    (hx : x ≤ 4 * Real.exp large₂) : Real.logb l x ≤ 3 + large₂ := by
  rcases hx0.eq_or_lt with h | hpos
  · subst h; simp; linarith
  have hlogl : 1 ≤ Real.log l := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have h4 : Real.log x ≤ Real.log 4 + large₂ := by
    have := Real.log_le_log hpos hx
    rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
  have h43 : Real.log 4 ≤ 3 := by have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith
  unfold Real.logb
  rcases le_or_gt (Real.log x) 0 with hn | hp
  · have : Real.log x / Real.log l ≤ 0 := div_nonpos_of_nonpos_of_nonneg hn (by linarith)
    linarith
  · have : Real.log x / Real.log l ≤ Real.log x := div_le_self hp.le hlogl
    linarith

/- English proof (translation)
Establish `hl1 : 1 < l` using `by linarith`. Establish `hl0 : 0 < l` using `by linarith`. Establish `h1 : H / l ≤ 2 * hB / l` using `div_le_div_of_nonneg_right hH hl0.le`. Establish `h2 : Real.logb l (H + 1) ≤ Real.logb l (3 * hB)` using `Real.logb_le_logb_of_le hl1 (by linarith) (by linarith)`. Establish `h3 : Real.logb l (3 * hB) = Real.logb l 3 + Real.logb l hB` using `Real.logb_mul (by norm_num) (by linarith)`.

Establish `h4 : Real.logb l 3 ≤ 1`. Use `Real.logb_le_logb_of_le hl1 (show (0:ℝ) < 3 by norm_num) (show (3:ℝ) ≤ l by linarith)` as an intermediate fact. Rewrite `this` using `[Real.logb_self_eq_one hl1]`. Then use the resulting hypothesis. Establish `h5 : 0 ≤ Real.logb l hB` using `Real.logb_nonneg hl1 hB1`. Establish `h6 : 0 ≤ hB / l` using `div_nonneg (by linarith) hl0.le`.

Establish `h7 : 2 * hB / l = 2 * (hB / l)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lift_shape_le {l H hB e : ℝ} (hl : 11 ≤ l) (hB1 : 1 ≤ hB) (hH0 : 0 ≤ H) (hH : H ≤ 2 * hB)
    (he : e ≤ 23 * (1 + H / l + (1 + Real.logb l (H + 1)))) :
    e ≤ 69 * (1 + hB / l + Real.logb l hB) := by
  have hl1 : 1 < l := by linarith
  have hl0 : 0 < l := by linarith
  have h1 : H / l ≤ 2 * hB / l := div_le_div_of_nonneg_right hH hl0.le
  have h2 : Real.logb l (H + 1) ≤ Real.logb l (3 * hB) :=
    Real.logb_le_logb_of_le hl1 (by linarith) (by linarith)
  have h3 : Real.logb l (3 * hB) = Real.logb l 3 + Real.logb l hB :=
    Real.logb_mul (by norm_num) (by linarith)
  have h4 : Real.logb l 3 ≤ 1 := by
    have := Real.logb_le_logb_of_le hl1 (show (0:ℝ) < 3 by norm_num) (show (3:ℝ) ≤ l by linarith)
    rwa [Real.logb_self_eq_one hl1] at this
  have h5 : 0 ≤ Real.logb l hB := Real.logb_nonneg hl1 hB1
  have h6 : 0 ≤ hB / l := div_nonneg (by linarith) hl0.le
  have h7 : 2 * hB / l = 2 * (hB / l) := by ring
  linarith

/- English proof (translation)
Establish `hl0 : 0 < l` using `by linarith`. Establish `hA : 0 ≤ (n + 1) * r` using `mul_nonneg (by linarith) hr`. Establish `e1 : h / l ^ 2 ≤ hB / l ^ 2` using `div_le_div_of_nonneg_right hh (by positivity)`. Establish `e2 : (w + η) / l ≤ (wP + eta₃) / l` using `div_le_div_of_nonneg_right (by linarith) hl0.le`. Establish `e3 : η * band ≤ eta₃ * ind`.

Establish `hb0 : 0 ≤ band ∨ band < 0` using `le_or_gt 0 band`. Break down `hb0 with hb0 | hb0` into its components or cases. Conclude with `mul_le_mul hη hband hb0 (by linarith)`. Establish `: η * band ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos h0η hb0.le`. Establish `: 0 ≤ eta₃ * ind` using `mul_nonneg (by linarith) hind0`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e4 : 0 ≤ (wP + eta₃) / l` using `div_nonneg (by linarith) hl0.le`. Establish `e5 : 0 ≤ eta₃ * ind` using `mul_nonneg (by linarith) hind0`. Establish `e6 : 0 ≤ hB / l ^ 2` using `div_nonneg (by linarith) (by positivity)`. Establish `hbr : h / l ^ 2 + (w + η) / l + S + 1 + lg + η * band ≤ hB / l ^ 2 + 6 * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `k1 : 320 * (n + 1) * r * (h / l ^ 2 + (w + η) / l + S + 1 + lg + η * band) ≤ 320 * ((n + 1) * r) * (hB / l ^ 2 + 6 * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind))`. Rewrite using `[mul_assoc 320 (n + 1) r]`. Conclude with `mul_le_mul_of_nonneg_left hbr (by positivity)`. Establish `k2 : 320 * n * m * e' ≤ 320 * n * m * (69 * cE)` using `mul_le_mul_of_nonneg_left he (by positivity)`.

Establish `hf : 0 ≤ (n + 1) * r * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind)` using `mul_nonneg hA (by linarith)`. Establish `hH : 0 ≤ (n + 1) * r * (hB / l ^ 2)` using `mul_nonneg hA e6`. Establish `hM : 0 ≤ n * m * cE` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem bound_real {l n r m h w η S lg band e' hB wP eta₃ Sc large₂ ind cE : ℝ}
    (hl : 11 ≤ l) (hn : 0 ≤ n) (hr : 0 ≤ r) (hm : 0 ≤ m)
    (hh : h ≤ hB) (hw : w ≤ wP) (hη : η ≤ eta₃) (hS : S ≤ Sc) (h0w : 0 ≤ w) (h0η : 0 ≤ η)
    (h0S : 0 ≤ S) (h0h : 0 ≤ h) (hlg : lg ≤ 3 + large₂) (hLg : 1 ≤ large₂) (hband : band ≤ ind)
    (hind0 : 0 ≤ ind) (he : e' ≤ 69 * cE) (hcE : 0 ≤ cE) :
    320 * (n + 1) * r * (h / l ^ 2 + (w + η) / l + S + 1 + lg + η * band) + 320 * n * m * e' ≤
      368 * ((n + 1) * r * (hB / l ^ 2)) +
        2082 * ((n + 1) * r * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind)) + 22365 * (n * m * cE) := by
  have hl0 : 0 < l := by linarith
  have hA : 0 ≤ (n + 1) * r := mul_nonneg (by linarith) hr
  have e1 : h / l ^ 2 ≤ hB / l ^ 2 := div_le_div_of_nonneg_right hh (by positivity)
  have e2 : (w + η) / l ≤ (wP + eta₃) / l := div_le_div_of_nonneg_right (by linarith) hl0.le
  have e3 : η * band ≤ eta₃ * ind := by
    have hb0 : 0 ≤ band ∨ band < 0 := le_or_gt 0 band
    rcases hb0 with hb0 | hb0
    · exact mul_le_mul hη hband hb0 (by linarith)
    · have : η * band ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0η hb0.le
      have : 0 ≤ eta₃ * ind := mul_nonneg (by linarith) hind0
      linarith
  have e4 : 0 ≤ (wP + eta₃) / l := div_nonneg (by linarith) hl0.le
  have e5 : 0 ≤ eta₃ * ind := mul_nonneg (by linarith) hind0
  have e6 : 0 ≤ hB / l ^ 2 := div_nonneg (by linarith) (by positivity)
  have hbr : h / l ^ 2 + (w + η) / l + S + 1 + lg + η * band ≤
      hB / l ^ 2 + 6 * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind) := by
    nlinarith
  have k1 : 320 * (n + 1) * r * (h / l ^ 2 + (w + η) / l + S + 1 + lg + η * band) ≤
      320 * ((n + 1) * r) * (hB / l ^ 2 + 6 * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind)) := by
    rw [mul_assoc 320 (n + 1) r]
    exact mul_le_mul_of_nonneg_left hbr (by positivity)
  have k2 : 320 * n * m * e' ≤ 320 * n * m * (69 * cE) :=
    mul_le_mul_of_nonneg_left he (by positivity)
  have hf : 0 ≤ (n + 1) * r * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind) :=
    mul_nonneg hA (by linarith)
  have hH : 0 ≤ (n + 1) * r * (hB / l ^ 2) := mul_nonneg hA e6
  have hM : 0 ≤ n * m * cE := by positivity
  nlinarith

end GlobalTheory.NLink.RowNT

namespace GlobalTheory.NLink.RowNT

attribute [local instance] Formalism.MainNotions.N.nLet_neZero

/- English proof (translation)
Introduce `D L P HW F C₂ i r ρ π w hw Cx hG Wd h17 h54 hpar h11 hπ hb hbox hN`. Introduce `T₁ T₂ Fm h2 h1 hF`. Establish `hp : ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p = D.nd.l i` using `(D.loc _).PD_p _`. Establish `hcA` using `caseA_of_unram (D.loc (D.nd.l i)) (HW (D.nd.l i)) hG hb.unram (by omega)`. Establish `hT` using `h17 (D.nd.l i) (D.nbr i w hw).Kw Cx.LL hG hb.unram`.

Establish `hS` using `GlobalTheory.Survey.InertPlacesGoodSet.setting_of_wordsNT (by omega) hb hN inferInstance T₁ T₂ Fm h2 h1 hF`. Establish `hX` using `(hT (by rw [hp]; exact h11) T₁ T₂ Fm Wd.b Wd.w Wd.S Wd.η Wd.m Wd.up Wd.sz Wd.Mi Wd.hi hS hN.w20 hN.η20 hN.twenty_words_le_b hN.some_nt).1 hN.alt`. Rewrite `hX` using `[hp]`. Establish `hrk : Module.finrank ↥Cx.LL.1 T₂.V = D.R.r`. Take `⟨e, -⟩` from `h2`.

Rewrite using `[e.finrank_eq]`. Simplify using the standard rewrite rules. Establish `hnl : Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) = TwistedPlaces.nLam D w`. Establish `e : K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1` using `inf_eq_left.2 hb.unram`. Rewrite using `[e]`.

Conclude with `hb.deg`. Establish `hO` using `h54.2.2.2.2.2.2.2.2.2.2.1 (D.nd.l i) (D.nbr i w hw).Kw 1 Cx.LL hG T₁ Wd.Mi Wd.hi (hb.t1 T₁ h1).1 (hb.t1 T₁ h1).2.2`. Establish `hl : (11 : ℝ) ≤ (D.nd.l i : ℝ)` using `by exact_mod_cast h11`. Establish `hb1 : (1 : ℝ) ≤ L.sc.b` using `TwistedPlaces.one_le_b L`. Establish `hSc` using `L.Sc_pos`.

Establish `hEt` using `L.etaSz_pos`. Establish `ht0 : (0 : ℝ) ≤ (D.R.t : ℝ)` using `Nat.cast_nonneg _`. Establish `hB1 : (1 : ℝ) ≤ TwistedPlaces.hB L` using `by unfold TwistedPlaces.hB; linarith`. Establish `hB2 : TwistedPlaces.hB L ≤ 2 * L.sc.b` using `by unfold TwistedPlaces.hB; unfold EmbeddingTypeJumps.ParametersPolynomiallyBounded at hpar; linarith`. Establish `hHm : (LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) ≤ 2 * TwistedPlaces.hB L`.

Establish `hfl : LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi ≤ ⌊2 * TwistedPlaces.hB L⌋₊`. Unfold `LiftingTheory.Hmax`. Apply `Finset.sup_le` to reduce the goal to its premises. Introduce `k _`. Apply `Nat.le_floor` to reduce the goal to its premises.

Conclude with `hbox.box_le _`. Combine the equalities or inequalities in the displayed calculation. Establish `he : (TruncatedSeriesCountingBounds.eLift ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 Cx.LL hG) T₁ Wd.Mi Wd.hi : ℝ) ≤ 69 * coreE L (D.nd.l i)`. Establish `hO' : (TruncatedSeriesCountingBounds.eLift ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 Cx.LL hG) T₁ Wd.Mi Wd.hi : ℝ) ≤ 23 * (1 + (LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) / ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p + (1 + Real.logb ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw). …` using `hO.1 hcA`. Rewrite `hO'` using `[hp]`.

Unfold `coreE`. Conclude with `GlobalTheory.NLink.RowNT.lift_shape_le hl hB1 (Nat.cast_nonneg _) hHm hO'`. Establish `hh : (TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ) ≤ TwistedPlaces.hB L`. Establish `hwb : (Wd.w : ℝ) ≤ Wd.b` using `by have := hN.w20; exact_mod_cast (by omega : Wd.w ≤ Wd.b)`. Establish `hle` using `hb.h_le`.

Unfold `TruncatedSeriesCountingBounds.hB`. Use `split_ifs`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Use `push_cast`.

Establish `: (0:ℝ) ≤ Wd.η` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlg : Real.logb (D.nd.l i : ℝ) (2 * (TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ)) ≤ 3 + TwistedPlaces.large₂ L`. Apply `GlobalTheory.NLink.RowNT.logb_le_of_le_four_exp hl (by linarith [TwistedPlaces.L_ge_one L]) (by positivity)` to reduce the goal to its premises. Rewrite using `[← TwistedPlaces.b_eq]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hband : ((if TruncatedSeriesCountingBounds.Band (D.nd.l i) Wd.b Wd.S Wd.η Wd.sz (Real.logb (↑(D.nd.l i)) (2 * ↑(TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz))) 320 then 1 else 0) : ℝ) ≤ (if bandOf L HW 320 i r ρ w then 1 else 0)` using `by split_ifs with hx hy`. Conclude with `le_rfl`. Conclude with `absurd ⟨h11, π, hπ, hw, Cx, hG, Wd, hb, hbox, hN, hx⟩ hy`. Evaluate the numerical expressions.

Conclude with `le_rfl`. Apply the tactic sequence `have key := GlobalTheory.NLink.RowNT.bound_real (l := (D.nd.l i : ℝ)) (n := (TwistedPlaces.nLam D w : ℝ)) (r := (D.R.r : ℝ)) (m := (D.R.m : ℝ)) hl (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hh hb.w_le hb.η_le hb.S_le (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.c …`. Establish `: 0 ≤ TwistedPlaces.hB L / (D.nd.l i : ℝ)` using `div_nonneg (by linarith) (by linarith)`. Use the proof step `linarith)`. Take `⟨mm, k, e1, e2, e3⟩` from `hX`.

Use `⟨mm, k, e1, e2, e3.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))⟩` and prove the remaining obligations. Establish `hnlR : ((Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) : ℕ) : ℝ) = (TwistedPlaces.nLam D w : ℝ)`. Conclude with `hnl` after adjusting the coercions. Establish `hrkR : ((Module.finrank ↥Cx.LL.1 T₂.V : ℕ) : ℝ) = (D.R.r : ℝ)` using `by exact_mod_cast hrk`. Establish `hmR : ((Wd.m : ℕ) : ℝ) = (D.R.m : ℝ)` using `by exact_mod_cast hb.m_eq`.

Rewrite using `[hnlR, hrkR, hmR]`. Simplify using `only [bdCD, coreH, coreF, coreM, flat, rowC, KillingConditions.RowK.K₁, KillingConditions.RowK.K₂, KillingConditions.RowK.K₃]`. Use `le_trans key (le_of_eq ?_)` and prove the remaining obligations. Evaluate the numerical expressions.
-/
theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : WordDat (nLet i w hw)), ArcLiftingSetup.aux₃ D HW F 320 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → π ∈ D.nd.Zgood i → WordBase L HW i r ρ π w hw Cx hG Wd → WordBox L Wd → WordsNT Wd → RowL i r ρ π w hw Cx (bdCD L (bandOf L HW 320 i r ρ w) (D.nd.l i) w (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃) := by
  intro D L P HW F C₂ i r ρ π w hw Cx hG Wd h17 h54 hpar h11 hπ hb hbox hN
  intro T₁ T₂ Fm h2 h1 hF
  classical
  have hp : ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p = D.nd.l i := (D.loc _).PD_p _
  have hcA := caseA_of_unram (D.loc (D.nd.l i)) (HW (D.nd.l i)) hG hb.unram (by omega)
  have hT := h17 (D.nd.l i) (D.nbr i w hw).Kw Cx.LL hG hb.unram
  have hS := GlobalTheory.Survey.InertPlacesGoodSet.setting_of_wordsNT (by omega) hb hN inferInstance T₁ T₂ Fm h2 h1 hF
  have hX := (hT (by rw [hp]; exact h11) T₁ T₂ Fm Wd.b Wd.w Wd.S Wd.η Wd.m Wd.up Wd.sz Wd.Mi Wd.hi hS
    hN.w20 hN.η20 hN.twenty_words_le_b hN.some_nt).1 hN.alt
  rw [hp] at hX
  have hrk : Module.finrank ↥Cx.LL.1 T₂.V = D.R.r := by
    obtain ⟨e, -⟩ := h2
    rw [e.finrank_eq]; simp
  have hnl : Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) = TwistedPlaces.nLam D w := by
    have e : K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 := inf_eq_left.2 hb.unram
    rw [e]
    exact hb.deg
  have hO := h54.2.2.2.2.2.2.2.2.2.2.1 (D.nd.l i) (D.nbr i w hw).Kw 1 Cx.LL hG T₁ Wd.Mi Wd.hi
    (hb.t1 T₁ h1).1 (hb.t1 T₁ h1).2.2
  have hl : (11 : ℝ) ≤ (D.nd.l i : ℝ) := by exact_mod_cast h11
  have hb1 : (1 : ℝ) ≤ L.sc.b := TwistedPlaces.one_le_b L
  have hSc := L.Sc_pos
  have hEt := L.etaSz_pos
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hB1 : (1 : ℝ) ≤ TwistedPlaces.hB L := by unfold TwistedPlaces.hB; linarith
  have hB2 : TwistedPlaces.hB L ≤ 2 * L.sc.b := by unfold TwistedPlaces.hB; unfold EmbeddingTypeJumps.ParametersPolynomiallyBounded at hpar; linarith
  have hHm : (LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) ≤ 2 * TwistedPlaces.hB L := by
    have hfl : LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi ≤ ⌊2 * TwistedPlaces.hB L⌋₊ := by
      unfold LiftingTheory.Hmax
      apply Finset.sup_le
      intro k _
      apply Nat.le_floor
      exact hbox.box_le _
    calc (LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) ≤ (⌊2 * TwistedPlaces.hB L⌋₊ : ℝ) := by exact_mod_cast hfl
      _ ≤ 2 * TwistedPlaces.hB L := Nat.floor_le (by linarith)
  have he : (TruncatedSeriesCountingBounds.eLift ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 Cx.LL hG) T₁ Wd.Mi Wd.hi : ℝ) ≤
      69 * coreE L (D.nd.l i) := by
    have hO' : (TruncatedSeriesCountingBounds.eLift ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 Cx.LL hG) T₁ Wd.Mi Wd.hi : ℝ) ≤
        23 * (1 + (LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) / ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p +
          (1 + Real.logb ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p
            ((LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) + 1))) := hO.1 hcA
    rw [hp] at hO'
    unfold coreE
    exact GlobalTheory.NLink.RowNT.lift_shape_le hl hB1 (Nat.cast_nonneg _) hHm hO'
  have hh : (TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ) ≤ TwistedPlaces.hB L := by
    have hwb : (Wd.w : ℝ) ≤ Wd.b := by have := hN.w20; exact_mod_cast (by omega : Wd.w ≤ Wd.b)
    have hle := hb.h_le
    unfold TruncatedSeriesCountingBounds.hB
    split_ifs
    · push_cast; linarith
    · push_cast; have : (0:ℝ) ≤ Wd.η := Nat.cast_nonneg _; linarith
  have hlg : Real.logb (D.nd.l i : ℝ) (2 * (TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ)) ≤ 3 + TwistedPlaces.large₂ L := by
    apply GlobalTheory.NLink.RowNT.logb_le_of_le_four_exp hl (by linarith [TwistedPlaces.L_ge_one L]) (by positivity)
    rw [← TwistedPlaces.b_eq]; linarith
  have hband : ((if TruncatedSeriesCountingBounds.Band (D.nd.l i) Wd.b Wd.S Wd.η Wd.sz
        (Real.logb (↑(D.nd.l i)) (2 * ↑(TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz))) 320 then 1 else 0) : ℝ) ≤
      (if bandOf L HW 320 i r ρ w then 1 else 0) := by
    split_ifs with hx hy
    · exact le_rfl
    · exact absurd ⟨h11, π, hπ, hw, Cx, hG, Wd, hb, hbox, hN, hx⟩ hy
    · norm_num
    · exact le_rfl
  have key := GlobalTheory.NLink.RowNT.bound_real (l := (D.nd.l i : ℝ)) (n := (TwistedPlaces.nLam D w : ℝ))
    (r := (D.R.r : ℝ)) (m := (D.R.m : ℝ)) hl (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hh hb.w_le hb.η_le hb.S_le (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hlg (TwistedPlaces.L_ge_one L) hband (by split_ifs <;> norm_num) he
    (by unfold coreE; have := Real.logb_nonneg (by linarith : (1:ℝ) < D.nd.l i) hB1
        have : 0 ≤ TwistedPlaces.hB L / (D.nd.l i : ℝ) := div_nonneg (by linarith) (by linarith)
        linarith)
  obtain ⟨mm, k, e1, e2, e3⟩ := hX
  refine ⟨mm, k, e1, e2, e3.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))⟩
  have hnlR : ((Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) : ℕ) : ℝ) = (TwistedPlaces.nLam D w : ℝ) := by
    exact_mod_cast hnl
  have hrkR : ((Module.finrank ↥Cx.LL.1 T₂.V : ℕ) : ℝ) = (D.R.r : ℝ) := by exact_mod_cast hrk
  have hmR : ((Wd.m : ℕ) : ℝ) = (D.R.m : ℝ) := by exact_mod_cast hb.m_eq
  rw [hnlR, hrkR, hmR]
  simp only [bdCD, coreH, coreF, coreM, flat, rowC, KillingConditions.RowK.K₁, KillingConditions.RowK.K₂, KillingConditions.RowK.K₃]
  refine le_trans key (le_of_eq ?_)
  norm_num

end GlobalTheory.NLink.RowNT
