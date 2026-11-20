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

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.RowsThick

/- English proof (translation)
Unfold `Real.logb`. Rewrite using `[div_le_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem logb_le_of_log_le {l x A : ℝ} (hl : 1 ≤ Real.log l) (hx : Real.log x ≤ A) (hA : 0 ≤ A) :
    Real.logb l x ≤ A := by
  unfold Real.logb
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/- English proof (translation)
Establish `h1 : Real.exp 1 ≤ l` using `by linarith [Real.exp_one_lt_d9]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem one_le_log_of_eleven {l : ℝ} (hl : 11 ≤ l) : 1 ≤ Real.log l := by
  have h1 : Real.exp 1 ≤ l := by linarith [Real.exp_one_lt_d9]
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log l := Real.log_le_log (Real.exp_pos 1) h1

/- English proof (translation)
Establish `hlog` using `one_le_log_of_eleven hl`. Establish `hl0 : 0 < l` using `by linarith`. Establish `hl1 : 0 < l - 1` using `by linarith`. Establish `hetaP0 : 0 ≤ eta₃` using `hη0.trans hη`. Establish `hSc0 : 0 ≤ Sc` using `hS0.trans hS`.

Establish `hlB : 0 < Real.log l` using `by linarith`. Establish `hlam : Real.logb l (2 * H) ≤ 7 + large₂`. Apply `logb_le_of_log_le hlog _ (by linarith)` to reduce the goal to its premises. Break down `hH0.eq_or_lt with h0 | hpos` into its components or cases. Rewrite using `[← h0]`.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h8 : 2 * H ≤ 8 * Real.exp large₂` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Establish `hlogB : 0 ≤ Real.logb l hB` using `Real.logb_nonneg (by linarith) hB1`.

Establish `hlamB : Real.logb l (H' + 1) ≤ 1 + Real.logb l hB`. Establish `h3 : Real.log (H' + 1) ≤ Real.log l + Real.log hB`. Combine the equalities or inequalities in the displayed calculation. Use `Real.log_le_log (show (0 : ℝ) < 3 by norm_num) (show (3 : ℝ) ≤ l by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Unfold `Real.logb`. Combine the equalities or inequalities in the displayed calculation. Establish `hu0 : 0 ≤ eta₃ / l` using `div_nonneg hetaP0 hl0.le`. Establish `hv0 : 0 ≤ hB / l` using `div_nonneg (by linarith) hl0.le`. Establish `hw0 : 0 ≤ wP / l` using `div_nonneg hwP hl0.le`.

Establish `hE0 : 0 ≤ hB / l ^ 2` using `div_nonneg (by linarith) (by positivity)`. Establish `hHl : 32 * H / l ^ 2 ≤ 32 * (hB / l ^ 2) + 3 * (eta₃ / l)`. Establish `a1 : H / l ^ 2 ≤ (hB + eta₃) / l ^ 2` using `div_le_div_of_nonneg_right hH (by positivity)`. Establish `a2 : eta₃ / l ^ 2 = (eta₃ / l) / l` using `by rw [div_div, sq]`. Establish `a3 : (eta₃ / l) / l ≤ (eta₃ / l) / 11` using `div_le_div_of_nonneg_left hu0 (by norm_num) hl`.

Establish `a4` using `add_div hB eta₃ (l ^ 2)`. Rewrite using `[mul_div_assoc]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hηl : 10 * η / (l - 1) ≤ 11 * (eta₃ / l)`. Rewrite using `[div_le_iff₀ hl1]`.

Establish `a1 : 11 * (eta₃ / l) * (l - 1) = 11 * eta₃ - 11 * (eta₃ / l)` using `by field_simp`. Establish `a2 : eta₃ / l ≤ eta₃ / 11` using `div_le_div_of_nonneg_left hetaP0 (by norm_num) hl`. Rewrite using `[a1]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hwe : (wP + eta₃) / l = wP / l + eta₃ / l` using `add_div _ _ _`.

Use `set E1 := hB / l ^ 2 with hE1`. Use `set M1 := 1 + hB / l + Real.logb l hB with hM1`. Use `set cD := (H + 1) / (l - 1) + 1 with hcD`. Establish `hflt0 : 0 ≤ flt` using `by linarith`. Establish `he1 : e ≤ 32 * E1 + 225 * flt` using `by linarith`.

Establish `he2 : e' ≤ 69 * M1`. Establish `a1 : H' / l ≤ 2 * (hB / l)`. Rewrite using `[← mul_div_assoc]; exact div_le_div_of_nonneg_right (by linarith) hl0.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcD4 : cD ≤ 4 * M1`.

Establish `a1 : (H + 1) / (l - 1) ≤ 4 * (hB / l)`. Rewrite using `[div_le_iff₀ hl1]`. Establish `b1 : 4 * (hB / l) * (l - 1) = 4 * hB - 4 * (hB / l)` using `by field_simp`. Establish `b2 : hB / l ≤ hB / 11` using `div_le_div_of_nonneg_left (by linarith) (by norm_num) hl`. Rewrite using `[b1]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hcD]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hM0 : 0 ≤ M1` using `by linarith`. Establish `h1 : (n + 1) * r * e ≤ (n + 1) * r * (32 * E1 + 225 * flt)` using `mul_le_mul_of_nonneg_left he1 (by positivity)`.

Establish `h2 : n * m * e' ≤ n * m * (69 * M1)` using `mul_le_mul_of_nonneg_left he2 (by positivity)`. Establish `h3 : n * r * S ≤ (n + 1) * r * flt`. Establish `: S ≤ flt` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Establish `q1 : (n + 1) * r * flt = n * r * flt + r * flt` using `by ring`.

Establish `q2` using `mul_nonneg hr hflt0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : n * m * cD ≤ n * m * (4 * M1)` using `mul_le_mul_of_nonneg_left hcD4 (by positivity)`. Establish `p1 : 0 ≤ (n + 1) * r * E1` using `by positivity`. Establish `p2 : 0 ≤ (n + 1) * r * flt` using `by positivity`.

Establish `p3 : 0 ≤ n * m * M1` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem colBd_le_row {l n r m S η H H' e e' hB eta₃ wP Sc large₂ flt : ℝ}
    (hl : 11 ≤ l) (hn : 0 ≤ n) (hr : 0 ≤ r) (hm : 0 ≤ m) (hS0 : 0 ≤ S) (hS : S ≤ Sc) (hη0 : 0 ≤ η)
    (hη : η ≤ eta₃) (hH0 : 0 ≤ H) (hH : H ≤ hB + eta₃) (hetaB : eta₃ ≤ hB) (hB1 : 1 ≤ hB)
    (hBb : hB ≤ 2 * Real.exp large₂) (hLg : 1 ≤ large₂) (hwP : 0 ≤ wP)
    (hflt : (wP + eta₃) / l + Sc + large₂ ≤ flt)
    (he : e ≤ 32 * H / l ^ 2 + 4 * S + 10 * η / (l - 1) + 25 * (Real.logb l (2 * H) + 1))
    (hH'0 : 0 ≤ H') (hH' : H' ≤ H)
    (he' : e' ≤ 23 * (1 + H' / l + (1 + Real.logb l (H' + 1)))) :
    (n + 1) * r * e + 4 * n * m * e' + 3 / 2 * n * (r * S + 2 * m * ((H + 1) / (l - 1) + 1)) ≤
      368 * ((n + 1) * r * (hB / l ^ 2)) + 2082 * ((n + 1) * r * flt) +
        22365 * (n * m * (1 + hB / l + Real.logb l hB)) := by
  have hlog := one_le_log_of_eleven hl
  have hl0 : 0 < l := by linarith
  have hl1 : 0 < l - 1 := by linarith
  have hetaP0 : 0 ≤ eta₃ := hη0.trans hη
  have hSc0 : 0 ≤ Sc := hS0.trans hS
  have hlB : 0 < Real.log l := by linarith

  have hlam : Real.logb l (2 * H) ≤ 7 + large₂ := by
    apply logb_le_of_log_le hlog _ (by linarith)
    rcases hH0.eq_or_lt with h0 | hpos
    · rw [← h0]; simp; linarith
    · have h8 : 2 * H ≤ 8 * Real.exp large₂ := by linarith
      calc Real.log (2 * H) ≤ Real.log (8 * Real.exp large₂) := Real.log_le_log (by linarith) h8
        _ = Real.log 8 + large₂ := by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
        _ ≤ 7 + large₂ := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)]

  have hlogB : 0 ≤ Real.logb l hB := Real.logb_nonneg (by linarith) hB1
  have hlamB : Real.logb l (H' + 1) ≤ 1 + Real.logb l hB := by
    have h3 : Real.log (H' + 1) ≤ Real.log l + Real.log hB := by
      calc Real.log (H' + 1) ≤ Real.log (3 * hB) := Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 3 + Real.log hB := Real.log_mul (by norm_num) (by linarith)
        _ ≤ Real.log l + Real.log hB := by
          have := Real.log_le_log (show (0 : ℝ) < 3 by norm_num) (show (3 : ℝ) ≤ l by linarith)
          linarith
    unfold Real.logb
    calc Real.log (H' + 1) / Real.log l ≤ (Real.log l + Real.log hB) / Real.log l :=
          div_le_div_of_nonneg_right h3 hlB.le
      _ = 1 + Real.log hB / Real.log l := by rw [add_div, div_self hlB.ne']

  have hu0 : 0 ≤ eta₃ / l := div_nonneg hetaP0 hl0.le
  have hv0 : 0 ≤ hB / l := div_nonneg (by linarith) hl0.le
  have hw0 : 0 ≤ wP / l := div_nonneg hwP hl0.le
  have hE0 : 0 ≤ hB / l ^ 2 := div_nonneg (by linarith) (by positivity)
  have hHl : 32 * H / l ^ 2 ≤ 32 * (hB / l ^ 2) + 3 * (eta₃ / l) := by
    have a1 : H / l ^ 2 ≤ (hB + eta₃) / l ^ 2 := div_le_div_of_nonneg_right hH (by positivity)
    have a2 : eta₃ / l ^ 2 = (eta₃ / l) / l := by rw [div_div, sq]
    have a3 : (eta₃ / l) / l ≤ (eta₃ / l) / 11 := div_le_div_of_nonneg_left hu0 (by norm_num) hl
    have a4 := add_div hB eta₃ (l ^ 2)
    rw [mul_div_assoc]
    linarith
  have hηl : 10 * η / (l - 1) ≤ 11 * (eta₃ / l) := by
    rw [div_le_iff₀ hl1]
    have a1 : 11 * (eta₃ / l) * (l - 1) = 11 * eta₃ - 11 * (eta₃ / l) := by field_simp
    have a2 : eta₃ / l ≤ eta₃ / 11 := div_le_div_of_nonneg_left hetaP0 (by norm_num) hl
    rw [a1]; linarith
  have hwe : (wP + eta₃) / l = wP / l + eta₃ / l := add_div _ _ _
  set E1 := hB / l ^ 2 with hE1
  set M1 := 1 + hB / l + Real.logb l hB with hM1
  set cD := (H + 1) / (l - 1) + 1 with hcD
  have hflt0 : 0 ≤ flt := by linarith
  have he1 : e ≤ 32 * E1 + 225 * flt := by linarith
  have he2 : e' ≤ 69 * M1 := by
    have a1 : H' / l ≤ 2 * (hB / l) := by
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (by linarith) hl0.le
    linarith
  have hcD4 : cD ≤ 4 * M1 := by
    have a1 : (H + 1) / (l - 1) ≤ 4 * (hB / l) := by
      rw [div_le_iff₀ hl1]
      have b1 : 4 * (hB / l) * (l - 1) = 4 * hB - 4 * (hB / l) := by field_simp
      have b2 : hB / l ≤ hB / 11 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hl
      rw [b1]; linarith
    rw [hcD]; linarith
  have hM0 : 0 ≤ M1 := by linarith
  have h1 : (n + 1) * r * e ≤ (n + 1) * r * (32 * E1 + 225 * flt) :=
    mul_le_mul_of_nonneg_left he1 (by positivity)
  have h2 : n * m * e' ≤ n * m * (69 * M1) := mul_le_mul_of_nonneg_left he2 (by positivity)
  have h3 : n * r * S ≤ (n + 1) * r * flt := by
    have : S ≤ flt := by linarith
    calc n * r * S ≤ n * r * flt := mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ (n + 1) * r * flt := by
        have q1 : (n + 1) * r * flt = n * r * flt + r * flt := by ring
        have q2 := mul_nonneg hr hflt0
        linarith
  have h4 : n * m * cD ≤ n * m * (4 * M1) := mul_le_mul_of_nonneg_left hcD4 (by positivity)
  have p1 : 0 ≤ (n + 1) * r * E1 := by positivity
  have p2 : 0 ≤ (n + 1) * r * flt := by positivity
  have p3 : 0 ≤ n * m * M1 := by positivity
  linarith

attribute [local instance] nLet_neZero

section Facts

variable {D : D7} (L : SizeData₂ D)

/- English proof (translation)
Unfold `Scale.b`. Apply `Real.one_le_exp` to reduce the goal to its premises. Unfold `Scale.L`. Conclude with `Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _`.
-/
theorem one_le_b : 1 ≤ L.sc.b := by
  unfold Scale.b
  apply Real.one_le_exp
  unfold Scale.L
  exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _

/- English proof (translation)
Unfold `TwistedPlaces.large₂ Scale.L`. Conclude with `Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le`.
-/
theorem Lg_ge_one : 1 ≤ TwistedPlaces.large₂ L := by
  unfold TwistedPlaces.large₂ Scale.L
  exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

/- English proof (translation)
Establish `hx : 0 < L.sc.x` using `by linarith [L.sc.one_lt_alt]`. Establish `hb' : 0 < L.sc.b'`. Unfold `Scale.b' Scale.a Scale.X'`. Use `one_le_b L` as an intermediate fact. Check the signs of the components of the expression.

Establish `hw : 0 ≤ L.sc.w'' D.R.n`. Unfold `Scale.w''`. Check the signs of the components of the expression. Establish `hB : 0 ≤ TwistedPlaces.wB L`. Unfold `TwistedPlaces.wB`.

Use `L.etaSz_pos` as an intermediate fact. Conclude with `le_max_of_le_left (by linarith)`. Unfold `TwistedPlaces.wP`. Check the signs of the components of the expression.
-/
theorem placeWeight_nonneg : 0 ≤ TwistedPlaces.wP L := by
  have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hb' : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := one_le_b L
    positivity
  have hw : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w''
    positivity
  have hB : 0 ≤ TwistedPlaces.wB L := by
    unfold TwistedPlaces.wB
    have := L.etaSz_pos
    exact le_max_of_le_left (by linarith)
  unfold TwistedPlaces.wP
  positivity

/- English proof (translation)
Unfold `TwistedPlaces.hB`. Use `one_le_b L` as an intermediate fact. Use `L.Sc_pos` as an intermediate fact. Use `L.etaSz_pos` as an intermediate fact. Establish `: (0 : ℝ) ≤ D.R.t` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_hB : 1 ≤ TwistedPlaces.hB L := by
  unfold TwistedPlaces.hB
  have := one_le_b L
  have := L.Sc_pos
  have := L.etaSz_pos
  have : (0 : ℝ) ≤ D.R.t := by positivity
  linarith

/- English proof (translation)
Unfold `TwistedPlaces.eta₃ TwistedPlaces.hB`. Use `one_le_b L` as an intermediate fact. Use `L.Sc_pos` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem etaP_le_hB : TwistedPlaces.eta₃ L ≤ TwistedPlaces.hB L := by
  unfold TwistedPlaces.eta₃ TwistedPlaces.hB
  have := one_le_b L
  have := L.Sc_pos
  linarith

end Facts

/- English proof (translation)
Unfold `LiftingTheory.Hmax`. Apply `Finset.sup_le` to reduce the goal to its premises. Introduce `k _`. Establish `: b (k : ZMod n) ≤ Finset.univ.sup b` using `Finset.le_sup (Finset.mem_univ _)`. Unfold `RamifiedCoefficientChains.MiW RamifiedCoefficientChains.hiW RamifiedCoefficientChains.hpar`.

Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem Hmax_le {n : ℕ} [NeZero n] (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) :
    LiftingTheory.Hmax n (RamifiedCoefficientChains.MiW d b S η) (RamifiedCoefficientChains.hiW d b S η) ≤ RamifiedCoefficientChains.hpar n b S + η := by
  unfold LiftingTheory.Hmax
  apply Finset.sup_le
  intro k _
  have : b (k : ZMod n) ≤ Finset.univ.sup b := Finset.le_sup (Finset.mem_univ _)
  unfold RamifiedCoefficientChains.MiW RamifiedCoefficientChains.hiW RamifiedCoefficientChains.hpar
  split_ifs <;> omega

/- English proof (translation)
Unfold `RamifiedCoefficientChains.hpar`. Establish `: Finset.univ.sup sz ≤ b0 + η` using `Finset.sup_le fun a _ => (h a).2`. Use linear arithmetic over natural numbers and integers.
-/
theorem hpar_le_of_thick {n : ℕ} [NeZero n] {b0 η : ℕ} {sz : ZMod n → ℕ} (S : ℕ)
    (h : ∀ a, TruncatedSeriesCountingBounds.Thick b0 η sz a) : RamifiedCoefficientChains.hpar n sz S ≤ b0 + η + S := by
  unfold RamifiedCoefficientChains.hpar
  have : Finset.univ.sup sz ≤ b0 + η := Finset.sup_le fun a _ => (h a).2
  omega

/- English proof (translation)
Introduce `D L P HW F C₂ i r ρ π w hw Cx hG Wd d bd hP04 hP54 hPar h11 hb hbox hC hA`. Introduce `T₁ T₂ F' h2 h1 hF`. Establish `hp : ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p = D.nd.l i` using `(D.loc _).PD_p _`. Establish `hl' : (((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p : ℝ) = (D.nd.l i : ℝ)` using `by rw [hp]`. Establish `hS` using `GlobalTheory.Survey.InertPlacesGoodSet.setCS_of_wordsAT h11 hb hC hA T₁ T₂ F' h2 h1 hF`.

Take `⟨e, he, hcol, -⟩` from `hP04 (D.nd.l i) (D.nbr i w hw).Kw Cx.LL hG d T₁ T₂ F' Wd.sz Wd.S Wd.η Wd.m hS trivial`. Establish `hO` using `(hP54.2.2.2.2.2.2.2.2.2.2.1 (D.nd.l i) (D.nbr i w hw).Kw 1 Cx.LL hG T₁ (RamifiedCoefficientChains.MiW d Wd.sz Wd.S Wd.η) (RamifiedCoefficientChains.hiW d Wd.sz Wd.S Wd.η) hS.2.2.2.2.2.1.1 (RamifiedCoefficientChains.jumpsLet_win _ hS)).1 hS.1`. Establish `hrk : Module.finrank ↥Cx.LL.1 T₂.V = D.R.r`. Take `⟨e, -⟩` from `h2`. Rewrite using `[e.finrank_eq]`.

Simplify using the standard rewrite rules. Establish `hn : nLet i w hw = TwistedPlaces.nLam D w`. Establish `h0 : Loc.K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1` using `inf_eq_left.mpr hb.unram`. Unfold `nLet`. Rewrite using `[h0]`.

Conclude with `hb.deg`. Establish `hnR : ((nLet i w hw : ℕ) : ℝ) = (TwistedPlaces.nLam D w : ℝ)` using `by exact_mod_cast hn`. Take `⟨mm, k, hmm, hk, hle⟩` from `hcol`. Use `⟨mm, k, hmm, hk, hle.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg k))⟩` and prove the remaining obligations. Establish `hK : (rowC C₂).K₁ = 368 ∧ (rowC C₂).K₂ = 2082 ∧ (rowC C₂).K₃ = 22365`.

Apply the tactic sequence `refine ⟨?_, ?_, ?_⟩ <;> simp only [rowC, KillingConditions.RowK.K₁, KillingConditions.RowK.K₂, KillingConditions.RowK.K₃] <;> norm_num`. Rewrite using `[hK.1, hK.2.1, hK.2.2]`. Unfold `RamifiedCoefficientChains.colBd RamifiedCoefficientChains.cD bdCD coreH coreF coreM coreE`. Rewrite using `[hl', hrk, hb.m_eq, hnR]`. Unfold `RamifiedCoefficientChains.eBd RamifiedCoefficientChains.lam at he`.

Rewrite `he`, `hO` using `[hl']`. Establish `hHn` using `Hmax_le d Wd.sz Wd.S Wd.η`. Establish `hth` using `hpar_le_of_thick Wd.S hA.thick`. Establish `hHle : (((RamifiedCoefficientChains.hpar (nLet i w hw) Wd.sz Wd.S + Wd.η : ℕ)) : ℝ) ≤ TwistedPlaces.hB L + TwistedPlaces.eta₃ L`. Establish `a1 : RamifiedCoefficientChains.hpar (nLet i w hw) Wd.sz Wd.S + Wd.η ≤ Wd.b + Wd.η + Wd.S + Wd.η` using `by omega`.

Establish `a2 : (((RamifiedCoefficientChains.hpar (nLet i w hw) Wd.sz Wd.S + Wd.η : ℕ)) : ℝ) ≤ ((Wd.b + Wd.η + Wd.S + Wd.η : ℕ) : ℝ)`. Conclude with `a1` after adjusting the coercions. Move the coercions through the operations in `at a2 ⊢`. Combine the linear relations using `[hb.h_le, hb.η_le]`. Establish `hBb : TwistedPlaces.hB L ≤ 2 * Real.exp (TwistedPlaces.large₂ L)`.

Express the relevant statement in the definitionally equal form `TwistedPlaces.hB L ≤ 2 * L.sc.b`. Unfold `TwistedPlaces.hB`. Unfold `EmbeddingTypeJumps.ParametersPolynomiallyBounded at hPar`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hflt : (TwistedPlaces.wP L + TwistedPlaces.eta₃ L) / (D.nd.l i : ℝ) + L.Sc + TwistedPlaces.large₂ L ≤ flat L bd (D.nd.l i)`.

Unfold `flat`. Establish `h0 : 0 ≤ TwistedPlaces.eta₃ L` using `by have := L.etaSz_pos; unfold TwistedPlaces.eta₃; positivity`. Apply the tactic sequence `split_ifs <;> linarith`. Conclude with `GlobalTheory.RowsThick.colBd_le_row (η := (Wd.η : ℝ)) (H' := ((LiftingTheory.Hmax (nLet i w hw) (RamifiedCoefficientChains.MiW d Wd.sz Wd.S Wd.η) (RamifiedCoefficientChains.hiW d Wd.sz Wd.S Wd.η) : ℕ) : ℝ)) (eta₃ := TwistedPlaces.eta₃ L) (wP := TwistedPlaces.wP L) (Sc := L.Sc) (l …`.
-/
theorem rowL_of_allThick : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : WordDat (nLet i w hw)) (d : ℕ) (bd : Prop), RamifiedCoefficientChains.aux₃ D HW F 25 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → WordBase L HW i r ρ π w hw Cx hG Wd → WordBox L Wd → WordBaseC (HW := HW) ρ π hG Wd → @WordsAT (D.nd.l i) _ (nLet_neZero i w hw) Wd d → RowL i r ρ π w hw Cx (bdCD L bd (D.nd.l i) w (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃) := by
  intro D L P HW F C₂ i r ρ π w hw Cx hG Wd d bd hP04 hP54 hPar h11 hb hbox hC hA
  intro T₁ T₂ F' h2 h1 hF
  have hp : ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p = D.nd.l i := (D.loc _).PD_p _
  have hl' : (((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p : ℝ) = (D.nd.l i : ℝ) := by rw [hp]
  have hS := GlobalTheory.Survey.InertPlacesGoodSet.setCS_of_wordsAT h11 hb hC hA T₁ T₂ F' h2 h1 hF
  obtain ⟨e, he, hcol, -⟩ :=
    hP04 (D.nd.l i) (D.nbr i w hw).Kw Cx.LL hG d T₁ T₂ F' Wd.sz Wd.S Wd.η Wd.m hS trivial
  have hO := (hP54.2.2.2.2.2.2.2.2.2.2.1 (D.nd.l i) (D.nbr i w hw).Kw 1 Cx.LL hG T₁
    (RamifiedCoefficientChains.MiW d Wd.sz Wd.S Wd.η) (RamifiedCoefficientChains.hiW d Wd.sz Wd.S Wd.η) hS.2.2.2.2.2.1.1
    (RamifiedCoefficientChains.jumpsLet_win _ hS)).1 hS.1
  have hrk : Module.finrank ↥Cx.LL.1 T₂.V = D.R.r := by
    obtain ⟨e, -⟩ := h2
    rw [e.finrank_eq]; simp
  have hn : nLet i w hw = TwistedPlaces.nLam D w := by
    have h0 : Loc.K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 := inf_eq_left.mpr hb.unram
    unfold nLet
    rw [h0]
    exact hb.deg
  have hnR : ((nLet i w hw : ℕ) : ℝ) = (TwistedPlaces.nLam D w : ℝ) := by exact_mod_cast hn
  obtain ⟨mm, k, hmm, hk, hle⟩ := hcol
  refine ⟨mm, k, hmm, hk, hle.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg k))⟩
  have hK : (rowC C₂).K₁ = 368 ∧ (rowC C₂).K₂ = 2082 ∧ (rowC C₂).K₃ = 22365 := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [rowC, KillingConditions.RowK.K₁, KillingConditions.RowK.K₂, KillingConditions.RowK.K₃] <;> norm_num
  rw [hK.1, hK.2.1, hK.2.2]
  unfold RamifiedCoefficientChains.colBd RamifiedCoefficientChains.cD bdCD coreH coreF coreM coreE
  rw [hl', hrk, hb.m_eq, hnR]
  unfold RamifiedCoefficientChains.eBd RamifiedCoefficientChains.lam at he
  rw [hl'] at he hO
  have hHn := Hmax_le d Wd.sz Wd.S Wd.η
  have hth := hpar_le_of_thick Wd.S hA.thick
  have hHle : (((RamifiedCoefficientChains.hpar (nLet i w hw) Wd.sz Wd.S + Wd.η : ℕ)) : ℝ) ≤ TwistedPlaces.hB L + TwistedPlaces.eta₃ L := by
    have a1 : RamifiedCoefficientChains.hpar (nLet i w hw) Wd.sz Wd.S + Wd.η ≤ Wd.b + Wd.η + Wd.S + Wd.η := by omega
    have a2 : (((RamifiedCoefficientChains.hpar (nLet i w hw) Wd.sz Wd.S + Wd.η : ℕ)) : ℝ) ≤ ((Wd.b + Wd.η + Wd.S + Wd.η : ℕ) : ℝ) := by
      exact_mod_cast a1
    push_cast at a2 ⊢
    linarith [hb.h_le, hb.η_le]
  have hBb : TwistedPlaces.hB L ≤ 2 * Real.exp (TwistedPlaces.large₂ L) := by
    change TwistedPlaces.hB L ≤ 2 * L.sc.b
    unfold TwistedPlaces.hB
    unfold EmbeddingTypeJumps.ParametersPolynomiallyBounded at hPar
    linarith
  have hflt : (TwistedPlaces.wP L + TwistedPlaces.eta₃ L) / (D.nd.l i : ℝ) + L.Sc + TwistedPlaces.large₂ L ≤ flat L bd (D.nd.l i) := by
    unfold flat
    have h0 : 0 ≤ TwistedPlaces.eta₃ L := by have := L.etaSz_pos; unfold TwistedPlaces.eta₃; positivity
    split_ifs <;> linarith
  exact GlobalTheory.RowsThick.colBd_le_row (η := (Wd.η : ℝ))
    (H' := ((LiftingTheory.Hmax (nLet i w hw) (RamifiedCoefficientChains.MiW d Wd.sz Wd.S Wd.η) (RamifiedCoefficientChains.hiW d Wd.sz Wd.S Wd.η) : ℕ) : ℝ))
    (eta₃ := TwistedPlaces.eta₃ L) (wP := TwistedPlaces.wP L) (Sc := L.Sc) (large₂ := TwistedPlaces.large₂ L)
    (by exact_mod_cast h11) (by positivity) (by positivity) (by positivity) (by positivity) hb.S_le
    (by positivity) hb.η_le (by positivity) hHle (etaP_le_hB L) (one_le_hB L) hBb (Lg_ge_one L)
    (placeWeight_nonneg L) hflt he (by positivity) (by exact_mod_cast hHn) hO

end GlobalTheory.RowsThick
