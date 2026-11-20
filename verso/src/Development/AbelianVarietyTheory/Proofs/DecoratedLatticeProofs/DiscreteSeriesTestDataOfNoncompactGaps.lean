import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsStarProjectionOfIsOrthProjOnto
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePhLocOfIntegrablePh
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFdegFdegOfLowest
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hf`.
-/
private theorem isHCParam_comp_fin_cast {n m : ℕ} (h : n = m) {f : Fin m → ℝ} (hf : Formalism.QuantumDeterminants.IsHCParam f) :
    Formalism.QuantumDeterminants.IsHCParam (fun i : Fin n => f (Fin.cast h i)) := by
  subst h
  exact hf

/- English proof (translation)
Rewrite using `[show X.B.lam v = _ from funext (X.lam_eq v)]`. Conclude with `isHCParam_comp_fin_cast X.n_eq (Formalism.MainNotions.S.Inh.aut_isHCParam_lamS D.R (D.hc (X.pl v)))`.
-/
theorem isHCParam_lam_of_setting {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : InfinitePlace X.B.I.F) :
    Formalism.QuantumDeterminants.IsHCParam (X.B.lam v) := by
  rw [show X.B.lam v = _ from funext (X.lam_eq v)]
  exact isHCParam_comp_fin_cast X.n_eq (Formalism.MainNotions.S.Inh.aut_isHCParam_lamS D.R (D.hc (X.pl v)))

/- English proof (translation)
Rewrite using `[Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]`. Establish `h1 : ∀ a : Fin n, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1`. Introduce `a`. Apply the tactic sequence `cases ε a <;> simp`. Simplify using `only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]`.
-/
private theorem card_filter_true_add_card_filter_false {n : ℕ} (ε : Fin n → Bool) :
    (Finset.univ.filter fun a : Fin n => ε a = true).card +
      (Finset.univ.filter fun a : Fin n => ε a = false).card = n := by
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have h1 : ∀ a : Fin n, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a
    cases ε a <;> simp
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/- English proof (translation)
Establish `h1 : GlobalTheory.Count.rkR ε ≤ (Finset.univ.filter fun a : Fin n => ε a = true).card` using `min_le_left _ _`. Establish `h2 : GlobalTheory.Count.rkR ε ≤ (Finset.univ.filter fun a : Fin n => ε a = false).card` using `min_le_right _ _`. Establish `h3` using `card_filter_true_add_card_filter_false ε`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_mul_rkR_le {n : ℕ} (ε : Fin n → Bool) : 2 * GlobalTheory.Count.rkR ε ≤ n := by
  have h1 : GlobalTheory.Count.rkR ε ≤ (Finset.univ.filter fun a : Fin n => ε a = true).card := min_le_left _ _
  have h2 : GlobalTheory.Count.rkR ε ≤ (Finset.univ.filter fun a : Fin n => ε a = false).card := min_le_right _ _
  have h3 := card_filter_true_add_card_filter_false ε
  omega

/- English proof (translation)
Break down `Nat.eq_zero_or_pos q with hq | hq` into its components or cases. Substitute `hq` using the available equality. Rewrite using `[Nat.cast_zero, Real.zero_rpow (by norm_num)]`. Check the signs of the components of the expression. Establish `h1 : (1 : ℝ) ≤ q` using `by exact_mod_cast hq`.

Combine the equalities or inequalities in the displayed calculation.
-/
private theorem natCast_rpow_three_halves_le_sq (q : ℕ) : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (q : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]
    positivity
  · have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    calc (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (q : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = (q : ℝ) ^ 2 := Real.rpow_two _

/- English proof (translation)
Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Break down `Nat.eq_zero_or_pos q with hq | hq` into its components or cases. Substitute `hq` using the available equality. Rewrite using `[Nat.cast_zero, Real.zero_rpow (by norm_num), mul_zero]`. Check the signs of the components of the expression.

Establish `hn2 : (2 : ℝ) ≤ n` using `by exact_mod_cast (by omega : 2 ≤ n)`. Establish `hq2 : 2 * (q : ℝ) ≤ n` using `by exact_mod_cast h`. Establish `hq0 : (0 : ℝ) ≤ q` using `Nat.cast_nonneg q`. Establish `hsq : 4 * (q : ℝ) ^ 2 ≤ (n : ℝ) ^ 2` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left (show (30 : ℝ) ≤ 100 * n by linarith) (pow_nonneg hn0 3)]`.
-/
private theorem mul_rpow_three_halves_le_pow_four (q n : ℕ) (h : 2 * q ≤ n) :
    120 * (n : ℝ) * ((q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (n : ℝ) ^ 4 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    rw [Nat.cast_zero, Real.zero_rpow (by norm_num), mul_zero]
    positivity
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    have hq2 : 2 * (q : ℝ) ≤ n := by exact_mod_cast h
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hsq : 4 * (q : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    calc 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (n : ℝ) * (q : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (natCast_rpow_three_halves_le_sq q) (by positivity)
      _ ≤ 30 * (n : ℝ) ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hsq hn0]
      _ ≤ 100 * (n : ℝ) ^ 4 := by
          nlinarith [mul_le_mul_of_nonneg_left (show (30 : ℝ) ≤ 100 * n by linarith) (pow_nonneg hn0 3)]

/- English proof (translation)
The claim follows from `mul_rpow_three_halves_le_pow_four _ _ (two_mul_rkR_le ε)`.
-/
theorem rkR_bound {n : ℕ} (ε : Fin n → Bool) :
    120 * (n : ℝ) * ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (n : ℝ) ^ 4 :=
  mul_rpow_three_halves_le_pow_four _ _ (two_mul_rkR_le ε)

/- English proof (translation)
Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Break down `Nat.eq_zero_or_pos q with hq | hq` into its components or cases. Substitute `hq` using the available equality. Rewrite using `[Nat.cast_zero, Real.sqrt_zero, mul_zero]`. Check the signs of the components of the expression.

Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hn2 : (2 : ℝ) ≤ n` using `by exact_mod_cast (by omega : 2 ≤ n)`. Establish `hq2 : 2 * (q : ℝ) ≤ n` using `by exact_mod_cast h`. Establish `hs : Real.sqrt (q : ℝ) ≤ q`. Establish `h'` using `Real.sqrt_le_sqrt (show (q : ℝ) ≤ (q : ℝ) ^ 2 by nlinarith)`.

Rewrite `h'` using `[Real.sqrt_sq (by linarith)]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left (show (20 : ℝ) ≤ 100 * n by linarith) (pow_nonneg hn0 3)]`.
-/
private theorem mul_sq_mul_sqrt_le_pow_four (q n : ℕ) (h : 2 * q ≤ n) :
    40 * (n : ℝ) ^ 2 * Real.sqrt (q : ℝ) ≤ 100 * (n : ℝ) ^ 4 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    rw [Nat.cast_zero, Real.sqrt_zero, mul_zero]
    positivity
  · have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    have hq2 : 2 * (q : ℝ) ≤ n := by exact_mod_cast h
    have hs : Real.sqrt (q : ℝ) ≤ q := by
      have h' := Real.sqrt_le_sqrt (show (q : ℝ) ≤ (q : ℝ) ^ 2 by nlinarith)
      rwa [Real.sqrt_sq (by linarith)] at h'
    calc 40 * (n : ℝ) ^ 2 * Real.sqrt (q : ℝ) ≤ 40 * (n : ℝ) ^ 2 * q :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ 20 * (n : ℝ) ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hq2 (sq_nonneg (n : ℝ))]
      _ ≤ 100 * (n : ℝ) ^ 4 := by
          nlinarith [mul_le_mul_of_nonneg_left (show (20 : ℝ) ≤ 100 * n by linarith) (pow_nonneg hn0 3)]

/- English proof (translation)
The claim follows from `mul_sq_mul_sqrt_le_pow_four _ _ (two_mul_rkR_le ε)`.
-/
theorem rkR_bound_sqrt {n : ℕ} (ε : Fin n → Bool) :
    40 * (n : ℝ) ^ 2 * Real.sqrt (GlobalTheory.Count.rkR ε) ≤ 100 * (n : ℝ) ^ 4 :=
  mul_sq_mul_sqrt_le_pow_four _ _ (two_mul_rkR_le ε)

/- English proof (translation)
Introduce `D X hg`. Establish `hDS : GlobalTheory.Count.IsDSData X.B X.dv` using `fun v => ⟨isHCParam_lam_of_setting X v, X.ds v, X.low v, GlobalTheory.LowestVectorDegree.isFdeg_fdegOf_lowest D X v⟩`. Establish `hb : ∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (D.R.r : ℝ) ^ 4`. Introduce `v`. Establish `e : (X.B.I.n : ℝ) = (D.R.r : ℝ)` using `by exact_mod_cast X.n_eq`.

Combine the equalities or inequalities in the displayed calculation. Establish `hL : GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4)` using `GlobalTheory.Dec.locDec_of_decGap_gapGe (GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap) X.B X.dv _ hDS hg hb`. Establish `hI : Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I)` using `(GlobalTheory.Dec.ProjCuspGap.projector_rank_cuspidal X.B X.dv _ hDS hg hb).1`. Establish `hH : GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4)`. Unfold `GlobalTheory.Dec.HBig`.

Introduce `v`. Establish `e : (X.B.I.n : ℝ) = (D.R.r : ℝ)` using `by exact_mod_cast X.n_eq`. Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨hDS, hL, hH, hb, hI, GlobalTheory.ProdFactor.integrable_phLoc_of_integrable_ph D X hI⟩`.
-/
theorem seeData_of_gap : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Count.IsDSData X.B X.dv ∧ GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) ∧ GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) ∧ (∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (D.R.r : ℝ) ^ 4) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)) := by
  intro D X hg
  have hDS : GlobalTheory.Count.IsDSData X.B X.dv := fun v =>
    ⟨isHCParam_lam_of_setting X v, X.ds v, X.low v, GlobalTheory.LowestVectorDegree.isFdeg_fdegOf_lowest D X v⟩
  have hb : ∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      100 * (D.R.r : ℝ) ^ 4 := by
    intro v
    have e : (X.B.I.n : ℝ) = (D.R.r : ℝ) := by exact_mod_cast X.n_eq
    calc _ ≤ 100 * (X.B.I.n : ℝ) ^ 4 := rkR_bound (X.B.I.ε v)
      _ = 100 * (D.R.r : ℝ) ^ 4 := by rw [e]
  have hL : GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) :=
    GlobalTheory.Dec.locDec_of_decGap_gapGe (GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap)
      X.B X.dv _ hDS hg hb
  have hI : Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) :=
    (GlobalTheory.Dec.ProjCuspGap.projector_rank_cuspidal X.B X.dv _ hDS hg hb).1
  have hH : GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) := by
    unfold GlobalTheory.Dec.HBig
    intro v
    have e : (X.B.I.n : ℝ) = (D.R.r : ℝ) := by exact_mod_cast X.n_eq
    calc _ ≤ 100 * (X.B.I.n : ℝ) ^ 4 := rkR_bound_sqrt (X.B.I.ε v)
      _ = 100 * (D.R.r : ℝ) ^ 4 := by rw [e]
  exact ⟨hDS, hL, hH, hb, hI, GlobalTheory.ProdFactor.integrable_phLoc_of_integrable_ph D X hI⟩

end GlobalTheory.Core.Mi
