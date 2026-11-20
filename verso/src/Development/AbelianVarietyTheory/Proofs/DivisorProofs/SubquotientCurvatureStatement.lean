import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovariantSecondFundamentalForm
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionBlocksHermitianFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubbundleCurvatureFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientBundleCurvatureFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingTorsionPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureQuotientSubBlockStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarExtensionFormZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovDelHolExtensionZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcExtensionTraceChernFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtTraceNonnegOfPosFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtTraceWedgeSelfEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubBundleCurvatureRankOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTwoDdcExtTraceStatement

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.SubQuotCurv

/- English proof (translation)
The claim follows from `GlobalTheory.T.connection_blocks_hermitian_frame`.
-/
theorem connBlocks : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U), ConnBlocks H z (fun η => -secondFormAdj H z η) (secondForm H z) :=
  GlobalTheory.T.connection_blocks_hermitian_frame

/- English proof (translation)
The claim follows from `GlobalTheory.T.subbundle_curvature_formula`.
-/
theorem gaussS : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), curv (gramS H) z ξ η = blockSS (H z) (curv H z ξ η) + wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η :=
  GlobalTheory.T.subbundle_curvature_formula

/- English proof (translation)
The claim follows from `GlobalTheory.T.quotient_bundle_curvature_formula`.
-/
theorem gaussQ : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), curv (gramQ H) z ξ η = blockQQ (H z) (curv H z ξ η) + wedgeHolAnti (secondForm H z) (secondFormAdj H z) ξ η :=
  GlobalTheory.T.quotient_bundle_curvature_formula

/- English proof (translation)
The claim follows from `GlobalTheory.T.curvature_off_diagonal_block`.
-/
theorem curvSQ : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), blockSQ (H z) (curv H z ξ η) = covDelAnti (gramQ H) (gramS H) (extForm H) z ξ η :=
  GlobalTheory.T.curvature_off_diagonal_block

/- English proof (translation)
The claim follows from `GlobalTheory.T.curvature_quotient_sub_block`.
-/
theorem curvQS : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), blockQS (curv H z ξ η) = -dbarHol (extFormAdj H) z ξ η :=
  GlobalTheory.T.curvature_quotient_sub_block

/- English proof (translation)
The claim follows from `GlobalTheory.T.dbar_extension_form_zero`.
-/
theorem dbarExt : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (η₁ η₂ : V), dbarAnti (extForm H) z η₁ η₂ = 0 :=
  GlobalTheory.T.dbar_extension_form_zero

/- English proof (translation)
The claim follows from `GlobalTheory.T.cov_del_hol_extension_zero`.
-/
theorem delExtAdj : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ₁ ξ₂ : V), covDelHol (gramS H) (gramQ H) (extFormAdj H) z ξ₁ ξ₂ = 0 :=
  GlobalTheory.T.cov_del_hol_extension_zero

/- English proof (translation)
The claim follows from `GlobalTheory.T.ddc_extension_trace_chern_forms`.
-/
theorem ddcAny : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (hb : ∀ x ∈ U, ExtBlocksAt H x) (ξ₁ η₁ ξ₂ η₂ : V), ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ = chTwo (gramS H) z ξ₁ η₁ ξ₂ η₂ + chTwo (gramQ H) z ξ₁ η₁ ξ₂ η₂ - chTwo H z ξ₁ η₁ ξ₂ η₂ :=
  GlobalTheory.T.ddc_extension_trace_chern_forms

/- English proof (translation)
The claim follows from `GlobalTheory.T.ext_trace_nonneg_of_pos_frame`.
-/
theorem nonneg : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H) (hz : z ∈ U), IsNonnegForm (extTrace H z) :=
  GlobalTheory.T.ext_trace_nonneg_of_pos_frame

/- English proof (translation)
The claim follows from `GlobalTheory.T.ext_trace_wedge_self_eq_zero`.
-/
theorem sqZero : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H) (hz : z ∈ U) (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) (ξ₁ η₁ ξ₂ η₂ : V), wedge (extTrace H z) (extTrace H z) ξ₁ η₁ ξ₂ η₂ = 0 :=
  GlobalTheory.T.ext_trace_wedge_self_eq_zero

/- English proof (translation)
The claim follows from `GlobalTheory.T.sub_bundle_curvature_rank_one`.
-/
theorem line_bundle_curvature_subquotient : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H) (hz : z ∈ U) (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) (hg : ∀ ξ η, curv (gramS H) z ξ η = blockSS (H z) (curv H z ξ η) + wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η) (hc : ∀ ξ η, chernOne H z ξ η = chernOne (gramS H) z ξ η + chernOne (gramQ H) z ξ η) (u : m → ℂ) (hu : u ≠ 0) (ξ η : V), chernOne (gramS H) z ξ η = lineCurv H z (incl m l *ᵥ u) ξ η - extTrace H z ξ η ∧ chernOne (gramQ H) z ξ η = chernOne H z ξ η - lineCurv H z (incl m l *ᵥ u) ξ η + extTrace H z ξ η :=
  GlobalTheory.T.sub_bundle_curvature_rank_one

/- English proof (translation)
The claim follows from `GlobalTheory.T.chern_two_ddc_ext_trace`.
-/
theorem ddcTwo : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) (hc : ∀ ξ η, chernOne H z ξ η = chernOne (gramS H) z ξ η + chernOne (gramQ H) z ξ η) (hd : ∀ ξ₁ η₁ ξ₂ η₂, ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ = chTwo (gramS H) z ξ₁ η₁ ξ₂ η₂ + chTwo (gramQ H) z ξ₁ η₁ ξ₂ η₂ - chTwo H z ξ₁ η₁ ξ₂ η₂) (ξ₁ η₁ ξ₂ η₂ : V), ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ = chernTwo H z ξ₁ η₁ ξ₂ η₂ - wedge (chernOne (gramS H) z) (chernOne (gramQ H) z) ξ₁ η₁ ξ₂ η₂ :=
  GlobalTheory.T.chern_two_ddc_ext_trace

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
  {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}

/- English proof (translation)
Use `⟨fun η η' => ?_, fun c η => ?_, fun ξ ξ' => ?_, fun c ξ => ?_, fun η => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_secondFormAdj h hs hz η, fun ξ => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_secondForm h hz ξ⟩` and prove the remaining obligations. Simplify using `only [secondFormAdj, adj, secondForm, blockQS, conn_add_vec, Matrix.mul_add, Matrix.add_mul, conjTranspose_add]`. Simplify using `only [secondFormAdj, adj, secondForm, blockQS, conn_smul_vec, Matrix.mul_smul, Matrix.smul_mul, conjTranspose_smul, Complex.star_def]`. Simplify using `only [secondForm, blockQS, conn_add_vec, Matrix.mul_add, Matrix.add_mul]`. Simplify using `only [secondForm, blockQS, conn_smul_vec, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem formTypes_secondForm (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det)
    (hz : z ∈ U) : FormTypes (secondFormAdj H) (secondForm H) z := by
  refine ⟨fun η η' => ?_, fun c η => ?_, fun ξ ξ' => ?_, fun c ξ => ?_,
    fun η => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_secondFormAdj h hs hz η, fun ξ => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_secondForm h hz ξ⟩
  · simp only [secondFormAdj, adj, secondForm, blockQS, conn_add_vec, Matrix.mul_add,
      Matrix.add_mul, conjTranspose_add]
  · simp only [secondFormAdj, adj, secondForm, blockQS, conn_smul_vec, Matrix.mul_smul,
      Matrix.smul_mul, conjTranspose_smul, Complex.star_def]
  · simp only [secondForm, blockQS, conn_add_vec, Matrix.mul_add, Matrix.add_mul]
  · simp only [secondForm, blockQS, conn_smul_vec, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun ξ _ => ⟨eq_conn_of_compatible (h.isUnit z hz), fun e => e ▸ conn_transpose_mul (h.isUnit z hz) ξ⟩, formTypes_secondForm h hs hz, fun ξ s q => form_secondForm (h.herm z hz) (hs z hz) ξ s q, connBlocks h hs hz, gaussS h hs hz, gaussQ h hs hz⟩`.
-/
theorem subQuotAt (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) :
    SubQuotAt H z :=
  ⟨fun ξ _ => ⟨eq_conn_of_compatible (h.isUnit z hz),
      fun e => e ▸ conn_transpose_mul (h.isUnit z hz) ξ⟩,
    formTypes_secondForm h hs hz, fun ξ s q => form_secondForm (h.herm z hz) (hs z hz) ξ s q,
    connBlocks h hs hz, gaussS h hs hz, gaussQ h hs hz⟩

/- English proof (translation)
The claim follows from `funext fun η => extForm_eq_neg_secondFormAdj (h.one hz) (h.eventually_herm hz) (h.isUnit z hz) (hs z hz) η`.
-/
theorem extForm_eq (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) :
    extForm H z = fun η => -secondFormAdj H z η :=
  funext fun η => extForm_eq_neg_secondFormAdj (h.one hz) (h.eventually_herm hz) (h.isUnit z hz)
    (hs z hz) η

/- English proof (translation)
The claim follows from `funext fun ξ => extFormAdj_eq_neg_secondForm (h.one hz) (h.eventually_herm hz) (h.isUnit z hz) (hs z hz) ξ`.
-/
theorem extFormAdj_eq (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det)
    (hz : z ∈ U) : extFormAdj H z = fun ξ => -secondForm H z ξ :=
  funext fun ξ => extFormAdj_eq_neg_secondForm (h.one hz) (h.eventually_herm hz) (h.isUnit z hz)
    (hs z hz) ξ

/- English proof (translation)
Establish `hh` using `h.herm z hz`. Establish `eβ` using `extForm_eq h hs hz`. Establish `eγ` using `extFormAdj_eq h hs hz`. Establish `ft` using `formTypes_secondForm h hs hz`. Establish `w1 : ∀ ξ η, wedgeAntiHol (extForm H z) (extFormAdj H z) ξ η = wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η` using `fun ξ η => by`.

Simplify using `only [wedgeAntiHol, eβ, eγ, Matrix.neg_mul, Matrix.mul_neg, neg_neg]`. Establish `w2 : ∀ ξ η, wedgeHolAnti (extFormAdj H z) (extForm H z) ξ η = wedgeHolAnti (secondForm H z) (secondFormAdj H z) ξ η` using `fun ξ η => by`. Simplify using `only [wedgeHolAnti, eβ, eγ, Matrix.neg_mul, Matrix.mul_neg, neg_neg]`. Use `⟨⟨fun η η' => ?_, fun c η => ?_, fun ξ ξ' => ?_, fun c ξ => ?_, fun η => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_extForm h hs hz η, fun ξ => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_extFormAdj h hs hz ξ⟩, …` and prove the remaining obligations. Rewrite using `[eβ]`.

Simplify using `only [ft.1 η η', neg_add]`. Rewrite using `[eβ]`. Simplify using `only [ft.2.1 c η, smul_neg]`. Rewrite using `[eγ]`. Simplify using `only [ft.2.2.1 ξ ξ', neg_add]`.

Rewrite using `[eγ]`. Simplify using `only [ft.2.2.2.1 c ξ, smul_neg]`. Establish `e2 : (fun ξ => -extFormAdj H z ξ) = secondForm H z`. Rewrite using `[eγ]`. Use function extensionality and compare the values at `ξ`.

Simplify using the standard rewrite rules. Rewrite using `[eβ, e2]`. Conclude with `connBlocks h hs hz`. Rewrite using `[w1, gaussS h hs hz]`. Normalize the expressions using the abelian group laws.

Rewrite using `[w2, gaussQ h hs hz]`. Normalize the expressions using the abelian group laws.
-/
theorem extBlocksAt (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) :
    ExtBlocksAt H z := by
  have hh := h.herm z hz
  have eβ := extForm_eq h hs hz
  have eγ := extFormAdj_eq h hs hz
  have ft := formTypes_secondForm h hs hz
  have w1 : ∀ ξ η, wedgeAntiHol (extForm H z) (extFormAdj H z) ξ η =
      wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η := fun ξ η => by
    simp only [wedgeAntiHol, eβ, eγ, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  have w2 : ∀ ξ η, wedgeHolAnti (extFormAdj H z) (extForm H z) ξ η =
      wedgeHolAnti (secondForm H z) (secondFormAdj H z) ξ η := fun ξ η => by
    simp only [wedgeHolAnti, eβ, eγ, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  refine ⟨⟨fun η η' => ?_, fun c η => ?_, fun ξ ξ' => ?_, fun c ξ => ?_,
      fun η => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_extForm h hs hz η, fun ξ => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_extFormAdj h hs hz ξ⟩,
    fun ξ q s => form_adj (isHermitian_quotGram hh) (isUnit_det_quotGram (h.isUnit z hz) (hs z hz))
      (isHermitian_subGram hh) _ q s, ?_, fun ξ η => ?_, curvSQ h hs hz, curvQS h hs hz,
    fun ξ η => ?_, dbarExt h hs hz, delExtAdj h hs hz⟩
  · rw [eβ]; simp only [ft.1 η η', neg_add]
  · rw [eβ]; simp only [ft.2.1 c η, smul_neg]
  · rw [eγ]; simp only [ft.2.2.1 ξ ξ', neg_add]
  · rw [eγ]; simp only [ft.2.2.2.1 c ξ, smul_neg]
  · have e2 : (fun ξ => -extFormAdj H z ξ) = secondForm H z := by
      rw [eγ]; funext ξ; simp
    rw [eβ, e2]; exact connBlocks h hs hz
  · rw [w1, gaussS h hs hz]; abel
  · rw [w2, gaussQ h hs hz]; abel

/- English proof (translation)
Rewrite using `[chernOne, chernOne, chernOne, GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.trace_eq_blocks (H z), gaussS h hs hz, gaussQ h hs hz]`. Simplify using `only [wedgeAntiHol, wedgeHolAnti, trace_add, trace_neg, trace_mul_comm (secondForm H z ξ)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chernOne_add (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det)
    (hz : z ∈ U) (ξ η : V) :
    chernOne H z ξ η = chernOne (gramS H) z ξ η + chernOne (gramQ H) z ξ η := by
  rw [chernOne, chernOne, chernOne, GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.trace_eq_blocks (H z), gaussS h hs hz, gaussQ h hs hz]
  simp only [wedgeAntiHol, wedgeHolAnti, trace_add, trace_neg,
    trace_mul_comm (secondForm H z ξ)]
  ring

/- English proof (translation)
Introduce `V _ _ _ _ _ m l _ _ _ _ U H`. Use `⟨fun h hs => ⟨h.sub hs, h.quot hs, fun z hz => subQuotAt h hs hz⟩, fun hp => ?_⟩` and prove the remaining obligations. Establish `h` using `hp.isHermFrame`. Establish `hs : ∀ z ∈ U, IsUnit (subGram (H z)).det` using `fun z hz => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.isUnit_sub hp z hz`. Use `⟨hp.sub, hp.quot, fun z hz => ⟨fun ξ s => ?_, extBlocksAt h hs hz, nonneg hp hz, chernOne_add h hs hz, ddcAny h hs hz (fun x hx => extBlocksAt h hs hx)⟩, fun hm hl z hz => ⟨nonneg hp hz, sqZero hp hz hm hl, fun u hu ξ η => line_bundle_curvature_subquotient hp hz hm hl (gaussS h h …` and prove the remaining obligations.

Establish `hh` using `h.herm z hz`. Simplify using `only [wedgeAntiHol, gramS, gramQ]`. Rewrite using `[form_secondFormAdj_mul hh (hs z hz) ξ s, form_self (posDef_quotGram (hp.posDef z hz)).posSemidef]`.
-/
theorem subQuotCurvature : SubQuotCurvature := by
  intro V _ _ _ _ _ m l _ _ _ _ U H
  refine ⟨fun h hs => ⟨h.sub hs, h.quot hs, fun z hz => subQuotAt h hs hz⟩, fun hp => ?_⟩
  have h := hp.isHermFrame
  have hs : ∀ z ∈ U, IsUnit (subGram (H z)).det := fun z hz => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.isUnit_sub hp z hz
  refine ⟨hp.sub, hp.quot, fun z hz => ⟨fun ξ s => ?_, extBlocksAt h hs hz,
    nonneg hp hz, chernOne_add h hs hz, ddcAny h hs hz (fun x hx => extBlocksAt h hs hx)⟩,
    fun hm hl z hz => ⟨nonneg hp hz, sqZero hp hz hm hl,
      fun u hu ξ η => line_bundle_curvature_subquotient hp hz hm hl (gaussS h hs hz) (chernOne_add h hs hz) u hu ξ η,
      ddcTwo hm hl (chernOne_add h hs hz) (ddcAny h hs hz (fun x hx => extBlocksAt h hs hx))⟩⟩
  have hh := h.herm z hz
  simp only [wedgeAntiHol, gramS, gramQ]
  rw [form_secondFormAdj_mul hh (hs z hz) ξ s, form_self (posDef_quotGram (hp.posDef z hz)).posSemidef]

end GlobalTheory.SubQuotCurv
