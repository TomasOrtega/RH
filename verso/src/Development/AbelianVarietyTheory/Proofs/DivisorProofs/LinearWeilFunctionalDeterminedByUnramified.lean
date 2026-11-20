import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinearRightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDeterminantOpenImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalUnitaryActionPreservesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLinearWittModelNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqRightTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqSchwartzPosFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationOneUnitsNhdsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddHaarMatrixSpaceStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.WeilLinW

/- English proof (translation)
Introduce `u _`. Simplify using `[mat]`.
-/
theorem one_mem_UAt' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (Y : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ Y.J) ∈ UAt σ Y ev := by
  intro u _
  simp [mat]

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hv t ι hι β₀ hβ`. Establish `hloc` using `(GlobalTheory.T.theta_action_exists hP) F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ (GlobalTheory.ThK.Check.isPair_of_isTriple hTr).1 v`. Take `⟨φ₀, hφ₀, hιφ₀⟩` from `hι.bij.surjOn (GlobalTheory.KSplit.indicator_intM_mem_SB (k := Fv F v) (R := Fin a) (D := Fin (a + a')))`. Establish `h0 : ι φ₀ 0 ≠ 0`. Rewrite using `[hιφ₀]`.

Establish `: (0 : Matrix (Fin a) (Fin (a + a')) (Fv F v)) ∈ GlobalTheory.KSplit.intM (Fv F v) (Fin a) (Fin (a + a'))` using `fun i j => by simp`. Simplify using `[Set.indicator_of_mem this]`. Establish `omA_eq : ∀ (h' : GL (Fin (a + a')) (Fv F v)) (Φ : Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ) Y, GlobalTheory.SplitFlip.omA 1 β₀ 1 h' Φ Y = ((β₀ (GlobalTheory.SplitFlip.gdet h') : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h') (-(a : ℂ) / 2)) * Φ (Y * (GlobalTh …`. Introduce `h' Φ Y`. Simplify using `[GlobalTheory.SplitFlip.omA]`.

Establish `gdet_eq : ∀ (h : UA σ G.W.J) (h' : GL (Fin (a + a')) (Fv F v)), (mat h).map (piW t) = h'.1 → ((GlobalTheory.SplitFlip.gdet h' : (Fv F v)ˣ) : Fv F v) = ((mat h).map (piW t)).det`. Introduce `h h' e`. Rewrite using `[e]`. Both sides reduce to the same expression. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Take `⟨U, hU, hUφ⟩` from `hloc.2.2 φ₀ hφ₀`. Establish `hUW : {h : UA σ G.W.J | ((1 : UA σ G.V.J), h) ∈ U} ∈ 𝓝 (1 : UA σ G.W.J)`. Establish `hc : Continuous (fun h : UA σ G.W.J => ((1 : UA σ G.V.J), h))` using `continuous_const.prodMk continuous_id`. Conclude with `hc.continuousAt.preimage_mem_nhds hU`. Take `⟨V, hV, hVx⟩` from `GlobalTheory.T.unitary_determinant_open_image F E σ B a a' G X om om' hTr v hv t _ hUW`.

Unfold `GlobalTheory.SmGL.IsSmoothChar`. Apply `Subgroup.isOpen_of_mem_nhds (g := 1)` to reduce the goal to its premises. Use `filter_upwards [hV, GlobalTheory.T.valuation_one_units_nhds (k := Fv F v)] with x hx hxv`. Take `⟨h, hh, hhU, hdet⟩` from `hVx x hx`. Take `⟨h', hh', hrel⟩` from `hβ h hh`.

Establish `hA` using `hUφ (1, h) hhU (one_mem_UAt' σ G.V _) hh`. Establish `e` using `congrFun (hrel φ₀ hφ₀ φ₀ hφ₀ hA) 0`. Rewrite `e` using `[omA_eq]`. Establish `hg : GlobalTheory.SplitFlip.gdet h' = x` using `Units.ext ((gdet_eq h h' hh').trans hdet)`. Rewrite `e` using `[hg, Matrix.zero_mul, GlobalTheory.SplitFlip.apow_of_valuation_eq_one hxv, mul_one]`.

Establish `e2 : (β₀ x : ℂ) = 1`. Use `mul_right_cancel₀ h0 (e.symm.trans (one_mul _).symm)` as an intermediate fact. Conclude with `this`. Use `show β₀ x = 1`. Conclude with `Units.ext e2`.

Introduce `x`. Establish `ha : 0 < a + a'` using `by have := hTr.geo.lt; omega`. Set `i0 : Fin (a + a')` to `⟨0, ha⟩`. Set `D : (Fv F v)ˣ → Matrix (Fin (a + a')) (Fin (a + a')) (Fv F v)` to `fun y => Matrix.diagonal (Function.update (1 : Fin (a + a') → Fv F v) i0 (y : Fv F v))`. Establish `hD : ∀ y z : (Fv F v)ˣ, D y * D z = D (y * z)`.

Introduce `y z`. Simplify using `only [D, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = i0`.

Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne hi]`. Establish `hD1 : D 1 = 1`. Simplify using `only [D]`.

Rewrite using `[← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = i0`. Substitute `hi` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne hi]`. Set `h' : GL (Fin (a + a')) (Fv F v)` to `⟨D x, D x⁻¹, by rw [hD, mul_inv_cancel, hD1], by rw [hD, inv_mul_cancel, hD1]⟩`. Establish `hg : GlobalTheory.SplitFlip.gdet h' = x`. Apply `Units.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `(D x).det = (x : Fv F v)`. Simplify using `only [D, Matrix.det_diagonal]`. Rewrite using `[Finset.prod_update_of_mem (Finset.mem_univ _)]`. Simplify using the standard rewrite rules. Take `⟨h, hh, hht⟩` from `GlobalTheory.T.local_unitary_group_surjects_general_linear_right hP F E σ B a a' G X om om' hTr v hv t h'`.

Take `⟨φ₁, ⟨hφ₁, hA⟩, -⟩` from `hloc.1 1 (one_mem_UAt' σ G.V _) h hh φ₀ hφ₀`. Take `⟨h'', hh'', hrel⟩` from `hβ h hh`. Establish `: h'' = h'` using `Units.ext (hh''.symm.trans hht)`. Substitute `this` using the available equality. Establish `e` using `hrel φ₀ hφ₀ φ₁ hφ₁ hA`.

Take `⟨ν, hν⟩` from `GlobalTheory.T.exists_add_haar_matrix_space (k := Fv F v) (a := a) (d := a + a')`. Establish `hu` using `GlobalTheory.T.triple_local_unitary_action_preserves hP F E σ B a a' G X om om' hTr v h hh φ₀ hφ₀ φ₁ hφ₁ hA`. Establish `hl` using `GlobalTheory.T.triple_linear_witt_model_nonvanishing hP F E σ B a a' G X om om' hTr v hv t ι hι φ₀ hφ₀ φ₁ hφ₁ hu ν hν`. Rewrite `hl` using `[e]`. Rewrite `hl` using `[omA_eq, hg]`.

Use `set c : ℂ := (β₀ x : ℂ) * GlobalTheory.SplitFlip.apow x (-(a : ℂ) / 2) with hcdef`. Establish `hc : ∀ Y : Matrix (Fin a) (Fin (a + a')) (Fv F v), ‖c * ι φ₀ (Y * (GlobalTheory.SplitFlip.invT h').1)‖ₑ ^ 2 = ‖c‖ₑ ^ 2 * ‖ι φ₀ (Y * (GlobalTheory.SplitFlip.invT h').1)‖ₑ ^ 2`. Introduce `Y`. Rewrite using `[enorm_mul, mul_pow]`. Rewrite `hl` using `[hc]`.

Rewrite `hl` using `[lintegral_const_mul' _ _ (by simp [enorm_eq_nnnorm]), GlobalTheory.T.lintegral_norm_sq_right_translate (ι φ₀) h' ν hν, hg]`. Take `⟨hn0, hntop⟩` from `GlobalTheory.T.lintegral_norm_sq_schwartz_pos_finite (ι φ₀) (hι.bij.mapsTo hφ₀) (fun hz => h0 (by simp [hz])) ν hν`. Rewrite `hl` using `[← mul_assoc]`. Establish `h1 : ‖c‖ₑ ^ 2 * ‖GlobalTheory.SplitFlip.apow x (a : ℂ)‖ₑ = 1` using `(ENNReal.mul_left_inj hn0 hntop).mp (hl.trans (one_mul _).symm)`. Use `clear_value c`.

Establish `h2 : ‖c‖ₑ ^ 2 * ‖GlobalTheory.SplitFlip.apow x (a : ℂ)‖ₑ = ‖(β₀ x : ℂ)‖ₑ ^ 2`. Establish `: c * c * GlobalTheory.SplitFlip.apow x (a : ℂ) = (β₀ x : ℂ) * (β₀ x : ℂ)`. Rewrite using `[hcdef]`. Establish `e3 : GlobalTheory.SplitFlip.apow x (-(a : ℂ) / 2) * GlobalTheory.SplitFlip.apow x (-(a : ℂ) / 2) * GlobalTheory.SplitFlip.apow x (a : ℂ) = 1`. Rewrite using `[← GlobalTheory.SplitFlip.apow_add, ← GlobalTheory.SplitFlip.apow_add]`.

Establish `: -(a : ℂ) / 2 + -(a : ℂ) / 2 + a = 0` using `by ring`. Rewrite using `[this, GlobalTheory.SplitFlip.apow_zero]`. Take the linear combination `((β₀ x : ℂ) * (β₀ x : ℂ)) * e3`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[enorm_mul, enorm_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = ‖(β₀ x : ℂ) * (β₀ x : ℂ)‖ₑ := by rw [this]`. Use `_ = ‖(β₀ x : ℂ)‖ₑ ^ 2 := by rw [enorm_mul]; ring`. Rewrite `h1` using `[h2]`. Establish `h3 : ‖(β₀ x : ℂ)‖₊ = 1`.

Rewrite `h1` using `[enorm_eq_nnnorm, ← ENNReal.coe_pow, ENNReal.coe_eq_one]`. Conclude with `(pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 h1`. Conclude with `congrArg NNReal.toReal h3`.
-/
theorem charW_smooth_unitary : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → ∀ β₀ : (Fv F v)ˣ →* ℂˣ, (∀ h ∈ UAt σ G.W (evFin F v), ∃ h' : GL (Fin (a + a')) (Fv F v), (mat h).map (piW t) = h'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA 1 β₀ 1 h' (ι φ)) →
    GlobalTheory.SmGL.IsSmoothChar β₀ ∧ GlobalTheory.SmGL.IsUnitaryChar β₀ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hv t ι hι β₀ hβ
  have hloc := (GlobalTheory.T.theta_action_exists hP) F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hTr).1 v
  obtain ⟨φ₀, hφ₀, hιφ₀⟩ := hι.bij.surjOn (GlobalTheory.KSplit.indicator_intM_mem_SB (k := Fv F v) (R := Fin a) (D := Fin (a + a')))
  have h0 : ι φ₀ 0 ≠ 0 := by
    rw [hιφ₀]
    have : (0 : Matrix (Fin a) (Fin (a + a')) (Fv F v)) ∈ GlobalTheory.KSplit.intM (Fv F v) (Fin a) (Fin (a + a')) :=
      fun i j => by simp
    simp [Set.indicator_of_mem this]
  have omA_eq : ∀ (h' : GL (Fin (a + a')) (Fv F v)) (Φ : Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ) Y,
      GlobalTheory.SplitFlip.omA 1 β₀ 1 h' Φ Y = ((β₀ (GlobalTheory.SplitFlip.gdet h') : ℂ) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h') (-(a : ℂ) / 2)) * Φ (Y * (GlobalTheory.SplitFlip.invT h').1) := by
    intro h' Φ Y
    simp [GlobalTheory.SplitFlip.omA]
  have gdet_eq : ∀ (h : UA σ G.W.J) (h' : GL (Fin (a + a')) (Fv F v)), (mat h).map (piW t) = h'.1 →
      ((GlobalTheory.SplitFlip.gdet h' : (Fv F v)ˣ) : Fv F v) = ((mat h).map (piW t)).det := by
    intro h h' e
    rw [e]; rfl
  refine ⟨?_, ?_⟩
  · obtain ⟨U, hU, hUφ⟩ := hloc.2.2 φ₀ hφ₀
    have hUW : {h : UA σ G.W.J | ((1 : UA σ G.V.J), h) ∈ U} ∈ 𝓝 (1 : UA σ G.W.J) := by
      have hc : Continuous (fun h : UA σ G.W.J => ((1 : UA σ G.V.J), h)) := continuous_const.prodMk continuous_id
      exact hc.continuousAt.preimage_mem_nhds hU
    obtain ⟨V, hV, hVx⟩ := GlobalTheory.T.unitary_determinant_open_image F E σ B a a' G X om om' hTr v hv t _ hUW
    unfold GlobalTheory.SmGL.IsSmoothChar
    apply Subgroup.isOpen_of_mem_nhds (g := 1)
    filter_upwards [hV, GlobalTheory.T.valuation_one_units_nhds (k := Fv F v)] with x hx hxv
    obtain ⟨h, hh, hhU, hdet⟩ := hVx x hx
    obtain ⟨h', hh', hrel⟩ := hβ h hh
    have hA := hUφ (1, h) hhU (one_mem_UAt' σ G.V _) hh
    have e := congrFun (hrel φ₀ hφ₀ φ₀ hφ₀ hA) 0
    rw [omA_eq] at e
    have hg : GlobalTheory.SplitFlip.gdet h' = x := Units.ext ((gdet_eq h h' hh').trans hdet)
    rw [hg, Matrix.zero_mul, GlobalTheory.SplitFlip.apow_of_valuation_eq_one hxv, mul_one] at e
    have e2 : (β₀ x : ℂ) = 1 := by
      have := mul_right_cancel₀ h0 (e.symm.trans (one_mul _).symm)
      exact this
    show β₀ x = 1
    exact Units.ext e2
  · intro x
    have ha : 0 < a + a' := by have := hTr.geo.lt; omega
    let i0 : Fin (a + a') := ⟨0, ha⟩
    let D : (Fv F v)ˣ → Matrix (Fin (a + a')) (Fin (a + a')) (Fv F v) := fun y =>
      Matrix.diagonal (Function.update (1 : Fin (a + a') → Fv F v) i0 (y : Fv F v))
    have hD : ∀ y z : (Fv F v)ˣ, D y * D z = D (y * z) := by
      intro y z
      simp only [D, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      by_cases hi : i = i0
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    have hD1 : D 1 = 1 := by
      simp only [D]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      by_cases hi : i = i0
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    let h' : GL (Fin (a + a')) (Fv F v) :=
      ⟨D x, D x⁻¹, by rw [hD, mul_inv_cancel, hD1], by rw [hD, inv_mul_cancel, hD1]⟩
    have hg : GlobalTheory.SplitFlip.gdet h' = x := by
      apply Units.ext
      change (D x).det = (x : Fv F v)
      simp only [D, Matrix.det_diagonal]
      rw [Finset.prod_update_of_mem (Finset.mem_univ _)]
      simp
    obtain ⟨h, hh, hht⟩ := GlobalTheory.T.local_unitary_group_surjects_general_linear_right hP F E σ B a a' G X om om' hTr v hv t h'
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc.1 1 (one_mem_UAt' σ G.V _) h hh φ₀ hφ₀
    obtain ⟨h'', hh'', hrel⟩ := hβ h hh
    have : h'' = h' := Units.ext (hh''.symm.trans hht)
    subst this
    have e := hrel φ₀ hφ₀ φ₁ hφ₁ hA
    obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_add_haar_matrix_space (k := Fv F v) (a := a) (d := a + a')
    have hu := GlobalTheory.T.triple_local_unitary_action_preserves hP F E σ B a a' G X om om' hTr v h hh φ₀ hφ₀ φ₁ hφ₁ hA
    have hl := GlobalTheory.T.triple_linear_witt_model_nonvanishing hP F E σ B a a' G X om om' hTr v hv t ι hι φ₀ hφ₀ φ₁ hφ₁ hu ν hν
    rw [e] at hl
    simp_rw [omA_eq, hg] at hl
    set c : ℂ := (β₀ x : ℂ) * GlobalTheory.SplitFlip.apow x (-(a : ℂ) / 2) with hcdef
    have hc : ∀ Y : Matrix (Fin a) (Fin (a + a')) (Fv F v), ‖c * ι φ₀ (Y * (GlobalTheory.SplitFlip.invT h').1)‖ₑ ^ 2 =
        ‖c‖ₑ ^ 2 * ‖ι φ₀ (Y * (GlobalTheory.SplitFlip.invT h').1)‖ₑ ^ 2 := by
      intro Y; rw [enorm_mul, mul_pow]
    simp_rw [hc] at hl
    rw [lintegral_const_mul' _ _ (by simp [enorm_eq_nnnorm]), GlobalTheory.T.lintegral_norm_sq_right_translate (ι φ₀) h' ν hν, hg] at hl
    obtain ⟨hn0, hntop⟩ := GlobalTheory.T.lintegral_norm_sq_schwartz_pos_finite (ι φ₀) (hι.bij.mapsTo hφ₀) (fun hz => h0 (by simp [hz])) ν hν
    rw [← mul_assoc] at hl
    have h1 : ‖c‖ₑ ^ 2 * ‖GlobalTheory.SplitFlip.apow x (a : ℂ)‖ₑ = 1 :=
      (ENNReal.mul_left_inj hn0 hntop).mp (hl.trans (one_mul _).symm)
    clear_value c
    have h2 : ‖c‖ₑ ^ 2 * ‖GlobalTheory.SplitFlip.apow x (a : ℂ)‖ₑ = ‖(β₀ x : ℂ)‖ₑ ^ 2 := by
      have : c * c * GlobalTheory.SplitFlip.apow x (a : ℂ) = (β₀ x : ℂ) * (β₀ x : ℂ) := by
        rw [hcdef]
        have e3 : GlobalTheory.SplitFlip.apow x (-(a : ℂ) / 2) * GlobalTheory.SplitFlip.apow x (-(a : ℂ) / 2) * GlobalTheory.SplitFlip.apow x (a : ℂ) = 1 := by
          rw [← GlobalTheory.SplitFlip.apow_add, ← GlobalTheory.SplitFlip.apow_add]
          have : -(a : ℂ) / 2 + -(a : ℂ) / 2 + a = 0 := by ring
          rw [this, GlobalTheory.SplitFlip.apow_zero]
        linear_combination ((β₀ x : ℂ) * (β₀ x : ℂ)) * e3
      calc ‖c‖ₑ ^ 2 * ‖GlobalTheory.SplitFlip.apow x (a : ℂ)‖ₑ = ‖c * c * GlobalTheory.SplitFlip.apow x (a : ℂ)‖ₑ := by
            rw [enorm_mul, enorm_mul]; ring
        _ = ‖(β₀ x : ℂ) * (β₀ x : ℂ)‖ₑ := by rw [this]
        _ = ‖(β₀ x : ℂ)‖ₑ ^ 2 := by rw [enorm_mul]; ring
    rw [h2] at h1
    have h3 : ‖(β₀ x : ℂ)‖₊ = 1 := by
      rw [enorm_eq_nnnorm, ← ENNReal.coe_pow, ENNReal.coe_eq_one] at h1
      exact (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 h1
    exact congrArg NNReal.toReal h3

end GlobalTheory.WeilLinW
