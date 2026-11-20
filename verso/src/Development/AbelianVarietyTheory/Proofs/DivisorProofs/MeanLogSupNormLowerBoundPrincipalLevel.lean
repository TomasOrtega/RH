import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundOfCoreLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SupNormDefiniteOnCuspFormsGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualDataTransvectionPrincipalLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWeightSpreadLeExponentNormAddStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory

/- English proof (translation)
Substitute `hX` using the available equality. Introduce `v hv hvv b hb hbi`. Take `⟨γ, hγ, hγ'⟩` from `htr v hv hvv b hb hbi`. Conclude with `⟨γ, hγ, hχ γ hγ, hγ'⟩`.
-/
theorem transv_of_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Xx : DataX E r) (Y : Data E r)
    (hX : Xx.toData = Y) (la : Wt Y.Ψ r) (M : ℝ) (hχ : ∀ γ ∈ Y.Γ, Y.χ la γ = 1)
    (htr : ∀ v ∈ Xx.L', herm Xx.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ Xx.Γ, ∀ τ : Xx.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = Xx.flowMat v τ ((M : ℂ) * τ.1 b)) :
    ∀ v ∈ Xx.L', herm Y.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ Y.Γ, Y.χ la γ = 1 ∧
        ∀ τ : Y.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = Y.flowMat v τ ((M : ℂ) * τ.1 b) := by
  subst hX
  intro v hv hvv b hb hbi
  obtain ⟨γ, hγ, hγ'⟩ := htr v hv hvv b hb hbi
  exact ⟨γ, hγ, hχ γ hγ, hγ'⟩

/- English proof (translation)
Introduce `D j H Dw l Xo c U dict h _ χ hχ a n ha F hF hval hF0`. Establish `hσ₀ : GoodEmb c c.F.val.toRingHom` using `rfl`. Establish `hr : 0 < D.R.r`. Use `D.R.m_add_three_le_k` as an intermediate fact. Unfold `Ranks.r`.

Use linear arithmetic over natural numbers and integers. Establish `hU` using `h.unf c.F.val.toRingHom hσ₀`. Establish `hpq : Dw.p + Dw.q = D.R.r` using `hU.1.symm`. Establish `hSD : SupDef Xo c U` using `(Formalism.L2.PjFree.supDef_ofPj U).1 (GlobalTheory.supNorm_definite_on_cusp D.host.E H Dw l Xo c D.R.r (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (h.unf σ hσ)))`. Use `set σ₀ := c.F.val.toRingHom with hσdef`.

Establish `hhol : rdU (U σ₀) F ∈ holSub (U σ₀).X (laU (U σ₀) a n)` using `((mem_cusp _ _ _ _ _ F).1 hF).2 σ₀ hσ₀`. Establish `hSS` using `Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds (U σ₀).X (laU (U σ₀) a n) hhol`. Establish `hfin : supE (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F) ≠ ⊤` using `supE_cusp_ne_top hσ₀ hF`. Establish `hpos : 0 < supN (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F)`. Break down `(ENNReal.toReal_nonneg : 0 ≤ (supE (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F)).toReal).lt_or_eq with hlt | heq` into its components or cases.

Conclude with `hlt`. Conclude with `absurd (hSD a n ha σ₀ hσ₀ F hF heq.symm) hF0`. Take `⟨k, z0, hz0, hlt⟩` from `Formalism.L2.Pj.abelian₂.half_max (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F) hpos hfin`. Establish `hhalf : ∀ x ∈ ((U σ₀).X k).dom, ((U σ₀).X k).pnorm (laU (U σ₀) a n k) (rdU (U σ₀) F k) x ≤ 2 * ((U σ₀).X k).pnorm (laU (U σ₀) a n k) (rdU (U σ₀) F k) z0` using `fun x hx => (Formalism.L2.Pj.abelian₂.pnorm_le_supN _ _ _ hfin k x hx).trans hlt.le`. Establish `hposz : 0 < ((U σ₀).X k).pnorm (laU (U σ₀) a n k) (rdU (U σ₀) F k) z0` using `by linarith`.

Take `⟨Xx, hX, hXg, hΛ, -, M, hM, hMk, htr⟩` from `GlobalTheory.T.exists_selfDual_data_transvection_principal_level D j H Dw l Xo c U dict h σ₀ hσ₀ k`. Establish `hsp` using `GlobalTheory.T.sum_weightSpread_le_exponentNorm_add D j H Dw l Xo c U dict h σ₀ hσ₀ a n k`. Use `set s : ℝ := ((absA Dw a : ℕ) : ℝ) with hs`. Use `set t : ℝ := ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) with ht`. Establish `hs0 : 0 ≤ s` using `Nat.cast_nonneg _`.

Establish `ht0 : 0 ≤ t` using `Nat.cast_nonneg _`. Establish `hw : (∑ τ, ((U σ₀).X k).spread (laU (U σ₀) a n k) τ) ≤ s + t + 1` using `by linarith`. Establish `hw1 : (1 : ℝ) ≤ s + t + 1` using `by linarith`. Take `⟨x, lam, hx, hLB, hPx⟩` from `Formalism.L2.Pj.abelian₂.cm_frame_of_eq Xx ((U σ₀).X k) hX _ _ z0 M (s + t + 1) (hSS k) hM hw hw1 hr (transv_of_eq Xx _ hX _ M (h.chiTriv σ₀ hσ₀ a n ha k) htr) hz0 hhalf hposz`. Establish `hp0 : Xx.p0 = Dw.q` using `(congrArg Data.p0 hX).trans (hU.2.1 k).1`.

Establish `heps : epStar M (fdeg D.host.E) (s + t + 1) Xx.k0 = epsLev D.host.E D.host.d l.M (s + t + 1)`. Unfold `epsLev epStar`. Use `congr 2`. Rewrite using `[← hMk]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hLa : frameBasisRadius D.R.r Xx.p0 (fdeg D.host.E) (dE D.host.E) (Real.sqrt (epStar M (fdeg D.host.E) (s + t + 1) Xx.k0)) (3 * frameRadius (s + t + 1) D.R.r / 5) = cmLen D.host.E D.R.r Dw.q D.host.d l.M (s + t + 1)`. Unfold `cmLen`. Rewrite using `[hp0, heps]`. Rewrite `hLB` using `[hLa]`. Establish `hf1 : 1 ≤ fdeg D.host.E`.

Establish `h2` using `finrank_eq_two_mul_half_degree (E := D.host.E)`. Establish `h3 : 0 < Module.finrank ℚ D.host.E` using `Module.finrank_pos`. Establish `h4 : Module.finrank ℚ D.host.E = 2 * fdeg D.host.E` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers. Establish `hd1` using `GlobalTheory.WtSizes.one_le_dE D`.

Establish `hlog : Real.log (M * Xx.k0) ≤ 19 * |Real.log (M * Xx.k0)| + 3 + Real.log (dE D.host.E)`. Use `Real.log_nonneg hd1` as an intermediate fact. Use `le_abs_self (Real.log (M * Xx.k0))` as an intermediate fact. Use `abs_nonneg (Real.log (M * Xx.k0))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨C0, hC0, hroom⟩` from `GlobalTheory.T.exists_constant_cmEvaluation_fits_room`. Establish `hLa1 : 1 ≤ cmLen D.host.E D.R.r Dw.q D.host.d l.M (s + t + 1)`. Rewrite using `[← hLa]`. Conclude with `(hroom (fdeg D.host.E) D.R.r Xx.p0 (dE D.host.E) |Real.log (M * Xx.k0)| 0 M Xx.k0 (s + t + 1) hf1 hr Xx.p0_le hd1 (abs_nonneg _) hM Xx.minWeight_pos hw1 hlog).1`. Establish `hSpos : ∀ σ, 0 < supC Xo c U (xiR D) (goodOf c σ) a n F` using `fun σ => by`.

Unfold `supC`. Use `mul_pos (lieFac_pos _ _ _) (lt_of_le_of_ne (supN_nonneg _ _ _) fun h0 => hF0 ?_)` and prove the remaining obligations. Conclude with `hSD a n ha _ (Formalism.L2.Pj.goodEmb_goodOf (c := c) σ) F hF h0.symm`. Establish `h5` using `GlobalTheory.T.meanLogSupNorm_lowerBound_cmFrame_nonvanishing D.host.E H Dw l Xo c D.R.r U (xiR D) h.unf h.xiAbs (by omega) χ hχ a n ha F hF hval hSpos k ⟨x, hx⟩ Xx hX D.host.AA (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D) hΛ _ lam hLa1 hLB hPx`. Use `le_trans ?_ h5` and prove the remaining obligations.

Establish `et : ((Module.finrank ℚ D.host.E / 2 * D.R.r : ℕ) : ℝ) * n = t`. Rewrite using `[ht]`. Simplify using `only [fdeg, Nat.cast_mul]`. Rewrite using `[et]`. Unfold `lamSup`.

Apply `le_of_eq` to reduce the goal to its premises. Simplify using `only [absA] at hs`. Rewrite using `[← hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lamSup_of_laws : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ F ∈ cusp Xo c U a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → F ≠ 0 → -lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) ≤ (∑ σ : c.F →+* ℂ, Real.log (supC Xo c U (xiR D) (goodOf c σ) a n F)) / (Module.finrank ℚ c.F : ℝ) := by
  classical
  intro D j H Dw l Xo c U dict h _ χ hχ a n ha F hF hval hF0
  have hσ₀ : GoodEmb c c.F.val.toRingHom := rfl
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hU := h.unf c.F.val.toRingHom hσ₀
  have hpq : Dw.p + Dw.q = D.R.r := hU.1.symm
  have hSD : SupDef Xo c U :=
    (Formalism.L2.PjFree.supDef_ofPj U).1 (GlobalTheory.supNorm_definite_on_cusp D.host.E H Dw l Xo c D.R.r
      (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (h.unf σ hσ)))
  set σ₀ := c.F.val.toRingHom with hσdef
  have hhol : rdU (U σ₀) F ∈ holSub (U σ₀).X (laU (U σ₀) a n) := ((mem_cusp _ _ _ _ _ F).1 hF).2 σ₀ hσ₀
  have hSS := Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds (U σ₀).X (laU (U σ₀) a n) hhol
  have hfin : supE (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F) ≠ ⊤ := supE_cusp_ne_top hσ₀ hF
  have hpos : 0 < supN (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F) := by
    rcases (ENNReal.toReal_nonneg : 0 ≤ (supE (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F)).toReal).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (hSD a n ha σ₀ hσ₀ F hF heq.symm) hF0
  obtain ⟨k, z0, hz0, hlt⟩ := Formalism.L2.Pj.abelian₂.half_max (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F) hpos hfin
  have hhalf : ∀ x ∈ ((U σ₀).X k).dom, ((U σ₀).X k).pnorm (laU (U σ₀) a n k) (rdU (U σ₀) F k) x ≤
      2 * ((U σ₀).X k).pnorm (laU (U σ₀) a n k) (rdU (U σ₀) F k) z0 :=
    fun x hx => (Formalism.L2.Pj.abelian₂.pnorm_le_supN _ _ _ hfin k x hx).trans hlt.le
  have hposz : 0 < ((U σ₀).X k).pnorm (laU (U σ₀) a n k) (rdU (U σ₀) F k) z0 := by linarith
  obtain ⟨Xx, hX, hXg, hΛ, -, M, hM, hMk, htr⟩ := GlobalTheory.T.exists_selfDual_data_transvection_principal_level D j H Dw l Xo c U dict h σ₀ hσ₀ k
  have hsp := GlobalTheory.T.sum_weightSpread_le_exponentNorm_add D j H Dw l Xo c U dict h σ₀ hσ₀ a n k
  set s : ℝ := ((absA Dw a : ℕ) : ℝ) with hs
  set t : ℝ := ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) with ht
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have ht0 : 0 ≤ t := Nat.cast_nonneg _
  have hw : (∑ τ, ((U σ₀).X k).spread (laU (U σ₀) a n k) τ) ≤ s + t + 1 := by linarith
  have hw1 : (1 : ℝ) ≤ s + t + 1 := by linarith
  obtain ⟨x, lam, hx, hLB, hPx⟩ := Formalism.L2.Pj.abelian₂.cm_frame_of_eq Xx ((U σ₀).X k) hX _ _ z0 M (s + t + 1) (hSS k) hM
    hw hw1 hr (transv_of_eq Xx _ hX _ M (h.chiTriv σ₀ hσ₀ a n ha k) htr) hz0 hhalf hposz
  have hp0 : Xx.p0 = Dw.q := (congrArg Data.p0 hX).trans (hU.2.1 k).1
  have heps : epStar M (fdeg D.host.E) (s + t + 1) Xx.k0 = epsLev D.host.E D.host.d l.M (s + t + 1) := by
    unfold epsLev epStar
    congr 2
    rw [← hMk]
    ring
  have hLa : frameBasisRadius D.R.r Xx.p0 (fdeg D.host.E) (dE D.host.E) (Real.sqrt (epStar M (fdeg D.host.E) (s + t + 1) Xx.k0))
      (3 * frameRadius (s + t + 1) D.R.r / 5) = cmLen D.host.E D.R.r Dw.q D.host.d l.M (s + t + 1) := by
    unfold cmLen
    rw [hp0, heps]
  rw [hLa] at hLB
  have hf1 : 1 ≤ fdeg D.host.E := by
    have h2 := finrank_eq_two_mul_half_degree (E := D.host.E)
    have h3 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    have h4 : Module.finrank ℚ D.host.E = 2 * fdeg D.host.E := by exact_mod_cast h2
    omega
  have hd1 := GlobalTheory.WtSizes.one_le_dE D
  have hlog : Real.log (M * Xx.k0) ≤ 19 * |Real.log (M * Xx.k0)| + 3 + Real.log (dE D.host.E) := by
    have := Real.log_nonneg hd1
    have := le_abs_self (Real.log (M * Xx.k0))
    have := abs_nonneg (Real.log (M * Xx.k0))
    linarith
  obtain ⟨C0, hC0, hroom⟩ := GlobalTheory.T.exists_constant_cmEvaluation_fits_room
  have hLa1 : 1 ≤ cmLen D.host.E D.R.r Dw.q D.host.d l.M (s + t + 1) := by
    rw [← hLa]
    exact (hroom (fdeg D.host.E) D.R.r Xx.p0 (dE D.host.E) |Real.log (M * Xx.k0)| 0 M Xx.k0 (s + t + 1) hf1 hr
      Xx.p0_le hd1 (abs_nonneg _) hM Xx.minWeight_pos hw1 hlog).1
  have hSpos : ∀ σ, 0 < supC Xo c U (xiR D) (goodOf c σ) a n F := fun σ => by
    unfold supC
    refine mul_pos (lieFac_pos _ _ _) (lt_of_le_of_ne (supN_nonneg _ _ _) fun h0 => hF0 ?_)
    exact hSD a n ha _ (Formalism.L2.Pj.goodEmb_goodOf (c := c) σ) F hF h0.symm
  have h5 := GlobalTheory.T.meanLogSupNorm_lowerBound_cmFrame_nonvanishing D.host.E H Dw l Xo c D.R.r U (xiR D) h.unf h.xiAbs (by omega) χ hχ a n ha F hF hval hSpos
    k ⟨x, hx⟩ Xx hX D.host.AA (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D) hΛ _ lam hLa1 hLB hPx
  refine le_trans ?_ h5
  have et : ((Module.finrank ℚ D.host.E / 2 * D.R.r : ℕ) : ℝ) * n = t := by
    rw [ht]
    simp only [fdeg, Nat.cast_mul]
  rw [et]
  unfold lamSup
  apply le_of_eq
  simp only [absA] at hs
  rw [← hs]
  ring

end GlobalTheory
