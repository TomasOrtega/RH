import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfL
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvariantChartSetLeMulFundamentalSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHormanderPeakOrthonormalFrameL2BoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareL2InequalityFundamentalSetStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

/- English proof (translation)
Take `⟨CH, hCH, hH⟩` from `GlobalTheory.T.exists_hormanderPeak_orthonormalFrame_l2Bound`. Take `⟨CS, hCS, hS⟩` from `GlobalTheory.T.poincare_l2_inequality_fundamental_set`. Use `⟨CH + CS + 1, by linarith, ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ r X la x hp0 hp0r hx hgap hpair hinj x0 FF hx0 hFF`. Take `⟨σ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`.

Establish `hΨ : ∃ τ0 : X.Ψ, True`. Distinguish the cases in `hσ : σ ∈ X.Ψ`. Conclude with `⟨⟨σ, hσ⟩, trivial⟩`. Conclude with `⟨⟨ComplexEmbedding.conjugate σ, by`. Assume the negation of the conclusion as `h`.

Conclude with `hσ ((X.cmType σ).2 h)⟩, trivial⟩`. Take `⟨τ0, -⟩` from `hΨ`. Establish `hcard : (1 : ℝ) ≤ X.Ψ.card`. Conclude with `Finset.card_pos.mpr ⟨τ0.1, τ0.2⟩` after adjusting the coercions. Establish `hr : (1 : ℝ) ≤ r` using `by exact_mod_cast (show 1 ≤ r by omega)`.

Establish `hN : (1 : ℝ) ≤ (X.Ψ.card : ℝ) * r` using `by nlinarith`. Establish `hN8 : (1 : ℝ) ≤ ((X.Ψ.card : ℝ) * r) ^ 8` using `one_le_pow₀ hN`. Establish `hS0 : 0 ≤ ∑ τ, ∑ a, |(la τ a : ℝ)|` using `by positivity`. Establish `hgapH : ∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → CH * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ a : ℝ) - la τ b` using `fun τ a b h1 h2 => le_trans (by nlinarith) (hgap τ a b h1 h2)`. Establish `hpairH : ∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → CH * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ b : ℝ) - la τ a` using `fun τ a b h1 h2 => le_trans (by nlinarith) (hpair τ a b h1 h2)`.

Take `⟨F, P0, hFd, hP0, hagree, hP0x, hvan, hInAt, hbound⟩` from `hH E r X la x hp0 hp0r hx hgapH hpairH hinj`. Establish `hInv : IsInvFn X (fun _ : Frame X.Ψ r => (0 : ℝ))` using `fun _ _ _ _ _ _ => rfl`. Establish `hW` using `IW.metricW_of GlobalTheory.NormFactor.nfacRmul_holds GlobalTheory.NormFactor.nfacLact_holds ortho_holds lu_holds X la (fun _ => 0) hInv (fun _ _ => contDiffOn_const) ⟨0, fun _ _ => le_rfl⟩`. Establish `hbb : 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1` using `by linarith`. Establish `hpoin` using `poin_holds r X x hx (GlobalTheory.ClosedDiscontinuity.propDisc_closed r X) la _ _ hW.1 hW.2 hbb F P0 hFd hInAt hP0 hagree`.

Establish `hbdd : X.IsBddSec la (poin X la P0)` using `hpoin.2.1`. Establish `hSS : poin X la P0 ∈ X.SS la`. Use `cuspStatement_holds r X la τ0 hp0 hp0r (fun i j h1 h2 => ?_) (fun i0 i1 h1 h2 => ?_) _ hbdd` and prove the remaining obligations. Use `hgap τ0 i j h1 h2` as an intermediate fact. Establish `h3 : ((la τ0 j : ℤ) : ℝ) ≤ la τ0 i` using `by nlinarith`.

Conclude with `h3` after adjusting the coercions. Use `hpair τ0 i0 i1 h1 h2` as an intermediate fact. Establish `h3 : ((la τ0 i0 : ℤ) : ℝ) < la τ0 i1` using `by nlinarith`. Conclude with `h3` after adjusting the coercions. Establish `hchi1 : X.χ la 1 = 1`.

Establish `h1` using `X.χ_mul la 1 X.Γ.one_mem 1 X.Γ.one_mem`. Rewrite `h1` using `[one_mul]`. Establish `h2` using `IC.chi_ne_zero X la X.Γ.one_mem`. Establish `h3 : X.χ la 1 * (X.χ la 1 - 1) = 0` using `by linear_combination -h1`. Break down `mul_eq_zero.1 h3 with h | h` into its components or cases.

Conclude with `absurd h h2`. Take the linear combination `h`. Establish `hPx : poin X la P0 x = 1`. Rewrite using `[IC.poin_single X la P0 x X.Γ.one_mem hvan, IW.lact_one X, hP0x, hchi1]`. Simplify using the standard rewrite rules.

Establish `hpn : X.pnorm la (poin X la P0) x = 1`. Rewrite using `[IC.pnorm_orth X la _ hx, hPx, norm_one]`. Use `⟨poin X la P0, hSS, by rw [hPx]; exact one_ne_zero, ?_⟩` and prove the remaining obligations. Establish `hA : MeasurableSet (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x)` using `Metric.isOpen_ball.measurableSet.inter ((IW.isOpen_dom X).preimage (IW.cpt_diff X x).continuous).measurableSet`. Establish `hvol : muF X x (Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x) ≤ muF X x0 FF`.

Establish `h` using `GlobalTheory.Unfold.lintegral_chart_le_mul_fundSet E r X x0 x FF (Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x) 1 (fun _ => 1) hx0 hx hFF hA Set.inter_subset_right measurable_const (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (by`. Establish `hsub : {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x, ∃ z' ∈ Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x, ∃ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR …`. Introduce and unpack `γ ⟨hγ, z, hz, z', hz', b, hb, he⟩`. Establish `h1 : ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2)` using `le_of_lt (by simpa using hz.1)`. Establish `h2 : ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2)` using `le_of_lt (by simpa using hz'.1)`.

Conclude with `hinj γ hγ z z' h1 h2 b hb he`. Use `Set.encard_le_encard hsub` as an intermediate fact. Rewrite `this` using `[Set.encard_singleton]`. Conclude with `this)` after adjusting the coercions. Simplify `h` using `[setLIntegral_one]`.

Establish `hSb` using `hS E r X la x x0 FF F P0 hp0 hp0r hx hx0 hFF hinj hFd hP0 hagree`. Rewrite using `[hpn, one_pow, ENNReal.ofReal_one, one_mul]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hSb.trans (mul_le_mul' le_rfl (hbound.trans (mul_le_mul' le_rfl hvol)))`. Use `_ = ENNReal.ofReal (Real.exp (-((CH + CS + 1) * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))) * Real.exp (CS * ((X.Ψ.card : ℝ) * r) ^ 8) * Real.exp (CH * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))) * muF X x0 FF := by`.

Rewrite using `[ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ 1 * muF X x0 FF := by gcongr`. Rewrite using `[← Real.exp_add, ← Real.exp_add, ENNReal.ofReal_le_one, Real.exp_le_one_iff]`. Use the polynomial consequences of the given equalities and inequalities.

Use `_ = muF X x0 FF := one_mul _`.
-/
theorem GlobalTheory.PeakThick.peak : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ b : ℝ) - la τ a) → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ∀ (x0 : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X))), ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet X x0 FF → ∃ P ∈ X.SS la, P x ≠ 0 ∧ ENNReal.ofReal (Real.exp (-(C * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8)))) * ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la P (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) ≤ ENNReal.ofReal (X.pnorm la P x ^ 2) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0 FF := by
  obtain ⟨CH, hCH, hH⟩ := GlobalTheory.T.exists_hormanderPeak_orthonormalFrame_l2Bound
  obtain ⟨CS, hCS, hS⟩ := GlobalTheory.T.poincare_l2_inequality_fundamental_set
  refine ⟨CH + CS + 1, by linarith, ?_⟩
  intro E _ _ _ r X la x hp0 hp0r hx hgap hpair hinj x0 FF hx0 hFF
  classical
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hΨ : ∃ τ0 : X.Ψ, True := by
    by_cases hσ : σ ∈ X.Ψ
    · exact ⟨⟨σ, hσ⟩, trivial⟩
    · exact ⟨⟨ComplexEmbedding.conjugate σ, by
        by_contra h
        exact hσ ((X.cmType σ).2 h)⟩, trivial⟩
  obtain ⟨τ0, -⟩ := hΨ
  have hcard : (1 : ℝ) ≤ X.Ψ.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨τ0.1, τ0.2⟩
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hN : (1 : ℝ) ≤ (X.Ψ.card : ℝ) * r := by nlinarith
  have hN8 : (1 : ℝ) ≤ ((X.Ψ.card : ℝ) * r) ^ 8 := one_le_pow₀ hN
  have hS0 : 0 ≤ ∑ τ, ∑ a, |(la τ a : ℝ)| := by positivity
  have hgapH : ∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 →
      CH * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ a : ℝ) - la τ b := fun τ a b h1 h2 =>
    le_trans (by nlinarith) (hgap τ a b h1 h2)
  have hpairH : ∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 →
      CH * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ b : ℝ) - la τ a := fun τ a b h1 h2 =>
    le_trans (by nlinarith) (hpair τ a b h1 h2)
  obtain ⟨F, P0, hFd, hP0, hagree, hP0x, hvan, hInAt, hbound⟩ :=
    hH E r X la x hp0 hp0r hx hgapH hpairH hinj
  have hInv : IsInvFn X (fun _ : Frame X.Ψ r => (0 : ℝ)) := fun _ _ _ _ _ _ => rfl
  have hW := IW.metricW_of GlobalTheory.NormFactor.nfacRmul_holds GlobalTheory.NormFactor.nfacLact_holds ortho_holds
    lu_holds X la (fun _ => 0) hInv (fun _ _ => contDiffOn_const) ⟨0, fun _ _ => le_rfl⟩
  have hbb : 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1 := by linarith
  have hpoin := poin_holds r X x hx (GlobalTheory.ClosedDiscontinuity.propDisc_closed r X) la _ _ hW.1 hW.2
    hbb F P0 hFd hInAt hP0 hagree
  have hbdd : X.IsBddSec la (poin X la P0) := hpoin.2.1
  have hSS : poin X la P0 ∈ X.SS la := by
    refine cuspStatement_holds r X la τ0 hp0 hp0r (fun i j h1 h2 => ?_) (fun i0 i1 h1 h2 => ?_) _ hbdd
    · have := hgap τ0 i j h1 h2
      have h3 : ((la τ0 j : ℤ) : ℝ) ≤ la τ0 i := by nlinarith
      exact_mod_cast h3
    · have := hpair τ0 i0 i1 h1 h2
      have h3 : ((la τ0 i0 : ℤ) : ℝ) < la τ0 i1 := by nlinarith
      exact_mod_cast h3
  have hchi1 : X.χ la 1 = 1 := by
    have h1 := X.χ_mul la 1 X.Γ.one_mem 1 X.Γ.one_mem
    rw [one_mul] at h1
    have h2 := IC.chi_ne_zero X la X.Γ.one_mem
    have h3 : X.χ la 1 * (X.χ la 1 - 1) = 0 := by linear_combination -h1
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h h2
    · linear_combination h
  have hPx : poin X la P0 x = 1 := by
    rw [IC.poin_single X la P0 x X.Γ.one_mem hvan, IW.lact_one X, hP0x, hchi1]
    simp
  have hpn : X.pnorm la (poin X la P0) x = 1 := by
    rw [IC.pnorm_orth X la _ hx, hPx, norm_one]
  refine ⟨poin X la P0, hSS, by rw [hPx]; exact one_ne_zero, ?_⟩

  have hA : MeasurableSet (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x) :=
    Metric.isOpen_ball.measurableSet.inter
      ((IW.isOpen_dom X).preimage (IW.cpt_diff X x).continuous).measurableSet
  have hvol : muF X x (Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x) ≤ muF X x0 FF := by
    have h := GlobalTheory.Unfold.lintegral_chart_le_mul_fundSet E r X x0 x FF
      (Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x) 1 (fun _ => 1) hx0 hx hFF hA
      Set.inter_subset_right measurable_const (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (by
        have hsub : {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x,
            ∃ z' ∈ Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x, ∃ b ∈ Bor X.Ψ r,
              lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b} ⊆ {1} := by
          rintro γ ⟨hγ, z, hz, z', hz', b, hb, he⟩
          have h1 : ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) := le_of_lt (by simpa using hz.1)
          have h2 : ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) := le_of_lt (by simpa using hz'.1)
          exact hinj γ hγ z z' h1 h2 b hb he
        have := Set.encard_le_encard hsub
        rw [Set.encard_singleton] at this
        exact_mod_cast this)
    simpa [setLIntegral_one] using h
  have hSb := hS E r X la x x0 FF F P0 hp0 hp0r hx hx0 hFF hinj hFd hP0 hagree
  rw [hpn, one_pow, ENNReal.ofReal_one, one_mul]
  calc ENNReal.ofReal (Real.exp (-((CH + CS + 1) * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))))
        * ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(muF X x0)
      ≤ ENNReal.ofReal (Real.exp (-((CH + CS + 1) * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))))
        * (ENNReal.ofReal (Real.exp (CS * ((X.Ψ.card : ℝ) * r) ^ 8)) *
          (ENNReal.ofReal (Real.exp (CH * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))) * muF X x0 FF)) := by
        gcongr
        exact hSb.trans (mul_le_mul' le_rfl (hbound.trans (mul_le_mul' le_rfl hvol)))
    _ = ENNReal.ofReal (Real.exp (-((CH + CS + 1) * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8)))
          * Real.exp (CS * ((X.Ψ.card : ℝ) * r) ^ 8)
          * Real.exp (CH * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))) * muF X x0 FF := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        ring
    _ ≤ 1 * muF X x0 FF := by
        gcongr
        rw [← Real.exp_add, ← Real.exp_add, ENNReal.ofReal_le_one, Real.exp_le_one_iff]
        nlinarith
    _ = muF X x0 FF := one_mul _
