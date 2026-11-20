import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesOnEqModel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsProductCuspFormNeZeroArchSupNormBounds
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.CuspAndSupCLeOfBounded
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsRunBound
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsEvenSecEvRNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OrthonormalFramesBoundedOfDefinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupAtUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.Frames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalarCuspFormIndefiniteUnitaryShimuraStatement

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.ScalarCusp

/- English proof (translation)
Take `⟨R, hR⟩` from `GlobalTheory.orthonormal_frames_bounded_of_definite r X hp`. Set `K : Set (Frame X.Ψ r)` to `{x | X.IsOrtho x}`. Establish `hKd : K ⊆ X.dom` using `fun x hx => PIW.FdPA.orthonormal_domain r X x hx`. Establish `hKc : IsClosed K`. Establish `e : K = ⋂ τ : X.Ψ, {x : Frame X.Ψ r | gram τ.1 X.Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)}`.

Use extensionality with `x`. Simplify using `[K, Data.IsOrtho]`. Rewrite using `[e]`. Use `isClosed_iInter fun τ => isClosed_eq ?_ continuous_const` and prove the remaining obligations. Unfold `gram hermC col mat`.

Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply]`. Use `fun_prop`. Establish `hKb : Bornology.IsBounded K`. Rewrite using `[Metric.isBounded_iff_subset_closedBall 0]`.

Use `⟨max R 0, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_closedBall_zero_iff]`. Use `(pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun τ => ?_` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun a => ?_` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun b => ?_` and prove the remaining obligations.

Conclude with `(hR x hx τ a b).trans (le_max_left _ _)`. Take `⟨C, hC⟩` from `(Metric.isCompact_of_isClosed_isBounded hKc hKb).exists_bound_of_continuousOn (hP.1.continuousOn.mono hKd)`. Use `⟨C, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨b, hb, ho⟩` from `(orthonormalFlagTranslate_holds r X).1 x hx`. Rewrite using `[← (orthonormalFlagTranslate_holds r X).2.1 la P hP.2.1 x hx b hb, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit X la P (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho X ho)]`.

Conclude with `hC _ ho`.
-/
theorem bdd_of_definite {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (hp : X.p0 = 0 ∨ X.p0 = r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) :
    ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C := by
  obtain ⟨R, hR⟩ := GlobalTheory.orthonormal_frames_bounded_of_definite r X hp
  let K : Set (Frame X.Ψ r) := {x | X.IsOrtho x}
  have hKd : K ⊆ X.dom := fun x hx => PIW.FdPA.orthonormal_domain r X x hx
  have hKc : IsClosed K := by
    have e : K = ⋂ τ : X.Ψ, {x : Frame X.Ψ r | gram τ.1 X.Gm (mat x τ) =
        Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)} := by
      ext x; simp [K, Data.IsOrtho]
    rw [e]
    refine isClosed_iInter fun τ => isClosed_eq ?_ continuous_const
    unfold gram hermC col mat
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.of_apply]
    fun_prop
  have hKb : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨max R 0, fun x hx => ?_⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun τ => ?_
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun a => ?_
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun b => ?_
    exact (hR x hx τ a b).trans (le_max_left _ _)
  obtain ⟨C, hC⟩ := (Metric.isCompact_of_isClosed_isBounded hKc hKb).exists_bound_of_continuousOn
    (hP.1.continuousOn.mono hKd)
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨b, hb, ho⟩ := (orthonormalFlagTranslate_holds r X).1 x hx
  rw [← (orthonormalFlagTranslate_holds r X).2.1 la P hP.2.1 x hx b hb,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit X la P (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho X ho)]
  exact hC _ ho

end GlobalTheory.ScalarCusp

namespace GlobalTheory.ScalarCusp

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c r U x hL σ hσ Z`. Establish `hU` using `hL.unf σ hσ`. Establish `hr : r = Dw.p + Dw.q` using `hU.1`. Take `⟨k, hk⟩` from `GlobalTheory.FlatCore.framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ`. Distinguish the cases in `hdef : Dw.p = 0 ∨ Dw.q = 0`.

Take `⟨z, hz⟩` from `GlobalTheory.FlatLine.framesOn_nonempty hU Z`. Establish `hz' : z.1 = k ∧ z.2 ∈ ((U σ).X z.1).dom` using `by rw [hk] at hz; exact hz`. Take `⟨n, hn, he, f, hf, hne⟩` from `GlobalTheory.Reg.exists_even_sec_evR_ne_zero E H Dw l Xo c σ ((U σ).un z.1 ⟨z.2, hz'.2⟩)`. Establish `hD : Dom (0 : (E →+* ℂ) × ℕ → ℕ) n` using `⟨fun τ i i' _ => le_rfl, he⟩`. Use `⟨n, hn, he, f, ?_, z, hz, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_cusp]`. Use `⟨hf, fun σ' hσ' => holCusp_mem_holSub _ _ fun j => ?_⟩` and prove the remaining obligations. Establish `hU'` using `hL.unf σ' hσ'`. Establish `hs` using `hU'.2.2.2.2.1 0 n hD f hf j`. Choose the witnesses or unpack the hypotheses as in `⟨τ0⟩ : Nonempty ((U σ').X j).Ψ := by`.

Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Distinguish the cases in `h : τ ∈ ((U σ').X j).Ψ`. Conclude with `⟨⟨τ, h⟩⟩`. Conclude with `⟨⟨_, not_not.mp (fun h' => h ((((U σ').X j).cmType τ).mpr h'))⟩⟩`. Establish `hp0 : ((U σ').X j).p0 = 0 ∨ ((U σ').X j).p0 = r`.

Rewrite using `[(hU'.2.1 j).1]`. Use linear arithmetic over natural numbers and integers. Conclude with `GlobalTheory.BoundedCusp.mem_SS_of_definite _ _ τ0 hp0 _ ⟨hs, bdd_of_definite _ hp0 _ _ hs⟩`. Establish `e : rdU (U σ) f z.1 z.2 = toC (evR Xo c f ((U σ).un z.1 ⟨z.2, hz'.2⟩))` using `dif_pos hz'.2`. Rewrite using `[e]`.

Conclude with `hne`. Use `push_neg at hdef`. Establish `hp : 1 ≤ Dw.p` using `Nat.one_le_iff_ne_zero.2 hdef.1`. Establish `hq : 1 ≤ Dw.q` using `Nat.one_le_iff_ne_zero.2 hdef.2`. Distinguish the cases in `hrun : ∃ m : ℕ, 1 ≤ m ∧ m ^ 4 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E ∧ (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ 16 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ (Dw.p ≤ m ∨ Dw.q ≤ m)`.

Take `⟨m, hm1, hm4, hf2, hrd, hpm⟩` from `hrun`. Establish `hr2 : 2 ≤ r` using `by omega`. Establish `hf1 : 1 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E` using `le_trans (Nat.one_le_pow _ _ hm1) hm4`. Establish `hfr : 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r` using `by nlinarith`. Take `⟨q', R0, -, -, hrunOK⟩` from `GlobalTheory.RunParametersBound.exists_run_bound E r m hfr hm1 hm4 hf2 hrd`.

Establish `hT : AllTest Xo c` using `GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c`. Take `⟨i, J, _, cf, xs, f, hi, -, -, -, hf, -, hnz, -⟩` from `GlobalTheory.EtaAn.exists_etaRule_cusp_ne_zero_bounds E H Dw l Xo c r (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) σ (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (hL.unf σ hσ)) hσ hT hr2 5 (by decide) (by norm_num) 1 q' m R0 hrunOK hpm`. Take `⟨y, hy, hne⟩` from `hnz k`. Establish `hf' : f ∈ cusp Xo c U 0 (2 * 5 ^ 4 * r * i)` using `hf`. Use `⟨2 * 5 ^ 4 * r * i, by positivity, ⟨5 ^ 4 * r * i, by ring⟩, f, hf', ⟨k, y⟩, ?_, hne⟩` and prove the remaining obligations.

Rewrite using `[hk]`. Conclude with `⟨rfl, hy⟩`. Conclude with `GlobalTheory.T.exists_scalar_cuspForm_indefinite_unitaryShimura E H Dw l Xo c r U x hL hp hq hrun σ hσ Z`.
-/
theorem exists_scalar_cusp_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (Z : Comp Xo c), ∃ n₀ : ℕ, 0 < n₀ ∧ Even n₀ ∧ ∃ f₀ ∈ cusp Xo c U 0 n₀, ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f₀ z.1 z.2 ≠ 0 := by
  intro E _ _ _ H Dw l Xo c r U x hL σ hσ Z
  have hU := hL.unf σ hσ
  have hr : r = Dw.p + Dw.q := hU.1
  obtain ⟨k, hk⟩ := GlobalTheory.FlatCore.framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ
  by_cases hdef : Dw.p = 0 ∨ Dw.q = 0
  · obtain ⟨z, hz⟩ := GlobalTheory.FlatLine.framesOn_nonempty hU Z
    have hz' : z.1 = k ∧ z.2 ∈ ((U σ).X z.1).dom := by rw [hk] at hz; exact hz
    obtain ⟨n, hn, he, f, hf, hne⟩ :=
      GlobalTheory.Reg.exists_even_sec_evR_ne_zero E H Dw l Xo c σ ((U σ).un z.1 ⟨z.2, hz'.2⟩)
    have hD : Dom (0 : (E →+* ℂ) × ℕ → ℕ) n := ⟨fun τ i i' _ => le_rfl, he⟩
    refine ⟨n, hn, he, f, ?_, z, hz, ?_⟩
    · rw [mem_cusp]
      refine ⟨hf, fun σ' hσ' => holCusp_mem_holSub _ _ fun j => ?_⟩
      have hU' := hL.unf σ' hσ'
      have hs := hU'.2.2.2.2.1 0 n hD f hf j
      obtain ⟨τ0⟩ : Nonempty ((U σ').X j).Ψ := by
        obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
        by_cases h : τ ∈ ((U σ').X j).Ψ
        · exact ⟨⟨τ, h⟩⟩
        · exact ⟨⟨_, not_not.mp (fun h' => h ((((U σ').X j).cmType τ).mpr h'))⟩⟩
      have hp0 : ((U σ').X j).p0 = 0 ∨ ((U σ').X j).p0 = r := by
        rw [(hU'.2.1 j).1]; omega
      exact GlobalTheory.BoundedCusp.mem_SS_of_definite _ _ τ0 hp0 _ ⟨hs, bdd_of_definite _ hp0 _ _ hs⟩
    · have e : rdU (U σ) f z.1 z.2 = toC (evR Xo c f ((U σ).un z.1 ⟨z.2, hz'.2⟩)) := dif_pos hz'.2
      rw [e]
      exact hne
  · push_neg at hdef
    have hp : 1 ≤ Dw.p := Nat.one_le_iff_ne_zero.2 hdef.1
    have hq : 1 ≤ Dw.q := Nat.one_le_iff_ne_zero.2 hdef.2
    by_cases hrun : ∃ m : ℕ, 1 ≤ m ∧ m ^ 4 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E ∧ (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ 16 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ (Dw.p ≤ m ∨ Dw.q ≤ m)
    · obtain ⟨m, hm1, hm4, hf2, hrd, hpm⟩ := hrun
      have hr2 : 2 ≤ r := by omega
      have hf1 : 1 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E := le_trans (Nat.one_le_pow _ _ hm1) hm4
      have hfr : 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r := by nlinarith
      obtain ⟨q', R0, -, -, hrunOK⟩ := GlobalTheory.RunParametersBound.exists_run_bound E r m hfr hm1 hm4 hf2 hrd
      have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
      obtain ⟨i, J, _, cf, xs, f, hi, -, -, -, hf, -, hnz, -⟩ :=
        GlobalTheory.EtaAn.exists_etaRule_cusp_ne_zero_bounds E H Dw l Xo c r (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) σ
          (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (hL.unf σ hσ)) hσ hT hr2 5 (by decide)
          (by norm_num) 1 q' m R0 hrunOK hpm
      obtain ⟨y, hy, hne⟩ := hnz k
      have hf' : f ∈ cusp Xo c U 0 (2 * 5 ^ 4 * r * i) := hf
      refine ⟨2 * 5 ^ 4 * r * i, by positivity, ⟨5 ^ 4 * r * i, by ring⟩, f, hf', ⟨k, y⟩, ?_, hne⟩
      rw [hk]
      exact ⟨rfl, hy⟩
    · exact GlobalTheory.T.exists_scalar_cuspForm_indefinite_unitaryShimura E H Dw l Xo c r U x hL hp hq hrun σ hσ Z

end GlobalTheory.ScalarCusp
