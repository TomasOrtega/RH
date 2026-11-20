import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStartPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfE

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace DivUpPf

variable {r : ℕ} (X : Data E r)

/- English proof (translation)
Unfold `bchar`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Take `⟨hdet, htri⟩` from `hb τ`. Establish `hd : (mat b τ).det = ∏ j, mat b τ j j` using `Matrix.det_of_upperTriangular (fun a c h => htri a c h)`. Establish `hne : b τ i i ≠ 0`. Introduce `h0`. Apply `hdet` to reduce the goal to its premises.

Rewrite using `[hd]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) h0`. Conclude with `zpow_add₀ hne _ _`.
-/
theorem bchar_add (la la' : Wt X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    bchar (la + la') b = bchar la b * bchar la' b := by
  unfold bchar
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  obtain ⟨hdet, htri⟩ := hb τ
  have hd : (mat b τ).det = ∏ j, mat b τ j j :=
    Matrix.det_of_upperTriangular (fun a c h => htri a c h)
  have hne : b τ i i ≠ 0 := by
    intro h0
    apply hdet
    rw [hd]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  exact zpow_add₀ hne _ _

/- English proof (translation)
Rewrite using `[show -(-2 * Real.log P) = Real.log P + Real.log P by ring, Real.exp_add, Real.exp_log hP]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma exp_neg_neg_two_mul_log (P : ℝ) (hP : 0 < P) : Real.exp (-(-2 * Real.log P)) = P ^ 2 := by
  rw [show -(-2 * Real.log P) = Real.log P + Real.log P by ring, Real.exp_add, Real.exp_log hP]
  ring

/- English proof (translation)
Unfold `Data.dom GG at hx`. Establish `hd : ∀ τ (i : Fin (r + 1)), dmin X.Gm x τ i ≠ 0`. Introduce `τ i h0`. Establish `h1` using `(hx τ).2 i`. Rewrite `h1` using `[h0, Complex.zero_re, mul_zero]`.

Conclude with `lt_irrefl _ h1`. Unfold `phla Data.nfac`. Conclude with `exp_neg_neg_two_mul_log _ (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd τ _) (hd τ _))) _)`.
-/
theorem exp_phla (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Real.exp (-phla X la x) = X.nfac la x ^ 2 := by
  unfold Data.dom GG at hx
  have hd : ∀ τ (i : Fin (r + 1)), dmin X.Gm x τ i ≠ 0 := by
    intro τ i h0
    have h1 := (hx τ).2 i
    rw [h0, Complex.zero_re, mul_zero] at h1
    exact lt_irrefl _ h1
  unfold phla Data.nfac
  exact exp_neg_neg_two_mul_log _ (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd τ _) (hd τ _))) _)

/- English proof (translation)
Establish `hc : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i`. Introduce `τ i`. Use `first`. Consider the case `(unfold dmin lminor gram mat hermC col; fun_prop)`. Consider the case `(unfold dmin lminor gram mat hermC col; continuity)`.

Consider the case `(unfold dmin lminor gram mat hermC col; exact Nat.zero)`. Unfold `Data.nfac`. Use `Finset.measurable_prod _ fun τ _ => Finset.measurable_prod _ fun i _ => ?_` and prove the remaining obligations. Conclude with `(((hc τ _).measurable.div (hc τ _).measurable).norm).pow_const _`.
-/
theorem nfac_meas (la : Wt X.Ψ r) : Measurable (X.nfac la) := by
  have hc : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    first
      | (unfold dmin lminor gram mat hermC col; fun_prop)
      | (unfold dmin lminor gram mat hermC col; continuity)
      | (unfold dmin lminor gram mat hermC col; exact Nat.zero)
  unfold Data.nfac
  refine Finset.measurable_prod _ fun τ _ => Finset.measurable_prod _ fun i _ => ?_
  exact (((hc τ _).measurable.div (hc τ _).measurable).norm).pow_const _

/- English proof (translation)
Use `⟨?_, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩` and prove the remaining obligations. Unfold `phla`. Conclude with `ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((measurable_const.mul (Real.measurable_log.comp (nfac_meas X la))).neg))`. Establish `hxb` using `OrthogonalFrameDomain.rmul_mem_dom X hx hb`. Establish `hbc : bchar la b ≠ 0`.

Unfold `bchar`. Conclude with `Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (FrameDegreeData.bdiag_ne X hb τ i)`. Establish `hn` using `FlowCoefficientBounds.nfac_pos X hx la`. Simplify using `only`. Rewrite using `[exp_phla X la hxb, exp_phla X la hx, normFactor_rightBorel_holds r X la x hx b hb, mul_pow, inv_pow, ← ENNReal.ofReal_div_of_pos (by positivity)]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Simplify using `only [phla]`. Rewrite using `[normFactor_leftAction_holds r X la γ hγ x hx]`.
-/
theorem metricW_exp (la : Wt X.Ψ r) :
    IsMetricW X la (fun x => ENNReal.ofReal (Real.exp (-phla X la x))) := by
  refine ⟨?_, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · unfold phla
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_const.mul (Real.measurable_log.comp (nfac_meas X la))).neg))
  · have hxb := OrthogonalFrameDomain.rmul_mem_dom X hx hb
    have hbc : bchar la b ≠ 0 := by
      unfold bchar
      exact Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ =>
        zpow_ne_zero _ (FrameDegreeData.bdiag_ne X hb τ i)
    have hn := FlowCoefficientBounds.nfac_pos X hx la
    simp only
    rw [exp_phla X la hxb, exp_phla X la hx, normFactor_rightBorel_holds r X la x hx b hb, mul_pow, inv_pow,
      ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  · simp only [phla]
    rw [normFactor_leftAction_holds r X la γ hγ x hx]

/- English proof (translation)
Unfold `WLower`. Conclude with `⟨1, one_pos, fun x _ => le_of_eq (by rw [one_mul])⟩`.
-/
theorem wLower_exp (la : Wt X.Ψ r) :
    WLower X la (fun x => ENNReal.ofReal (Real.exp (-phla X la x))) := by
  unfold WLower
  exact ⟨1, one_pos, fun x _ => le_of_eq (by rw [one_mul])⟩

/- English proof (translation)
Establish `h` using `DivSt.sec_prod X Finset.univ (fun k => α k • Xa.L) (fun k _ => DivSt.sec_pow X (Fl.s_van k).1.1.1 (α k))`. Rewrite using `[Finset.sum_smul]`. Conclude with `h`.
-/
theorem mono_sec {Xa : ArchInM X} (Fl : FlatM X Xa) (α : Fin (nd X) → ℕ) :
    X.IsSec ((∑ k, α k) • Xa.L) (monoM X Fl.s α) := by
  have h := DivSt.sec_prod X Finset.univ (fun k => α k • Xa.L)
    (fun k _ => DivSt.sec_pow X (Fl.s_van k).1.1.1 (α k))
  rw [Finset.sum_smul]
  exact h

end DivUpPf

open DivUpPf

/- English proof (translation)
Introduce `r X Xa Fl hPD hFin hm hL hcF hcFp hcka hfd δ t ht hval x0 hx0 FF hFF f hf hint cc hv`. Take `⟨hgb, hgi⟩` from `hStart r X Xa Fl hPD hFin δ t ht x0 hx0 FF hFF f hf hint cc`. Establish `hgSS` using `hcka _ hgb`. Take `⟨bb, m', hbb, hm', hmarg⟩` from `hm`. Take `⟨Ps, g1, hWm, hWl, hg1d, hg1ne, hPs, hWPs, hlevi, hstart⟩` from `hOW r X Xa Fl hPD hFin bb m' hbb hm' hmarg hL x0 hx0 FF hFF`.

Establish `hIn` using `hstart _ hgSS hgi hv`. Establish `hfd' : ∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f' ∈ X.SS (Xa.Fp + Xa.T • Xa.L), InFF X x0 (WSk X Xa Fl) FF f' → ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f' x = ∑ i, c i * g i x`. Take `⟨K, gg, hK⟩` from `hfd`. Conclude with `⟨K, gg, fun f' hf' _ => hK f' hf'⟩`. Take `⟨F, P, hFd, hFA, hPeq, hPF, hpoin⟩` from `ontoStatement_holds r X x0 hx0 hPD (Xa.Fp + Xa.T • Xa.L) (WSk X Xa Fl) Ps g1 bb m' hWm hWl hbb hm' hg1d hg1ne hPs hWPs hlevi hcka FF hFF hfd' _ hgSS hIn`.

Take `⟨H, hH, hFH⟩` from `hUD r X Xa Fl hPD hFin bb m' hbb hm' hmarg hL x0 hx0 F hFd hFA`. Establish `hbb0 : 0 < bb` using `lt_of_le_of_lt (by positivity) hbb`. Establish `hL2 : ∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), ∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom → ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖H α z‖ ^ 2 * Real.exp (-phla X (Xa.Fp + nd X • Xa.L) (cpt X x0 z))) ∂muF X x0 < ⊤`. Introduce `α hα C _ _`. Use `lt_of_le_of_lt (setLIntegral_le_lintegral _ _) (lt_of_le_of_lt ?_ (hH α hα).2)` and prove the remaining obligations.

Use `lintegral_mono_ae ?_` and prove the remaining obligations. Use `filter_upwards [ExtFPf.ae_OmF (x0 := x0)] with z hz`. Establish `hr` using `ExF.rhF_nonneg X x0 hx0 hz`. Establish `hka : 0 < kaF X x0 bb z` using `Real.exp_pos _`. Establish `hka1 : kaF X x0 bb z ≤ 1` using `Real.exp_le_one_iff.mpr (by nlinarith)`.

Rewrite using `[weightFunctionOnFrames, ← ENNReal.ofReal_mul (by positivity)]`. Use `ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)` and prove the remaining obligations. Rewrite using `[le_div_iff₀ hka]`. Use polynomial arithmetic with `[sq_nonneg ‖H α z‖]`. Establish `hext` using `fun α (hα : α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X)) => extFStatement_holds r X x0 hx0 (Xa.Fp + nd X • Xa.L) (H α) (hH α hα).1 (hL2 α hα)`.

Use `choose! Pα hPαB hPαF using hext`. Establish `hpo` using `fun α (hα : α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X)) => poin_holds r X x0 hx0 hPD (Xa.Fp + nd X • Xa.L) (weightFunctionOnFrames X Xa) bb (metricW_exp X _) (wLower_exp X _) hbb (H α) (Pα α) (hH α hα).1 (hH α hα).2 (hPαB α hα) (hPαF α hα)`. Establish `hnT : nd X ≤ Xa.T`. Establish `h1` using `Xa.T_ge`. Establish `h2` using `Xa.n_ge`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hw : Xa.Fp + Xa.T • Xa.L = (Xa.Fp + nd X • Xa.L) + (Xa.T - nd X) • Xa.L`. Rewrite using `[add_assoc, ← add_nsmul, Nat.add_sub_cancel' hnT]`. Establish `hmono : ∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), X.IsSec ((Xa.T - nd X) • Xa.L) (monoM X Fl.s α)` using `fun α hα => by`. Use `mono_sec X Fl α` as an intermediate fact.

Rewrite `this` using `[Finset.Nat.mem_antidiagonalTuple.mp hα]`. Then use the resulting hypothesis. Take `⟨Q, hQ⟩ : ∃ Q : Frame X.Ψ r → ℂ, Q = fun x => ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), monoM X Fl.s α x * Pα α x` from `⟨_, rfl⟩`. Establish `hPQ : ∀ x ∈ X.dom, P x = Q x`. Take `⟨Δ, zOf, bOf, hΔd, hdense, -, -, hsplit, -⟩` from `lu_holds r X x0 hx0`. Establish `hQd : DifferentiableOn ℂ Q X.dom`.

Rewrite using `[hQ]`. Conclude with `DifferentiableOn.fun_sum fun α hα => (hmono α hα).1.mul (hPαB α hα).1`. Establish `heq : Set.EqOn P Q {x | x ∈ X.dom ∧ Δ x ≠ 0}`. Introduce `x hx`. Take `⟨hz, hb, hxe⟩` from `hsplit x hx.1 hx.2`.

Rewrite using `[hxe, hPeq.2 _ hz _ hb, hPF _ hz, hFH _ hz, hQ]`. Simplify using `only`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun α hα => ?_` and prove the remaining obligations. Rewrite using `[(hmono α hα).2.1 _ hz _ hb, (hPαB α hα).2 _ hz _ hb, hPαF α hα _ hz, hw, bchar_add X _ _ hb]`.

Simplify using `only [monoM]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcl : X.dom ⊆ closure {x | x ∈ X.dom ∧ Δ x ≠ 0}`. Introduce `x hx`. Rewrite using `[Metric.mem_closure_iff]`.

Introduce `ε hε`. Take `⟨ε0, hε0, hb0⟩` from `Metric.isOpen_iff.mp (FourierCoefficientDomain.isOpen_dom X) x hx`. Take `⟨y, hy, hΔy⟩` from `hdense x hx (min ε ε0) (lt_min hε hε0)`. Use `⟨y, ⟨hb0 (Metric.ball_subset_ball (min_le_right _ _) hy), hΔy⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[dist_comm]`.

Conclude with `lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_left _ _)`. Introduce `x hx`. Conclude with `Set.EqOn.of_subset_closure heq hPeq.1.continuousOn hQd.continuousOn (fun y hy => hy.1) hcl hx`. Use `⟨fun α => poin X (Xa.Fp + nd X • Xa.L) (Pα α), fun α hα => (hpo α hα).2.1, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← hpoin x hx]`.

Establish `h2 : poin X (Xa.Fp + Xa.T • Xa.L) P x = poin X (Xa.Fp + Xa.T • Xa.L) Q x`. Unfold `poin`. Conclude with `tsum_congr fun γ => by rw [hPQ _ (KU.lact_dom X γ.2 hx)]`. Rewrite using `[h2, hQ]`. Unfold `poin`.

Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Summable.tsum_finsetSum]`. Use `Finset.sum_congr rfl fun α hα => ?_` and prove the remaining obligations. Establish `hprod` using `(hpo α hα).2.2.2.2 ((Xa.T - nd X) • Xa.L) (monoM X Fl.s α) (hmono α hα) x hx`. Unfold `poin at hprod`.

Rewrite using `[hw, ← hprod]`. Introduce `α hα`. Establish `hs` using `(hpo α hα).1 x hx`. Use `Summable.of_norm_bounded (hs.mul_left ‖monoM X Fl.s α x‖) fun γ => ?_` and prove the remaining obligations. Rewrite using `[(hmono α hα).2.2 γ.1 γ.2 x hx, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv, PoinPf.norm_chi X _ γ.2, PoinPf.norm_chi X _ γ.2, PoinPf.norm_chi X _ γ.2]`.

Simplify using the standard rewrite rules.
-/
theorem divCore_up_of (hOW : OntoWeightStatement (E := E)) (hUD : UpDivStatement (E := E))
    (hStart : DivStartStatement (E := E)) : DivCoreStatement (E := E) := by
  intro r X Xa Fl hPD hFin hm hL hcF hcFp hcka hfd δ t ht hval x0 hx0 FF hFF f hf hint cc hv
  obtain ⟨hgb, hgi⟩ := hStart r X Xa Fl hPD hFin δ t ht x0 hx0 FF hFF f hf hint cc
  have hgSS := hcka _ hgb
  obtain ⟨bb, m', hbb, hm', hmarg⟩ := hm
  obtain ⟨Ps, g1, hWm, hWl, hg1d, hg1ne, hPs, hWPs, hlevi, hstart⟩ :=
    hOW r X Xa Fl hPD hFin bb m' hbb hm' hmarg hL x0 hx0 FF hFF
  have hIn := hstart _ hgSS hgi hv
  have hfd' : ∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f' ∈ X.SS (Xa.Fp + Xa.T • Xa.L),
      InFF X x0 (WSk X Xa Fl) FF f' → ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f' x = ∑ i, c i * g i x := by
    obtain ⟨K, gg, hK⟩ := hfd
    exact ⟨K, gg, fun f' hf' _ => hK f' hf'⟩
  obtain ⟨F, P, hFd, hFA, hPeq, hPF, hpoin⟩ := ontoStatement_holds r X x0 hx0 hPD
    (Xa.Fp + Xa.T • Xa.L) (WSk X Xa Fl) Ps g1 bb m' hWm hWl hbb hm' hg1d hg1ne hPs hWPs hlevi hcka
    FF hFF hfd' _ hgSS hIn
  obtain ⟨H, hH, hFH⟩ := hUD r X Xa Fl hPD hFin bb m' hbb hm' hmarg hL x0 hx0 F hFd hFA
  have hbb0 : 0 < bb := lt_of_le_of_lt (by positivity) hbb

  have hL2 : ∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), ∀ C : Set (Frame X.Ψ r),
      IsCompact C → C ⊆ X.dom → ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖H α z‖ ^ 2 *
        Real.exp (-phla X (Xa.Fp + nd X • Xa.L) (cpt X x0 z))) ∂muF X x0 < ⊤ := by
    intro α hα C _ _
    refine lt_of_le_of_lt (setLIntegral_le_lintegral _ _) (lt_of_le_of_lt ?_ (hH α hα).2)
    refine lintegral_mono_ae ?_
    filter_upwards [ExtFPf.ae_OmF (x0 := x0)] with z hz
    have hr := ExF.rhF_nonneg X x0 hx0 hz
    have hka : 0 < kaF X x0 bb z := Real.exp_pos _
    have hka1 : kaF X x0 bb z ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [weightFunctionOnFrames, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    rw [le_div_iff₀ hka]
    nlinarith [sq_nonneg ‖H α z‖]
  have hext := fun α (hα : α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X)) =>
    extFStatement_holds r X x0 hx0 (Xa.Fp + nd X • Xa.L) (H α) (hH α hα).1 (hL2 α hα)
  choose! Pα hPαB hPαF using hext
  have hpo := fun α (hα : α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X)) =>
    poin_holds r X x0 hx0 hPD (Xa.Fp + nd X • Xa.L) (weightFunctionOnFrames X Xa) bb (metricW_exp X _) (wLower_exp X _) hbb
      (H α) (Pα α) (hH α hα).1 (hH α hα).2 (hPαB α hα) (hPαF α hα)
  have hnT : nd X ≤ Xa.T := by
    have h1 := Xa.T_ge
    have h2 := Xa.n_ge
    nlinarith
  have hw : Xa.Fp + Xa.T • Xa.L = (Xa.Fp + nd X • Xa.L) + (Xa.T - nd X) • Xa.L := by
    rw [add_assoc, ← add_nsmul, Nat.add_sub_cancel' hnT]
  have hmono : ∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X),
      X.IsSec ((Xa.T - nd X) • Xa.L) (monoM X Fl.s α) := fun α hα => by
    have := mono_sec X Fl α
    rwa [Finset.Nat.mem_antidiagonalTuple.mp hα] at this
  obtain ⟨Q, hQ⟩ : ∃ Q : Frame X.Ψ r → ℂ, Q = fun x =>
      ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), monoM X Fl.s α x * Pα α x := ⟨_, rfl⟩

  have hPQ : ∀ x ∈ X.dom, P x = Q x := by
    obtain ⟨Δ, zOf, bOf, hΔd, hdense, -, -, hsplit, -⟩ := lu_holds r X x0 hx0
    have hQd : DifferentiableOn ℂ Q X.dom := by
      rw [hQ]
      exact DifferentiableOn.fun_sum fun α hα => (hmono α hα).1.mul (hPαB α hα).1
    have heq : Set.EqOn P Q {x | x ∈ X.dom ∧ Δ x ≠ 0} := by
      intro x hx
      obtain ⟨hz, hb, hxe⟩ := hsplit x hx.1 hx.2
      rw [hxe, hPeq.2 _ hz _ hb, hPF _ hz, hFH _ hz, hQ]
      simp only
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [(hmono α hα).2.1 _ hz _ hb, (hPαB α hα).2 _ hz _ hb, hPαF α hα _ hz, hw,
        bchar_add X _ _ hb]
      simp only [monoM]
      ring
    have hcl : X.dom ⊆ closure {x | x ∈ X.dom ∧ Δ x ≠ 0} := by
      intro x hx
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨ε0, hε0, hb0⟩ := Metric.isOpen_iff.mp (FourierCoefficientDomain.isOpen_dom X) x hx
      obtain ⟨y, hy, hΔy⟩ := hdense x hx (min ε ε0) (lt_min hε hε0)
      refine ⟨y, ⟨hb0 (Metric.ball_subset_ball (min_le_right _ _) hy), hΔy⟩, ?_⟩
      rw [dist_comm]
      exact lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_left _ _)
    intro x hx
    exact Set.EqOn.of_subset_closure heq hPeq.1.continuousOn hQd.continuousOn (fun y hy => hy.1) hcl hx
  refine ⟨fun α => poin X (Xa.Fp + nd X • Xa.L) (Pα α), fun α hα => (hpo α hα).2.1, fun x hx => ?_⟩
  rw [← hpoin x hx]
  have h2 : poin X (Xa.Fp + Xa.T • Xa.L) P x = poin X (Xa.Fp + Xa.T • Xa.L) Q x := by
    unfold poin
    exact tsum_congr fun γ => by rw [hPQ _ (KU.lact_dom X γ.2 hx)]
  rw [h2, hQ]
  unfold poin
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum]
  · refine Finset.sum_congr rfl fun α hα => ?_
    have hprod := (hpo α hα).2.2.2.2 ((Xa.T - nd X) • Xa.L) (monoM X Fl.s α) (hmono α hα) x hx
    unfold poin at hprod
    rw [hw, ← hprod]
  · intro α hα
    have hs := (hpo α hα).1 x hx
    refine Summable.of_norm_bounded (hs.mul_left ‖monoM X Fl.s α x‖) fun γ => ?_
    rw [(hmono α hα).2.2 γ.1 γ.2 x hx, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv,
      PoinPf.norm_chi X _ γ.2, PoinPf.norm_chi X _ γ.2, PoinPf.norm_chi X _ γ.2]
    simp

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
