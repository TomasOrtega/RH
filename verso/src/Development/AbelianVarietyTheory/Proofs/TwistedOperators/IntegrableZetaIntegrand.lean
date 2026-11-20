import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviEmbMulSingle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyDeepSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)

namespace GlobalTheory.ZetaConvergence

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨y, hy⟩` from `hK.elim_directed_cover (fun y : kˣ => GlobalTheory.SplitWeil.cball y) (fun y => GlobalTheory.SplitWeil.isOpen_cball y) (fun x _ => by`. Distinguish the cases in `hx : x = 0`. Conclude with `Set.mem_iUnion.2 ⟨1, by simp [hx, GlobalTheory.SplitWeil.cball]⟩`. Conclude with `Set.mem_iUnion.2 ⟨Units.mk0 x hx, by simp [GlobalTheory.SplitWeil.cball]⟩)`. Use the proof step `(fun a b => by`.

Break down `le_total (valuation k (a : k)) (valuation k (b : k)) with h | h` into its components or cases. Conclude with `⟨b, fun z hz => le_trans (show valuation k z ≤ _ from hz) h, subset_rfl⟩`. Conclude with `⟨a, subset_rfl, fun z hz => le_trans (show valuation k z ≤ _ from hz) h⟩)`. Conclude with `⟨nabs k y, fun x hx => nabs_le_of_valuation_le (hy hx)⟩`.
-/
theorem exists_nabs_le {K : Set k} (hK : IsCompact K) : ∃ B : ℝ, ∀ x : kˣ, (x : k) ∈ K → nabs k x ≤ B := by
  obtain ⟨y, hy⟩ := hK.elim_directed_cover (fun y : kˣ => GlobalTheory.SplitWeil.cball y)
    (fun y => GlobalTheory.SplitWeil.isOpen_cball y)
    (fun x _ => by
      by_cases hx : x = 0
      · exact Set.mem_iUnion.2 ⟨1, by simp [hx, GlobalTheory.SplitWeil.cball]⟩
      · exact Set.mem_iUnion.2 ⟨Units.mk0 x hx, by simp [GlobalTheory.SplitWeil.cball]⟩)
    (fun a b => by
      rcases le_total (valuation k (a : k)) (valuation k (b : k)) with h | h
      · exact ⟨b, fun z hz => le_trans (show valuation k z ≤ _ from hz) h, subset_rfl⟩
      · exact ⟨a, subset_rfl, fun z hz => le_trans (show valuation k z ≤ _ from hz) h⟩)
  exact ⟨nabs k y, fun x hx => nabs_le_of_valuation_le (hy hx)⟩

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ν _ n _ _ c α hc hb Φ hΦ`. Take `⟨N, -, hN, -⟩` from `GlobalTheory.SBUniform.exists_bound_period k n Φ hΦ`. Take `⟨C, hC⟩` from `hb N`. Take `⟨hl, hK⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ` from `hΦ`. Take `⟨B, hB⟩` from `exists_nabs_le (IsCompact.image hK (f := fun x : Matrix n n k => x.det) continuous_id.matrix_det)`.

Use `GlobalTheory.SplitWeil.secondCountable k` as an intermediate fact. Use `GlobalTheory.SplitWeil.t2Space k` as an intermediate fact. Establish `: BorelSpace (Matrix n n k)` using `inferInstanceAs (BorelSpace (n → n → k))`. Establish `: (volM ν n n).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`. Establish `: BorelSpace (GL n k)` using `SplitFlip.borel_GL`.

Establish `: SecondCountableTopology (GL n k)` using `SplitFlip.secondCountable_GL`. Establish `hE` using `GlobalTheory.SplitWeil.Model.measurableEmbedding_val (k := k) n`. Establish `hd` using `continuous_density_volGL (k := k) (n := n)`. Establish `hn : IsLocallyConstant fun g : GL n k => nabs k (GeneralLinearGroup.det g)` using `(isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det`. Establish `hI : Integrable (fun g : GL n k => Φ g.val) ((volM ν n n).comap fun g : GL n k => g.val)`.

Establish `h1 : Integrable Φ (volM ν n n)` using `hl.continuous.integrable_of_hasCompactSupport hK`. Use `hE.integrable_map_iff.1 ?_` and prove the remaining obligations. Rewrite using `[hE.map_comap]`. Conclude with `h1.restrict`. Use `⟨α + Fintype.card n - ((Fintype.card n : ℝ) - 1) / 2, fun s hs => ?_⟩` and prove the remaining obligations.

Use `set t : ℂ := s + ((Fintype.card n : ℂ) - 1) / 2 with ht`. Establish `htr : t.re = s.re + ((Fintype.card n : ℝ) - 1) / 2`. Establish `: ((Fintype.card n : ℂ) - 1) / 2 = ((((Fintype.card n : ℝ) - 1) / 2 : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[ht, this, Complex.add_re, Complex.ofReal_re]`. Establish `he : 0 ≤ -(Fintype.card n : ℝ) + -α + t.re` using `by linarith`.

Establish `hz : Continuous (zetaIntegrand Φ c s)` using `((hl.continuous.comp Units.continuous_val).mul hc).mul (hn.comp fun r : ℝ => (r : ℂ) ^ t).continuous`. Unfold `volGL`. Rewrite using `[integrable_withDensity_iff_integrable_smul' hd.measurable (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]`. Use `(hI.norm.mul_const (|C| * B ^ (-(Fintype.card n : ℝ) + -α + t.re))).mono' (hd.measurable.ennreal_toReal.aestronglyMeasurable.smul hz.aestronglyMeasurable) (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Establish `hp` using `nabs_pos' k (GeneralLinearGroup.det g)`.

Distinguish the cases in `h0 : Φ g.val = 0`. Simplify using `[zetaIntegrand, h0]`. Establish `h1 : nabs k (GeneralLinearGroup.det g) ≤ B` using `hB _ ⟨g.val, subset_tsupport _ h0, rfl⟩`. Establish `h2` using `(hC g (hN _ h0)).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hp.le _))`. Rewrite using `[norm_smul, ENNReal.toReal_ofReal (Real.rpow_nonneg hp.le _), zetaIntegrand, norm_mul, norm_mul, val_absPow, Complex.norm_cpow_eq_rpow_re_of_pos hp, ← ht, Real.norm_of_nonneg (Real.rpow_nonneg hp.le _)]`.

Use `set a := nabs k (GeneralLinearGroup.det g)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.rpow_add hp, Real.rpow_add hp]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := by gcongr`.
-/
theorem integrable_zetaIntegrand : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : GL n k → ℂ) (α : ℝ), Continuous c → (∀ N : ℕ, ∃ C : ℝ, ∀ g : GL n k, (∀ i j, Deep (-(N : ℤ)) (g.val i j)) → ‖c g‖ ≤ C * nabs k (GeneralLinearGroup.det g) ^ (-α)) → ∀ Φ ∈ SB (Matrix n n k), ∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (zetaIntegrand Φ c s) (volGL ν n) := by
  intro k _ _ _ _ _ _ ν _ n _ _ c α hc hb Φ hΦ
  obtain ⟨N, -, hN, -⟩ := GlobalTheory.SBUniform.exists_bound_period k n Φ hΦ
  obtain ⟨C, hC⟩ := hb N
  obtain ⟨hl, hK⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  obtain ⟨B, hB⟩ := exists_nabs_le (IsCompact.image hK (f := fun x : Matrix n n k => x.det)
    continuous_id.matrix_det)
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  have : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  have : (volM ν n n).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : BorelSpace (GL n k) := SplitFlip.borel_GL
  have : SecondCountableTopology (GL n k) := SplitFlip.secondCountable_GL
  have hE := GlobalTheory.SplitWeil.Model.measurableEmbedding_val (k := k) n
  have hd := continuous_density_volGL (k := k) (n := n)
  have hn : IsLocallyConstant fun g : GL n k => nabs k (GeneralLinearGroup.det g) :=
    (isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det
  have hI : Integrable (fun g : GL n k => Φ g.val) ((volM ν n n).comap fun g : GL n k => g.val) := by
    have h1 : Integrable Φ (volM ν n n) := hl.continuous.integrable_of_hasCompactSupport hK
    refine hE.integrable_map_iff.1 ?_
    rw [hE.map_comap]
    exact h1.restrict
  refine ⟨α + Fintype.card n - ((Fintype.card n : ℝ) - 1) / 2, fun s hs => ?_⟩
  set t : ℂ := s + ((Fintype.card n : ℂ) - 1) / 2 with ht
  have htr : t.re = s.re + ((Fintype.card n : ℝ) - 1) / 2 := by
    have : ((Fintype.card n : ℂ) - 1) / 2 = ((((Fintype.card n : ℝ) - 1) / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [ht, this, Complex.add_re, Complex.ofReal_re]
  have he : 0 ≤ -(Fintype.card n : ℝ) + -α + t.re := by linarith
  have hz : Continuous (zetaIntegrand Φ c s) :=
    ((hl.continuous.comp Units.continuous_val).mul hc).mul (hn.comp fun r : ℝ => (r : ℂ) ^ t).continuous
  unfold volGL
  rw [integrable_withDensity_iff_integrable_smul' hd.measurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine (hI.norm.mul_const (|C| * B ^ (-(Fintype.card n : ℝ) + -α + t.re))).mono'
    (hd.measurable.ennreal_toReal.aestronglyMeasurable.smul hz.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun g => ?_)
  have hp := nabs_pos' k (GeneralLinearGroup.det g)
  by_cases h0 : Φ g.val = 0
  · simp [zetaIntegrand, h0]
  have h1 : nabs k (GeneralLinearGroup.det g) ≤ B := hB _ ⟨g.val, subset_tsupport _ h0, rfl⟩
  have h2 := (hC g (hN _ h0)).trans
    (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hp.le _))
  rw [norm_smul, ENNReal.toReal_ofReal (Real.rpow_nonneg hp.le _), zetaIntegrand, norm_mul, norm_mul,
    val_absPow, Complex.norm_cpow_eq_rpow_re_of_pos hp, ← ht, Real.norm_of_nonneg (Real.rpow_nonneg hp.le _)]
  set a := nabs k (GeneralLinearGroup.det g)
  calc _ ≤ a ^ (-(Fintype.card n : ℝ)) * (‖Φ g.val‖ * (|C| * a ^ (-α)) * a ^ t.re) := by gcongr
    _ = ‖Φ g.val‖ * (|C| * a ^ (-(Fintype.card n : ℝ) + -α + t.re)) := by
      rw [Real.rpow_add hp, Real.rpow_add hp]; ring
    _ ≤ _ := by gcongr

end GlobalTheory.ZetaConvergence
