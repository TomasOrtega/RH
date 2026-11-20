import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.NearNonzeroTerms
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FarTermSum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsAutIdemElementary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LogSingularValuesEuclidNormCartanProperties

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff ENNReal

namespace GlobalTheory.NearMeas

/- English proof (translation)
Rewrite using `[tsum_subtype S f, tsum_subtype T (S.indicator f), Set.indicator_indicator, Set.inter_eq_right.mpr h]`.
-/
theorem tsum_sub_eq {G : Type} (S T : Set G) (h : S ⊆ T) (f : G → ℝ≥0∞) :
    ∑' γ : S, f γ.1 = ∑' γ : T, S.indicator f γ.1 := by
  rw [tsum_subtype S f, tsum_subtype T (S.indicator f), Set.indicator_indicator,
    Set.inter_eq_right.mpr h]

/- English proof (translation)
Use `show Continuous fun g : B.I.Ginf => ((∏ v, d v : ℝ) : ℂ) * star (∏ v, ⟪B.w v, B.σ v (uMat (g v)) (B.w v)⟫_ℂ)`. Use `continuous_const.mul (continuous_star.comp (continuous_finsetProd _ fun v _ => ?_))` and prove the remaining obligations. Take `⟨-, ⟨-, -, ⟨-, -, hcont⟩, -⟩, -⟩` from `h v`. Establish `hmat : Continuous fun g : B.I.Ginf => uMat (g v)` using `Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply v))`. Establish `hc : Continuous fun g : B.I.Ginf => B.σ v (uMat (g v)) (B.w v)` using `(hcont (B.w v)).comp_continuous hmat fun g => (g v).2`.

Conclude with `continuous_const.inner hc`.
-/
private theorem continuous_ph' (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : IsDSData B d) :
    Continuous (ph B d) := by
  show Continuous fun g : B.I.Ginf =>
    ((∏ v, d v : ℝ) : ℂ) * star (∏ v, ⟪B.w v, B.σ v (uMat (g v)) (B.w v)⟫_ℂ)
  refine continuous_const.mul (continuous_star.comp (continuous_finsetProd _ fun v _ => ?_))
  obtain ⟨-, ⟨-, -, ⟨-, -, hcont⟩, -⟩, -⟩ := h v
  have hmat : Continuous fun g : B.I.Ginf => uMat (g v) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply v))
  have hc : Continuous fun g : B.I.Ginf => B.σ v (uMat (g v)) (B.w v) :=
    (hcont (B.w v)).comp_continuous hmat fun g => (g v).2
  exact continuous_const.inner hc

/- English proof (translation)
Take `⟨hlc, -⟩` from `B.e_adm`. Use `show Continuous fun x : B.I.GA => ph B d x.1 * B.e x.2`. Conclude with `((continuous_ph' B d h).comp continuous_fst).mul (hlc.continuous.comp continuous_snd)`.
-/
theorem continuous_phe (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : IsDSData B d) :
    Continuous (phe B d) := by
  obtain ⟨hlc, -⟩ := B.e_adm
  show Continuous fun x : B.I.GA => ph B d x.1 * B.e x.2
  exact ((continuous_ph' B d h).comp continuous_fst).mul (hlc.continuous.comp continuous_snd)

/- English proof (translation)
The claim follows from `(continuous_inv.mul continuous_const).mul continuous_id`.
-/
private theorem continuous_conj_by_inv (B : RowsAut) (γ : B.I.GA) :
    Continuous fun x : B.I.GA => x⁻¹ * γ * x :=
  (continuous_inv.mul continuous_const).mul continuous_id

/- English proof (translation)
Establish `hc : Continuous fun x : B.I.GA => phe B d (x⁻¹ * γ * x)` using `(continuous_phe B d h).comp (continuous_conj_by_inv B γ)`. Establish `hd : ∀ v, Continuous fun x : B.I.GA => dHS (uMat ((x⁻¹ * γ * x).1 v))` using `fun v => (GlobalTheory.Count.CartanSize.cartan_size _ (B.I.ε v)).1.comp ((continuous_apply v).comp (continuous_fst.comp (continuous_conj_by_inv B γ)))`. Establish `hcl : IsClosed {x : B.I.GA | ∀ v, dHS (uMat ((x⁻¹ * γ * x).1 v)) ≤ epN B}`. Rewrite using `[Set.ofPred_forall]`. Conclude with `isClosed_iInter fun v => isClosed_le (hd v) continuous_const`.

Establish `hne : MeasurableSet {x : B.I.GA | phe B d (x⁻¹ * γ * x) ≠ 0}` using `hc.measurable (measurableSet_singleton 0).compl`. Establish `hset : MeasurableSet {x : B.I.GA | γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x}`. Establish `heq : {x : B.I.GA | γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x} = ({x : B.I.GA | γ ∈ B.I.GFset} ∩ ({x : B.I.GA | phe B d (x⁻¹ * γ * x) ≠ 0} ∩ {x : B.I.GA | ∀ v, dHS (uMat ((x⁻¹ * γ * x).1 v)) ≤ epN B})) ∩ {x : B.I.GA | γ ≠ 1}`. Use extensionality with `x`. Both sides reduce to the same expression.

Rewrite using `[heq]`. Conclude with `((MeasurableSet.const _).inter (hne.inter hcl.measurableSet)).inter (MeasurableSet.const _)`. Conclude with `Measurable.indicator hc.enorm.measurable hset`.
-/
private theorem measurable_indicator_nearNe_phe (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : IsDSData B d)
    (γ : B.I.GA) :
    Measurable fun x : B.I.GA =>
      {x : B.I.GA | γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x}.indicator
        (fun x => ‖phe B d (x⁻¹ * γ * x)‖ₑ) x := by
  have hc : Continuous fun x : B.I.GA => phe B d (x⁻¹ * γ * x) :=
    (continuous_phe B d h).comp (continuous_conj_by_inv B γ)
  have hd : ∀ v, Continuous fun x : B.I.GA => dHS (uMat ((x⁻¹ * γ * x).1 v)) := fun v =>
    (GlobalTheory.Count.CartanSize.cartan_size _ (B.I.ε v)).1.comp
      ((continuous_apply v).comp (continuous_fst.comp (continuous_conj_by_inv B γ)))
  have hcl : IsClosed {x : B.I.GA | ∀ v, dHS (uMat ((x⁻¹ * γ * x).1 v)) ≤ epN B} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_le (hd v) continuous_const
  have hne : MeasurableSet {x : B.I.GA | phe B d (x⁻¹ * γ * x) ≠ 0} :=
    hc.measurable (measurableSet_singleton 0).compl
  have hset : MeasurableSet {x : B.I.GA | γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x} := by
    have heq : {x : B.I.GA | γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x} =
        ({x : B.I.GA | γ ∈ B.I.GFset} ∩ ({x : B.I.GA | phe B d (x⁻¹ * γ * x) ≠ 0} ∩
          {x : B.I.GA | ∀ v, dHS (uMat ((x⁻¹ * γ * x).1 v)) ≤ epN B})) ∩ {x : B.I.GA | γ ≠ 1} := by
      ext x
      rfl
    rw [heq]
    exact ((MeasurableSet.const _).inter (hne.inter hcl.measurableSet)).inter (MeasurableSet.const _)
  exact Measurable.indicator hc.enorm.measurable hset

/- English proof (translation)
Introduce `B d h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hcount : Countable B.I.GFset` using `(GlobalTheory.RatDiscrete.countable_GFset B.I).to_subtype`. Establish `heq : GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d = fun x => ∑' γ : B.I.GFset, {x : B.I.GA | γ.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x}.indicator (fun x => ‖phe B d (x⁻¹ * γ.1 * x)‖ₑ) x`. Use function extensionality and compare the values at `x`.

Conclude with `tsum_sub_eq (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x) B.I.GFset (fun γ hγ => hγ.1.1) (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ)`. Rewrite using `[heq]`. Conclude with `Measurable.tsum fun γ => measurable_indicator_nearNe_phe B d h γ.1`. Introduce `x hsum`. Establish `hone : (1 : B.I.GA) ∈ B.I.GFset` using `(GlobalTheory.RatDiscrete.ratSub B.I).one_mem`.

Set `o : B.I.GFset` to `⟨1, hone⟩`. Establish `hs : Summable fun γ : B.I.GFset => phe B d (x⁻¹ * γ.1 * x)` using `hsum.of_norm`. Establish `hk : kern B.I (phe B d) x x = ∑' γ : B.I.GFset, phe B d (x⁻¹ * γ.1 * x)` using `rfl`. Establish `h1 : phe B d 1 = phe B d (x⁻¹ * o.1 * x)` using `by simp [o]`. Rewrite using `[hk, h1, hs.tsum_eq_add_tsum_ite o, add_sub_cancel_left]`.

Establish `hgn : Summable fun γ : B.I.GFset => ‖if γ = o then (0 : ℂ) else phe B d (x⁻¹ * γ.1 * x)‖`. Use `hsum.of_nonneg_of_le (fun _ => norm_nonneg _) fun γ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hγ : γ = o <;> simp [hγ]`. Establish `hsub1 : GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x ⊆ B.I.GFset` using `fun γ hγ => hγ.1.1`. Establish `hsub2 : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSet B d x ⊆ B.I.GFset` using `fun γ hγ => hγ.1`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hgn]`. Simplify using `only [ofReal_norm]`. Use `_ ≤ ∑' γ : B.I.GFset, ((GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x).indicator (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ) γ.1 + (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSet B d x).indicator (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ) γ.1) := by`. Use `ENNReal.tsum_le_tsum fun γ => ?_` and prove the remaining obligations.

Distinguish the cases in `hγ : γ = o`. Simplify using `[hγ]`. Establish `hγ1 : γ.1 ≠ 1` using `fun h' => hγ (Subtype.ext h')`. Rewrite using `[if_neg hγ]`. Distinguish the cases in `hn : IsNear B d (epN B) x γ.1`.

Establish `hm : γ.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x` using `⟨hn, hγ1⟩`. Rewrite using `[Set.indicator_of_mem hm]`. Conclude with `le_self_add`. Establish `hm : γ.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSet B d x` using `⟨γ.2, hn⟩`. Rewrite using `[Set.indicator_of_mem hm]`.

Conclude with `le_add_self`. Use `_ = GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x + GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x := by`. Rewrite using `[ENNReal.tsum_add]`. Conclude with `congrArg₂ (· + ·) (tsum_sub_eq _ _ hsub1 (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ)).symm (tsum_sub_eq _ _ hsub2 (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ)).symm`.
-/
theorem nearAbs_measurable_and_split : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → Measurable (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) ∧ ∀ x : B.I.GA, Summable (fun γ : B.I.GFset => ‖phe B d (x⁻¹ * γ.1 * x)‖) → ENNReal.ofReal ‖kern B.I (phe B d) x x - phe B d 1‖ ≤ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x + GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x := by
  intro B d h
  classical
  refine ⟨?_, ?_⟩
  · have hcount : Countable B.I.GFset := (GlobalTheory.RatDiscrete.countable_GFset B.I).to_subtype
    have heq : GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d = fun x => ∑' γ : B.I.GFset,
        {x : B.I.GA | γ.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x}.indicator
          (fun x => ‖phe B d (x⁻¹ * γ.1 * x)‖ₑ) x := by
      funext x
      exact tsum_sub_eq (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x) B.I.GFset (fun γ hγ => hγ.1.1)
        (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ)
    rw [heq]
    exact Measurable.tsum fun γ => measurable_indicator_nearNe_phe B d h γ.1
  · intro x hsum
    have hone : (1 : B.I.GA) ∈ B.I.GFset := (GlobalTheory.RatDiscrete.ratSub B.I).one_mem
    let o : B.I.GFset := ⟨1, hone⟩
    have hs : Summable fun γ : B.I.GFset => phe B d (x⁻¹ * γ.1 * x) := hsum.of_norm
    have hk : kern B.I (phe B d) x x = ∑' γ : B.I.GFset, phe B d (x⁻¹ * γ.1 * x) := rfl
    have h1 : phe B d 1 = phe B d (x⁻¹ * o.1 * x) := by simp [o]
    rw [hk, h1, hs.tsum_eq_add_tsum_ite o, add_sub_cancel_left]
    have hgn : Summable fun γ : B.I.GFset =>
        ‖if γ = o then (0 : ℂ) else phe B d (x⁻¹ * γ.1 * x)‖ := by
      refine hsum.of_nonneg_of_le (fun _ => norm_nonneg _) fun γ => ?_
      by_cases hγ : γ = o <;> simp [hγ]
    have hsub1 : GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x ⊆ B.I.GFset := fun γ hγ => hγ.1.1
    have hsub2 : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSet B d x ⊆ B.I.GFset := fun γ hγ => hγ.1
    calc ENNReal.ofReal ‖∑' γ : B.I.GFset, if γ = o then (0 : ℂ) else phe B d (x⁻¹ * γ.1 * x)‖
        ≤ ENNReal.ofReal (∑' γ : B.I.GFset,
            ‖if γ = o then (0 : ℂ) else phe B d (x⁻¹ * γ.1 * x)‖) :=
          ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm hgn)
      _ = ∑' γ : B.I.GFset, ‖if γ = o then (0 : ℂ) else phe B d (x⁻¹ * γ.1 * x)‖ₑ := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hgn]
          simp only [ofReal_norm]
      _ ≤ ∑' γ : B.I.GFset,
            ((GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x).indicator (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ) γ.1 +
              (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSet B d x).indicator
                (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ) γ.1) := by
          refine ENNReal.tsum_le_tsum fun γ => ?_
          by_cases hγ : γ = o
          · simp [hγ]
          have hγ1 : γ.1 ≠ 1 := fun h' => hγ (Subtype.ext h')
          rw [if_neg hγ]
          by_cases hn : IsNear B d (epN B) x γ.1
          · have hm : γ.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x := ⟨hn, hγ1⟩
            rw [Set.indicator_of_mem hm]
            exact le_self_add
          · have hm : γ.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSet B d x := ⟨γ.2, hn⟩
            rw [Set.indicator_of_mem hm]
            exact le_add_self
      _ = GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x + GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x := by
          rw [ENNReal.tsum_add]
          exact congrArg₂ (· + ·)
            (tsum_sub_eq _ _ hsub1 (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ)).symm
            (tsum_sub_eq _ _ hsub2 (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ)).symm

end GlobalTheory.NearMeas
