import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantHeisenbergLatticeVacuumFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympDualNbhd

open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in

/- English proof (translation)
Introduce `F _ _ v ψ hψ hne κ _ N hN`. Choose the witnesses or unpack the hypotheses as in `⟨t₀, ht₀⟩ : ∃ t, ψ t ≠ 1 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hne (AddChar.ext _ _ fun t => by rw [h t, AddChar.one_apply])`.

Take `⟨U₀, hU₀⟩` from `_root_.GlobalTheory.HeisLatVac.lc_exists_open_ker ψ hψ`. Take `⟨δ, hδ, hδU⟩` from `Metric.isOpen_iff.mp U₀.isOpen 0 (zero_mem U₀)`. Take `⟨ε, hε, hεN⟩` from `Metric.mem_nhds_iff.mp hN`. Use `set R : ℝ := ‖t₀‖ / ε + 1 with hR`. Establish `hRpos : 0 < R` using `by positivity`.

Establish `hRt : ∀ a : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v, ε ≤ ‖a‖ → ‖t₀‖ / ‖a‖ ≤ R` using `fun a ha => (div_le_div_of_nonneg_left (norm_nonneg _) hε ha).trans (by linarith)`. Set `Y : AddSubgroup ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) × (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))` to `{ carrier := {w | ∀ i, ‖w.1 i‖ ≤ R ∧ ‖w.2 i‖ ≤ R} add_mem' := fun {a b} ha hb i => ⟨(IsUltrametricDist.norm_add_le_max (a.1 i) (b.1 i)).trans (max_le (ha i).1 (hb i).1), (IsUltrametricDist.norm_add_le_max (a.2 i) (b.2 i)).trans (max_le (ha i).2 (hb i).2)⟩ zero_mem' := fun i => by …`. Establish `hmemY : ∀ w, w ∈ Y ↔ ∀ i, ‖w.1 i‖ ≤ R ∧ ‖w.2 i‖ ≤ R` using `fun w => Iff.rfl`. Establish `hsingle : ∀ (i : κ) (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v), ‖y‖ ≤ R → ∀ j, ‖(Pi.single i y : κ → _) j‖ ≤ R`. Introduce `i y hy j`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `using hy`. Simplify using `[Pi.single_apply, hj, hRpos.le]`. Use `⟨Y, ?_, Metric.ball 0 (δ / R), Metric.ball_mem_nhds _ (div_pos hδ hRpos), ?_⟩` and prove the remaining obligations.

Introduce `w' hw'`. Establish `h1 : ∀ i, ‖w'.1 i‖ < ε`. Introduce `i`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Establish `h0 : w'.1 i ≠ 0` using `norm_pos_iff.mp (hε.trans_le h)`. Establish `hy : ((0 : κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v), (Pi.single i (t₀ / w'.1 i) : κ → _)) ∈ Y`. Rewrite using `[hmemY]`. Introduce `j`. Use `⟨by simp [hRpos.le], hsingle i _ ?_ j⟩` and prove the remaining obligations.

Rewrite using `[norm_div]`. Conclude with `hRt _ h`. Use `hw' _ hy` as an intermediate fact. Rewrite `this` using `[dotProduct_single, zero_dotProduct, sub_zero, mul_div_cancel₀ _ h0]`. Conclude with `ht₀ this`.

Establish `h2 : ∀ i, ‖w'.2 i‖ < ε`. Introduce `i`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h0 : w'.2 i ≠ 0` using `norm_pos_iff.mp (hε.trans_le h)`.

Establish `hy : ((Pi.single i (-t₀ / w'.2 i) : κ → _), (0 : κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∈ Y`. Rewrite using `[hmemY]`. Introduce `j`. Use `⟨hsingle i _ ?_ j, by simp [hRpos.le]⟩` and prove the remaining obligations. Rewrite using `[norm_div, norm_neg]`.

Conclude with `hRt _ h`. Use `hw' _ hy` as an intermediate fact. Rewrite `this` using `[single_dotProduct, dotProduct_zero, zero_sub, div_mul_cancel₀ _ h0, neg_neg]`. Conclude with `ht₀ this`. Apply `hεN` to reduce the goal to its premises.

Rewrite using `[mem_ball_zero_iff, Prod.norm_def, max_lt_iff]`. Conclude with `⟨(pi_norm_lt_iff hε).mpr h1, (pi_norm_lt_iff hε).mpr h2⟩`. Introduce `w' hw' w hw`. Rewrite `hw'` using `[mem_ball_zero_iff]`. Rewrite `hw` using `[hmemY]`.

Apply `hU₀` to reduce the goal to its premises. Establish `hsmall : ∀ a b : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v, ‖a‖ < δ / R → ‖b‖ ≤ R → a * b ∈ U₀`. Introduce `a b ha hb`. Apply `hδU` to reduce the goal to its premises. Rewrite using `[mem_ball_zero_iff, norm_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `c1 : ∀ i, ‖w'.1 i‖ < δ / R` using `fun i => ((norm_le_pi_norm w'.1 i).trans (norm_fst_le w')).trans_lt hw'`. Establish `c2 : ∀ i, ‖w'.2 i‖ < δ / R` using `fun i => ((norm_le_pi_norm w'.2 i).trans (norm_snd_le w')).trans_lt hw'`. Use `show ∑ i, w'.1 i * w.2 i - ∑ i, w.1 i * w'.2 i ∈ U₀`. Use `sub_mem (sum_mem fun i _ => hsmall _ _ (c1 i) (hw i).2) (sum_mem fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[mul_comm]`. Conclude with `hsmall _ _ (c2 i) (hw i).1`.
-/
theorem _root_.GlobalTheory.SympDualNbhd.exists_dual_nbhd : ∀ {F : Type} [Field F] [NumberField F]
    (v : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (ψ : AddChar (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ℂ),
    Continuous ψ → ψ ≠ 1 → ∀ {κ : Type} [Fintype κ]
    (N : Set ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) × (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))), N ∈ nhds 0 →
    ∃ Y : AddSubgroup ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) × (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)),
      (∀ w' : (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) × (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v),
        (∀ w ∈ Y, ψ (w'.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ w'.2) = 1) → w' ∈ N) ∧
      ∃ N' ∈ nhds (0 : (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) × (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)),
        ∀ w' ∈ N', ∀ w ∈ Y, ψ (w'.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ w'.2) = 1 := by
  intro F _ _ v ψ hψ hne κ _ N hN
  obtain ⟨t₀, ht₀⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (AddChar.ext _ _ fun t => by rw [h t, AddChar.one_apply])
  obtain ⟨U₀, hU₀⟩ := _root_.GlobalTheory.HeisLatVac.lc_exists_open_ker ψ hψ
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp U₀.isOpen 0 (zero_mem U₀)
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.mp hN
  set R : ℝ := ‖t₀‖ / ε + 1 with hR
  have hRpos : 0 < R := by positivity
  have hRt : ∀ a : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v, ε ≤ ‖a‖ → ‖t₀‖ / ‖a‖ ≤ R := fun a ha =>
    (div_le_div_of_nonneg_left (norm_nonneg _) hε ha).trans (by linarith)
  let Y : AddSubgroup ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) × (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) :=
    { carrier := {w | ∀ i, ‖w.1 i‖ ≤ R ∧ ‖w.2 i‖ ≤ R}
      add_mem' := fun {a b} ha hb i =>
        ⟨(IsUltrametricDist.norm_add_le_max (a.1 i) (b.1 i)).trans (max_le (ha i).1 (hb i).1),
          (IsUltrametricDist.norm_add_le_max (a.2 i) (b.2 i)).trans (max_le (ha i).2 (hb i).2)⟩
      zero_mem' := fun i => by simp [hRpos.le]
      neg_mem' := fun {a} ha i => by simpa using ha i }
  have hmemY : ∀ w, w ∈ Y ↔ ∀ i, ‖w.1 i‖ ≤ R ∧ ‖w.2 i‖ ≤ R := fun w => Iff.rfl
  have hsingle : ∀ (i : κ) (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v), ‖y‖ ≤ R → ∀ j, ‖(Pi.single i y : κ → _) j‖ ≤ R := by
    intro i y hy j
    by_cases hj : j = i
    · subst hj; simpa using hy
    · simp [Pi.single_apply, hj, hRpos.le]
  refine ⟨Y, ?_, Metric.ball 0 (δ / R), Metric.ball_mem_nhds _ (div_pos hδ hRpos), ?_⟩
  · intro w' hw'
    have h1 : ∀ i, ‖w'.1 i‖ < ε := by
      intro i
      by_contra h
      push_neg at h
      have h0 : w'.1 i ≠ 0 := norm_pos_iff.mp (hε.trans_le h)
      have hy : ((0 : κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v), (Pi.single i (t₀ / w'.1 i) : κ → _)) ∈ Y := by
        rw [hmemY]
        intro j
        refine ⟨by simp [hRpos.le], hsingle i _ ?_ j⟩
        rw [norm_div]
        exact hRt _ h
      have := hw' _ hy
      rw [dotProduct_single, zero_dotProduct, sub_zero, mul_div_cancel₀ _ h0] at this
      exact ht₀ this
    have h2 : ∀ i, ‖w'.2 i‖ < ε := by
      intro i
      by_contra h
      push_neg at h
      have h0 : w'.2 i ≠ 0 := norm_pos_iff.mp (hε.trans_le h)
      have hy : ((Pi.single i (-t₀ / w'.2 i) : κ → _), (0 : κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∈ Y := by
        rw [hmemY]
        intro j
        refine ⟨hsingle i _ ?_ j, by simp [hRpos.le]⟩
        rw [norm_div, norm_neg]
        exact hRt _ h
      have := hw' _ hy
      rw [single_dotProduct, dotProduct_zero, zero_sub, div_mul_cancel₀ _ h0, neg_neg] at this
      exact ht₀ this
    apply hεN
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
    exact ⟨(pi_norm_lt_iff hε).mpr h1, (pi_norm_lt_iff hε).mpr h2⟩
  · intro w' hw' w hw
    rw [mem_ball_zero_iff] at hw'
    rw [hmemY] at hw
    apply hU₀
    have hsmall : ∀ a b : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v, ‖a‖ < δ / R → ‖b‖ ≤ R → a * b ∈ U₀ := by
      intro a b ha hb
      apply hδU
      rw [mem_ball_zero_iff, norm_mul]
      calc ‖a‖ * ‖b‖ ≤ ‖a‖ * R := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ < δ / R * R := mul_lt_mul_of_pos_right ha hRpos
        _ = δ := div_mul_cancel₀ _ hRpos.ne'
    have c1 : ∀ i, ‖w'.1 i‖ < δ / R := fun i =>
      ((norm_le_pi_norm w'.1 i).trans (norm_fst_le w')).trans_lt hw'
    have c2 : ∀ i, ‖w'.2 i‖ < δ / R := fun i =>
      ((norm_le_pi_norm w'.2 i).trans (norm_snd_le w')).trans_lt hw'
    show ∑ i, w'.1 i * w.2 i - ∑ i, w.1 i * w'.2 i ∈ U₀
    refine sub_mem (sum_mem fun i _ => hsmall _ _ (c1 i) (hw i).2)
      (sum_mem fun i _ => ?_)
    rw [mul_comm]
    exact hsmall _ _ (c2 i) (hw i).1
