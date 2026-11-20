import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenRankGe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartitionOfUnity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv MeasureTheory
open scoped Topology

noncomputable section

namespace GlobalTheory.FullRankCoinv

variable {k : Type} [Field k]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd]`.
-/
theorem stack_top {ρ e d : ℕ} (Y₁ : Matrix (Fin ρ) (Fin d) k) (Y₂ : Matrix (Fin e) (Fin d) k) :
    ((Matrix.fromRows Y₁ Y₂).submatrix finSumFinEquiv.symm id).submatrix (Fin.castAdd e) id = Y₁ := by
  ext i j; simp [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd]`.
-/
theorem stack_bot {ρ e d : ℕ} (Y₁ : Matrix (Fin ρ) (Fin d) k) (Y₂ : Matrix (Fin e) (Fin d) k) :
    ((Matrix.fromRows Y₁ Y₂).submatrix finSumFinEquiv.symm id).submatrix (Fin.natAdd ρ) id = Y₂ := by
  ext i j; simp [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd]

/- English proof (translation)
Use extensionality with `i j`. Use `Fin.addCases (fun a => ?_) (fun a => ?_) i` and prove the remaining obligations. Simplify using `[Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd]`. Simplify using `[Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd]`.
-/
theorem stack_top_bot {ρ e d : ℕ} (Y : Matrix (Fin (ρ + e)) (Fin d) k) :
    (Matrix.fromRows (Y.submatrix (Fin.castAdd e) id) (Y.submatrix (Fin.natAdd ρ) id)).submatrix
      finSumFinEquiv.symm id = Y := by
  ext i j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · simp [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd]
  · simp [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd]

/- English proof (translation)
Establish `hli : LinearIndependent k Y₁.row`. Rewrite using `[linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]`. Rewrite `hY` using `[Matrix.rank_eq_finrank_span_row]`. Conclude with `hY.symm`. Set `b` to `Module.Basis.sumExtend hli`.

Establish `hfin : Finite (Fin ρ ⊕ Module.Basis.sumExtendIndex hli)` using `Module.Finite.finite_basis b`. Establish `: Finite (Module.Basis.sumExtendIndex hli)` using `Finite.of_injective (Sum.inr : _ → Fin ρ ⊕ _) Sum.inr_injective`. Establish `: Fintype (Module.Basis.sumExtendIndex hli)` using `Fintype.ofFinite _`. Establish `hcard : Fintype.card (Fin ρ ⊕ Module.Basis.sumExtendIndex hli) = d`. Rewrite using `[← Module.finrank_eq_card_basis b, Module.finrank_fin_fun]`.

Establish `hb : ∀ i, b (Sum.inl i) = Y₁.row i`. Introduce `i`. Simplify using `only [b, Module.Basis.sumExtend, Module.Basis.reindex_apply, Module.Basis.coe_extend, Equiv.symm_symm, Equiv.trans_apply, Equiv.sumCongr_apply]`. Both sides reduce to the same expression. Establish `hS : e ≤ Fintype.card (Module.Basis.sumExtendIndex hli)`.

Rewrite `hcard` using `[Fintype.card_sum, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Take `⟨f⟩` from `Function.Embedding.nonempty_of_card_le (α := Fin e) (β := ↥(Module.Basis.sumExtendIndex hli)) (by rw [Fintype.card_fin]; exact hS)`. Use `⟨Matrix.of fun j => b (Sum.inr (f j)), ?_⟩` and prove the remaining obligations. Set `τ : Fin (ρ + e) → Fin ρ ⊕ Module.Basis.sumExtendIndex hli` to `fun i => Sum.map id f (finSumFinEquiv.symm i)`.

Establish `hτ : Function.Injective τ` using `(Sum.map_injective.2 ⟨Function.injective_id, f.injective⟩).comp finSumFinEquiv.symm.injective`. Establish `hrow : ((Matrix.fromRows Y₁ (Matrix.of fun j => b (Sum.inr (f j)))).submatrix finSumFinEquiv.symm id).row = b ∘ τ`. Use function extensionality and compare the values at `i`. Use `Fin.addCases (fun a => ?_) (fun a => ?_) i` and prove the remaining obligations. Use extensionality with `j`.

Simplify using `[τ, Matrix.row, Matrix.submatrix_apply]`. Conclude with `(congrFun (hb a) j).symm`. Use extensionality with `j`. Simplify using `[τ, Matrix.row, Matrix.submatrix_apply]`. Rewrite using `[LinearIndependent.rank_matrix (hrow ▸ b.linearIndependent.comp τ hτ), Fintype.card_fin]`.
-/
theorem exists_stack_rank_eq {ρ e d : ℕ} (h : ρ + e ≤ d) (Y₁ : Matrix (Fin ρ) (Fin d) k) (hY : Y₁.rank = ρ) :
    ∃ Y₂ : Matrix (Fin e) (Fin d) k, ((Matrix.fromRows Y₁ Y₂).submatrix finSumFinEquiv.symm id).rank = ρ + e := by
  classical
  have hli : LinearIndependent k Y₁.row := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    rw [Matrix.rank_eq_finrank_span_row] at hY
    exact hY.symm
  let b := Module.Basis.sumExtend hli
  have hfin : Finite (Fin ρ ⊕ Module.Basis.sumExtendIndex hli) := Module.Finite.finite_basis b
  have : Finite (Module.Basis.sumExtendIndex hli) := Finite.of_injective (Sum.inr : _ → Fin ρ ⊕ _) Sum.inr_injective
  have : Fintype (Module.Basis.sumExtendIndex hli) := Fintype.ofFinite _
  have hcard : Fintype.card (Fin ρ ⊕ Module.Basis.sumExtendIndex hli) = d := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fin_fun]
  have hb : ∀ i, b (Sum.inl i) = Y₁.row i := by
    intro i
    simp only [b, Module.Basis.sumExtend, Module.Basis.reindex_apply, Module.Basis.coe_extend,
      Equiv.symm_symm, Equiv.trans_apply, Equiv.sumCongr_apply]
    rfl
  have hS : e ≤ Fintype.card (Module.Basis.sumExtendIndex hli) := by
    rw [Fintype.card_sum, Fintype.card_fin] at hcard; omega
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := Fin e) (β := ↥(Module.Basis.sumExtendIndex hli))
    (by rw [Fintype.card_fin]; exact hS)
  refine ⟨Matrix.of fun j => b (Sum.inr (f j)), ?_⟩
  let τ : Fin (ρ + e) → Fin ρ ⊕ Module.Basis.sumExtendIndex hli := fun i => Sum.map id f (finSumFinEquiv.symm i)
  have hτ : Function.Injective τ :=
    (Sum.map_injective.2 ⟨Function.injective_id, f.injective⟩).comp finSumFinEquiv.symm.injective
  have hrow : ((Matrix.fromRows Y₁ (Matrix.of fun j => b (Sum.inr (f j)))).submatrix finSumFinEquiv.symm id).row =
      b ∘ τ := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · ext j; simp [τ, Matrix.row, Matrix.submatrix_apply]; exact (congrFun (hb a) j).symm
    · ext j; simp [τ, Matrix.row, Matrix.submatrix_apply]
  rw [LinearIndependent.rank_matrix (hrow ▸ b.linearIndependent.comp τ hτ), Fintype.card_fin]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Use `Fin.addCases (fun a => ?_) (fun a => ?_) i` and prove the remaining obligations. Simplify using `only [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd, Matrix.fromRows_apply_inl, id]`. Conclude with `continuous_fst.matrix_elem a j`. Simplify using `only [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd, Matrix.fromRows_apply_inr, id]`.

Conclude with `continuous_snd.matrix_elem a j`.
-/
theorem continuous_stack {ρ e d : ℕ} : Continuous fun p : Matrix (Fin ρ) (Fin d) k × Matrix (Fin e) (Fin d) k =>
    (Matrix.fromRows p.1 p.2).submatrix finSumFinEquiv.symm id := by
  refine continuous_matrix fun i j => ?_
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd, Matrix.fromRows_apply_inl, id]
    exact continuous_fst.matrix_elem a j
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd, Matrix.fromRows_apply_inr, id]
    exact continuous_snd.matrix_elem a j

/- English proof (translation)
Take `⟨Z₀, hZ₀⟩` from `exists_stack_rank_eq h Y₀ hY`. Establish `hS` using `GlobalTheory.isOpen_setOf_le_rank_localField k (Fin (ρ + e)) (Fin d) (ρ + e)`. Establish `hW` using `hS.preimage (continuous_stack (k := k) (ρ := ρ) (e := e) (d := d))`. Take `⟨U, V', hU, hV', hYU, hZV', hsub⟩` from `isOpen_prod_iff.1 hW Y₀ Z₀ (show ρ + e ≤ _ from hZ₀.ge)`. Establish `h0 : (fun y => Z₀ + y) ⁻¹' V' ∈ 𝓝 (0 : Matrix (Fin e) (Fin d) k)`.

Use `(continuous_const.add continuous_id).continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Simplify using `using hV'.mem_nhds hZV'`. Take `⟨a, ha⟩` from `GlobalTheory.LocMod.Inhab.exists_box_subset h0`. Establish `hBo` using `GlobalTheory.LocMod.Inhab.isOpen_box (Y := Fin e) (Y' := Fin d) (k := k) a`. Establish `hBc : IsClosed ((GlobalTheory.LocMod.Inhab.box (Fin e) (Fin d) a : AddSubgroup (Matrix (Fin e) (Fin d) k)) : Set (Matrix (Fin e) (Fin d) k))` using `AddSubgroup.isClosed_of_isOpen _ hBo`.

Use `⟨U, hU, hYU, (Homeomorph.subRight Z₀) ⁻¹' (GlobalTheory.LocMod.Inhab.box (Fin e) (Fin d) a : Set _), hBo.preimage (Homeomorph.subRight Z₀).continuous, hBc.preimage (Homeomorph.subRight Z₀).continuous, (Homeomorph.subRight Z₀).isCompact_preimage.2 (GlobalTheory.LocMod.Inhab.isComp …` and prove the remaining obligations. Use `show Z₀ - Z₀ ∈ (GlobalTheory.LocMod.Inhab.box (Fin e) (Fin d) a : Set (Matrix (Fin e) (Fin d) k))`. Rewrite using `[sub_self]`. Conclude with `(GlobalTheory.LocMod.Inhab.box (Fin e) (Fin d) a).zero_mem`. Establish `hZ' : Z₀ + (Z - Z₀) ∈ V'` using `ha (Z - Z₀) hZ`.

Rewrite `hZ'` using `[add_sub_cancel]`. Establish `hm` using `hsub (Set.mk_mem_prod hY hZ')`. Rewrite `hm` using `[Set.mem_preimage, Set.mem_setOf_eq]`. Conclude with `hm`.
-/
theorem exists_nhds_stack_rank {ρ e d : ℕ} (h : ρ + e ≤ d) (Y₀ : Matrix (Fin ρ) (Fin d) k) (hY : Y₀.rank = ρ) :
    ∃ U : Set (Matrix (Fin ρ) (Fin d) k), IsOpen U ∧ Y₀ ∈ U ∧ ∃ V : Set (Matrix (Fin e) (Fin d) k),
      IsOpen V ∧ IsClosed V ∧ IsCompact V ∧ V.Nonempty ∧
      ∀ Y ∈ U, ∀ Z ∈ V, ρ + e ≤ ((Matrix.fromRows Y Z).submatrix finSumFinEquiv.symm id).rank := by
  obtain ⟨Z₀, hZ₀⟩ := exists_stack_rank_eq h Y₀ hY
  have hS := GlobalTheory.isOpen_setOf_le_rank_localField k (Fin (ρ + e)) (Fin d) (ρ + e)
  have hW := hS.preimage (continuous_stack (k := k) (ρ := ρ) (e := e) (d := d))
  obtain ⟨U, V', hU, hV', hYU, hZV', hsub⟩ := isOpen_prod_iff.1 hW Y₀ Z₀ (show ρ + e ≤ _ from hZ₀.ge)
  have h0 : (fun y => Z₀ + y) ⁻¹' V' ∈ 𝓝 (0 : Matrix (Fin e) (Fin d) k) := by
    refine (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds ?_
    simpa using hV'.mem_nhds hZV'
  obtain ⟨a, ha⟩ := GlobalTheory.LocMod.Inhab.exists_box_subset h0
  have hBo := GlobalTheory.LocMod.Inhab.isOpen_box (Y := Fin e) (Y' := Fin d) (k := k) a
  have hBc : IsClosed ((GlobalTheory.LocMod.Inhab.box (Fin e) (Fin d) a : AddSubgroup (Matrix (Fin e) (Fin d) k)) :
      Set (Matrix (Fin e) (Fin d) k)) := AddSubgroup.isClosed_of_isOpen _ hBo
  refine ⟨U, hU, hYU, (Homeomorph.subRight Z₀) ⁻¹' (GlobalTheory.LocMod.Inhab.box (Fin e) (Fin d) a : Set _),
    hBo.preimage (Homeomorph.subRight Z₀).continuous, hBc.preimage (Homeomorph.subRight Z₀).continuous,
    (Homeomorph.subRight Z₀).isCompact_preimage.2 (GlobalTheory.LocMod.Inhab.isCompact_box a),
    ⟨Z₀, ?_⟩, fun Y hY Z hZ => ?_⟩
  · show Z₀ - Z₀ ∈ (GlobalTheory.LocMod.Inhab.box (Fin e) (Fin d) a : Set (Matrix (Fin e) (Fin d) k))
    rw [sub_self]; exact (GlobalTheory.LocMod.Inhab.box (Fin e) (Fin d) a).zero_mem
  · have hZ' : Z₀ + (Z - Z₀) ∈ V' := ha (Z - Z₀) hZ
    rw [add_sub_cancel] at hZ'
    have hm := hsub (Set.mk_mem_prod hY hZ')
    rw [Set.mem_preimage, Set.mem_setOf_eq] at hm
    exact hm

end GlobalTheory.FullRankCoinv

namespace GlobalTheory.FullRankCoinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `set c : ℂ := ((μ.real V : ℝ) : ℂ)⁻¹ with hc`. Establish `hpos : 0 < μ V` using `hVo.measure_pos μ hVne`. Establish `hfin : μ V < ⊤` using `hVc.measure_lt_top`. Establish `hreal : ((μ.real V : ℝ) : ℂ) ≠ 0`. Rewrite using `[Complex.ofReal_ne_zero, Measure.real, ENNReal.toReal_ne_zero]`.

Conclude with `⟨hpos.ne', hfin.ne⟩`. Establish `hVm : MeasurableSet V` using `hVo.measurableSet`. Set `ind : Matrix (Fin e) (Fin d) k → ℂ` to `V.indicator fun _ => c`. Establish `hind : IsLocallyConstant ind`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`.

Introduce `x`. Distinguish the cases in `hx : x ∈ V`. Use `filter_upwards [hVo.mem_nhds hx] with y hy`. Simplify using `[ind, hx, hy]`. Use `filter_upwards [hVcl.isOpen_compl.mem_nhds hx] with y hy`.

Establish `hy' : y ∉ V` using `hy`. Simplify using `[ind, hx, hy']`. Establish `htop : Continuous fun Y : Matrix (Fin (ρ + e)) (Fin d) k => Y.submatrix (Fin.castAdd e) id` using `continuous_id.matrix_submatrix _ _`. Establish `hbot : Continuous fun Y : Matrix (Fin (ρ + e)) (Fin d) k => Y.submatrix (Fin.natAdd ρ) id` using `continuous_id.matrix_submatrix _ _`. Set `Θ : Matrix (Fin (ρ + e)) (Fin d) k → ℂ` to `fun Y => g (Y.submatrix (Fin.castAdd e) id) * ind (Y.submatrix (Fin.natAdd ρ) id)`.

Establish `hΘslice : ∀ Y₁ Y₂, Θ ((Matrix.fromRows Y₁ Y₂).submatrix finSumFinEquiv.symm id) = g Y₁ * ind Y₂` using `fun Y₁ Y₂ => by simp only [Θ, stack_top, stack_bot]`. Establish `hΘne : ∀ Y, Θ Y ≠ 0 → Y.submatrix (Fin.castAdd e) id ∈ U ∧ Y.submatrix (Fin.natAdd ρ) id ∈ V`. Introduce `Y hY`. Establish `h1 : g (Y.submatrix (Fin.castAdd e) id) ≠ 0` using `left_ne_zero_of_mul hY`. Establish `h2 : ind (Y.submatrix (Fin.natAdd ρ) id) ≠ 0` using `right_ne_zero_of_mul hY`.

Use `⟨hgU _ h1, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Conclude with `h2 (by simp [ind, hn])`. Establish `hlc : IsLocallyConstant Θ` using `(hg.1.comp_continuous htop).mul (hind.comp_continuous hbot)`. Use `⟨Θ, ⟨⟨hlc, ?_⟩, fun Y hY => ?_⟩, fun Y₁ => ?_, fun Y₁ => ?_⟩` and prove the remaining obligations.

Establish `hF` using `continuous_stack (k := k) (ρ := ρ) (e := e) (d := d)`. Use `HasCompactSupport.intro ((hg.2.isCompact.prod hVc).image hF) fun Y hY => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨-, h2⟩` from `hΘne Y hne`. Apply `hY` to reduce the goal to its premises.

Use `⟨(Y.submatrix (Fin.castAdd e) id, Y.submatrix (Fin.natAdd ρ) id), ⟨subset_tsupport _ (left_ne_zero_of_mul hne), h2⟩, stack_top_bot Y⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨h1, h2⟩` from `hΘne Y hne`. Establish `h3` using `hUV _ h1 _ h2`. Rewrite `h3` using `[stack_top_bot]`.

Establish `h4` using `Matrix.rank_le_card_height Y`. Rewrite `h4` using `[Fintype.card_fin]`. Conclude with `hY (le_antisymm h4 h3)`. Simplify using `only [hΘslice]`. Conclude with `((integrableOn_const hfin.ne : IntegrableOn (fun _ => c) V μ).integrable_indicator hVm).const_mul (g Y₁)`.

Simplify using `only [hΘslice]`. Rewrite using `[integral_const_mul, integral_indicator_const _ hVm, Complex.real_smul, hc, mul_inv_cancel₀ hreal, mul_one]`.
-/
theorem exists_fibre_piece {ρ e d : ℕ} [MeasurableSpace (Matrix (Fin e) (Fin d) k)]
    [BorelSpace (Matrix (Fin e) (Fin d) k)] (μ : Measure (Matrix (Fin e) (Fin d) k)) [μ.IsAddHaarMeasure]
    {U : Set (Matrix (Fin ρ) (Fin d) k)} {V : Set (Matrix (Fin e) (Fin d) k)}
    (hVo : IsOpen V) (hVcl : IsClosed V) (hVc : IsCompact V) (hVne : V.Nonempty)
    (hUV : ∀ Y ∈ U, ∀ Z ∈ V, ρ + e ≤ ((Matrix.fromRows Y Z).submatrix finSumFinEquiv.symm id).rank)
    {g : Matrix (Fin ρ) (Fin d) k → ℂ} (hg : g ∈ SB (Matrix (Fin ρ) (Fin d) k)) (hgU : ∀ Y, g Y ≠ 0 → Y ∈ U) :
    ∃ Θ ∈ fullRk k (ρ + e) d,
      (∀ Y₁, Integrable (fun Y₂ => Θ ((Matrix.fromRows Y₁ Y₂).submatrix finSumFinEquiv.symm id)) μ) ∧
      ∀ Y₁, ∫ Y₂, Θ ((Matrix.fromRows Y₁ Y₂).submatrix finSumFinEquiv.symm id) ∂μ = g Y₁ := by
  classical
  set c : ℂ := ((μ.real V : ℝ) : ℂ)⁻¹ with hc
  have hpos : 0 < μ V := hVo.measure_pos μ hVne
  have hfin : μ V < ⊤ := hVc.measure_lt_top
  have hreal : ((μ.real V : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨hpos.ne', hfin.ne⟩
  have hVm : MeasurableSet V := hVo.measurableSet
  let ind : Matrix (Fin e) (Fin d) k → ℂ := V.indicator fun _ => c
  have hind : IsLocallyConstant ind := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ V
    · filter_upwards [hVo.mem_nhds hx] with y hy
      simp [ind, hx, hy]
    · filter_upwards [hVcl.isOpen_compl.mem_nhds hx] with y hy
      have hy' : y ∉ V := hy
      simp [ind, hx, hy']
  have htop : Continuous fun Y : Matrix (Fin (ρ + e)) (Fin d) k => Y.submatrix (Fin.castAdd e) id :=
    continuous_id.matrix_submatrix _ _
  have hbot : Continuous fun Y : Matrix (Fin (ρ + e)) (Fin d) k => Y.submatrix (Fin.natAdd ρ) id :=
    continuous_id.matrix_submatrix _ _
  let Θ : Matrix (Fin (ρ + e)) (Fin d) k → ℂ := fun Y =>
    g (Y.submatrix (Fin.castAdd e) id) * ind (Y.submatrix (Fin.natAdd ρ) id)
  have hΘslice : ∀ Y₁ Y₂, Θ ((Matrix.fromRows Y₁ Y₂).submatrix finSumFinEquiv.symm id) = g Y₁ * ind Y₂ :=
    fun Y₁ Y₂ => by simp only [Θ, stack_top, stack_bot]
  have hΘne : ∀ Y, Θ Y ≠ 0 → Y.submatrix (Fin.castAdd e) id ∈ U ∧ Y.submatrix (Fin.natAdd ρ) id ∈ V := by
    intro Y hY
    have h1 : g (Y.submatrix (Fin.castAdd e) id) ≠ 0 := left_ne_zero_of_mul hY
    have h2 : ind (Y.submatrix (Fin.natAdd ρ) id) ≠ 0 := right_ne_zero_of_mul hY
    refine ⟨hgU _ h1, ?_⟩
    by_contra hn
    exact h2 (by simp [ind, hn])
  have hlc : IsLocallyConstant Θ := (hg.1.comp_continuous htop).mul (hind.comp_continuous hbot)
  refine ⟨Θ, ⟨⟨hlc, ?_⟩, fun Y hY => ?_⟩, fun Y₁ => ?_, fun Y₁ => ?_⟩
  · have hF := continuous_stack (k := k) (ρ := ρ) (e := e) (d := d)
    refine HasCompactSupport.intro ((hg.2.isCompact.prod hVc).image hF) fun Y hY => ?_
    by_contra hne
    obtain ⟨-, h2⟩ := hΘne Y hne
    apply hY
    refine ⟨(Y.submatrix (Fin.castAdd e) id, Y.submatrix (Fin.natAdd ρ) id),
      ⟨subset_tsupport _ (left_ne_zero_of_mul hne), h2⟩, stack_top_bot Y⟩
  · by_contra hne
    obtain ⟨h1, h2⟩ := hΘne Y hne
    have h3 := hUV _ h1 _ h2
    rw [stack_top_bot] at h3
    have h4 := Matrix.rank_le_card_height Y
    rw [Fintype.card_fin] at h4
    exact hY (le_antisymm h4 h3)
  · simp only [hΘslice]
    exact ((integrableOn_const hfin.ne : IntegrableOn (fun _ => c) V μ).integrable_indicator hVm).const_mul (g Y₁)
  · simp only [hΘslice]
    rw [integral_const_mul, integral_indicator_const _ hVm, Complex.real_smul, hc, mul_inv_cancel₀ hreal, mul_one]

/- English proof (translation)
Introduce `k _ _ _ _ ρ e d _ _ μ _ hρe θ hθ`. Set `P : (Matrix (Fin ρ) (Fin d) k → ℂ) → Prop` to `fun g => ∃ Θ ∈ fullRk k (ρ + e) d, (∀ Y₁, Integrable (fun Y₂ => Θ ((Matrix.fromRows Y₁ Y₂).submatrix finSumFinEquiv.symm id)) μ) ∧ ∀ Y₁, ∫ Y₂, Θ ((Matrix.fromRows Y₁ Y₂).submatrix finSumFinEquiv.symm id) ∂μ = g Y₁`. Establish `hcl : IsClosed (Function.support θ)`. Establish `: Function.support θ = (θ ⁻¹' {0})ᶜ` using `by ext; simp`. Rewrite using `[this]`.

Conclude with `(hθ.1.1.isOpen_fiber 0).isClosed_compl`. Establish `hcpt : IsCompact (Function.support θ)`. Use `hθ.1.2` as an intermediate fact. Rewrite `this` using `[HasCompactSupport, tsupport, hcl.closure_eq]`. Conclude with `this`.

Establish `hloc : ∀ x : Function.support θ, ∃ U : Set (Matrix (Fin ρ) (Fin d) k), IsOpen U ∧ (x : Matrix (Fin ρ) (Fin d) k) ∈ U ∧ ∃ V : Set (Matrix (Fin e) (Fin d) k), IsOpen V ∧ IsClosed V ∧ IsCompact V ∧ V.Nonempty ∧ ∀ Y ∈ U, ∀ Z ∈ V, ρ + e ≤ ((Matrix.fromRows Y Z).submatrix finSumFinEqui …` using `fun x => exists_nhds_stack_rank hρe x.1 (by by_contra h; exact x.2 (hθ.2 _ h))`. Use `choose U hU using hloc`. Take `⟨t, ht⟩` from `hcpt.elim_finite_subcover U (fun i => (hU i).1) fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, (hU _).2.1⟩`. Establish `hspan` using `GlobalTheory.CoverSB.mem_span_of_cover k (Fin ρ) (Fin d) {i // i ∈ t} (fun i => U i.1) (fun i => (hU _).1) θ hθ.1 fun Y hY => by`. Take `⟨i, hi, hYi⟩` from `Set.mem_iUnion₂.1 (ht hY)`.

Conclude with `⟨⟨i, hi⟩, hYi⟩`. Establish `hP : P θ`. Use `Submodule.span_induction (p := fun g _ => P g) ?_ ?_ ?_ ?_ hspan` and prove the remaining obligations. Introduce and unpack `g ⟨hg, i, hgi⟩`. Take `⟨-, -, V, hVo, hVcl, hVc, hVne, hUV⟩` from `hU i.1`.

Conclude with `exists_fibre_piece μ hVo hVcl hVc hVne hUV hg hgi`. Conclude with `⟨0, Submodule.zero_mem _, fun _ => integrable_zero _ _ _, fun _ => by simp⟩`. Introduce and unpack `g₁ g₂ - - ⟨Θ₁, h₁, i₁, e₁⟩ ⟨Θ₂, h₂, i₂, e₂⟩`. Use `⟨Θ₁ + Θ₂, Submodule.add_mem _ h₁ h₂, fun Y₁ => (i₁ Y₁).add (i₂ Y₁), fun Y₁ => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply]`.

Rewrite using `[integral_add (i₁ Y₁) (i₂ Y₁), e₁, e₂]`. Introduce and unpack `a g - ⟨Θ, h, i, e'⟩`. Use `⟨a • Θ, Submodule.smul_mem _ a h, fun Y₁ => (i Y₁).smul a, fun Y₁ => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply]`. Rewrite using `[integral_smul, e']`.

Take `⟨Θ, hΘ, -, hint⟩` from `hP`. Conclude with `⟨Θ, hΘ, hint⟩`.
-/
theorem exists_fullRk_fibre_integral_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ρ e d : ℕ)
    [MeasurableSpace (Matrix (Fin e) (Fin d) k)] [BorelSpace (Matrix (Fin e) (Fin d) k)]
    (μ : Measure (Matrix (Fin e) (Fin d) k)) [μ.IsAddHaarMeasure], ρ + e ≤ d →
    ∀ θ ∈ fullRk k ρ d, ∃ Θ ∈ fullRk k (ρ + e) d, ∀ Y₁ : Matrix (Fin ρ) (Fin d) k,
      ∫ Y₂, Θ ((Matrix.fromRows Y₁ Y₂).submatrix finSumFinEquiv.symm id) ∂μ = θ Y₁ := by
  intro k _ _ _ _ ρ e d _ _ μ _ hρe θ hθ
  classical
  let P : (Matrix (Fin ρ) (Fin d) k → ℂ) → Prop := fun g => ∃ Θ ∈ fullRk k (ρ + e) d,
    (∀ Y₁, Integrable (fun Y₂ => Θ ((Matrix.fromRows Y₁ Y₂).submatrix finSumFinEquiv.symm id)) μ) ∧
    ∀ Y₁, ∫ Y₂, Θ ((Matrix.fromRows Y₁ Y₂).submatrix finSumFinEquiv.symm id) ∂μ = g Y₁
  have hcl : IsClosed (Function.support θ) := by
    have : Function.support θ = (θ ⁻¹' {0})ᶜ := by ext; simp
    rw [this]; exact (hθ.1.1.isOpen_fiber 0).isClosed_compl
  have hcpt : IsCompact (Function.support θ) := by
    have := hθ.1.2
    rw [HasCompactSupport, tsupport, hcl.closure_eq] at this
    exact this
  have hloc : ∀ x : Function.support θ, ∃ U : Set (Matrix (Fin ρ) (Fin d) k), IsOpen U ∧
      (x : Matrix (Fin ρ) (Fin d) k) ∈ U ∧ ∃ V : Set (Matrix (Fin e) (Fin d) k),
      IsOpen V ∧ IsClosed V ∧ IsCompact V ∧ V.Nonempty ∧
      ∀ Y ∈ U, ∀ Z ∈ V, ρ + e ≤ ((Matrix.fromRows Y Z).submatrix finSumFinEquiv.symm id).rank :=
    fun x => exists_nhds_stack_rank hρe x.1 (by by_contra h; exact x.2 (hθ.2 _ h))
  choose U hU using hloc
  obtain ⟨t, ht⟩ := hcpt.elim_finite_subcover U (fun i => (hU i).1)
    fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, (hU _).2.1⟩
  have hspan := GlobalTheory.CoverSB.mem_span_of_cover k (Fin ρ) (Fin d) {i // i ∈ t} (fun i => U i.1)
    (fun i => (hU _).1) θ hθ.1 fun Y hY => by
      obtain ⟨i, hi, hYi⟩ := Set.mem_iUnion₂.1 (ht hY)
      exact ⟨⟨i, hi⟩, hYi⟩
  have hP : P θ := by
    refine Submodule.span_induction (p := fun g _ => P g) ?_ ?_ ?_ ?_ hspan
    · rintro g ⟨hg, i, hgi⟩
      obtain ⟨-, -, V, hVo, hVcl, hVc, hVne, hUV⟩ := hU i.1
      exact exists_fibre_piece μ hVo hVcl hVc hVne hUV hg hgi
    · exact ⟨0, Submodule.zero_mem _, fun _ => integrable_zero _ _ _, fun _ => by simp⟩
    · rintro g₁ g₂ - - ⟨Θ₁, h₁, i₁, e₁⟩ ⟨Θ₂, h₂, i₂, e₂⟩
      refine ⟨Θ₁ + Θ₂, Submodule.add_mem _ h₁ h₂, fun Y₁ => (i₁ Y₁).add (i₂ Y₁), fun Y₁ => ?_⟩
      simp only [Pi.add_apply]
      rw [integral_add (i₁ Y₁) (i₂ Y₁), e₁, e₂]
    · rintro a g - ⟨Θ, h, i, e'⟩
      refine ⟨a • Θ, Submodule.smul_mem _ a h, fun Y₁ => (i Y₁).smul a, fun Y₁ => ?_⟩
      simp only [Pi.smul_apply]
      rw [integral_smul, e']
  obtain ⟨Θ, hΘ, -, hint⟩ := hP
  exact ⟨Θ, hΘ, hint⟩

end GlobalTheory.FullRankCoinv
