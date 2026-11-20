import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableMajorantCoordinateCosetMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalShStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Pointwise

noncomputable section

namespace GlobalTheory.MajSum

variable {D : D7}

/- English proof (translation)
Unfold `realSize`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations. Establish `: Formalism.IndefR.Datum.compAt θ τ (x + y) i j = Formalism.IndefR.Datum.compAt θ τ x i j + Formalism.IndefR.Datum.compAt θ τ y i j` using `by show θ τ (infPart D (x i j + y i j)) = θ τ (infPart D (x i j)) + θ τ (infPart D (y i j))`. Rewrite using `[RingHom.map_add (infPart D), RingHom.map_add (θ τ)]`. Rewrite using `[this]`.

Conclude with `norm_add_le _ _`.
-/
theorem realSize_add_le (θ : InfFam D) {m n : ℕ} (x y : Mx D m n) :
    realSize θ (x + y) ≤ realSize θ x + realSize θ y := by
  unfold realSize
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have : Formalism.IndefR.Datum.compAt θ τ (x + y) i j =
      Formalism.IndefR.Datum.compAt θ τ x i j + Formalism.IndefR.Datum.compAt θ τ y i j := by
    show θ τ (infPart D (x i j + y i j)) = θ τ (infPart D (x i j)) + θ τ (infPart D (y i j))
    rw [RingHom.map_add (infPart D), RingHom.map_add (θ τ)]
  rw [this]
  exact norm_add_le _ _

/- English proof (translation)
Unfold `maj`. Distinguish the cases in `hγ : InBox K γ`. Establish `hbox : InBox (K + C) (γ + w)`. Take `⟨k, hk, hk0⟩` from `hγ`. Use `⟨k + w, Set.add_mem_add hk hwC, ?_⟩` and prove the remaining obligations.

Establish `: γ + w - (k + w) = γ - k` using `by abel`. Rewrite using `[this]`. Conclude with `hk0`. Rewrite using `[if_pos hγ, if_pos hbox]`. Establish `h0` using `realSize_nonneg θ γ`.

Establish `h1` using `realSize_nonneg θ (γ + w)`. Establish `h2 : 1 + realSize θ (γ + w) ≤ 2 * (1 + realSize θ γ)`. Use `realSize_add_le θ γ w` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp : (0:ℝ) < (1 + realSize θ (γ + w)) ^ N` using `by positivity`.

Establish `hq : (0:ℝ) < (1 + realSize θ γ) ^ N` using `by positivity`. Rewrite using `[← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hq hp, one_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[if_neg hγ]`. Use `maj_nonneg θ (K + C) N (γ + w)` as an intermediate fact.

Unfold `maj at this`. Check the signs of the components of the expression.
-/
theorem maj_le_shift (θ : InfFam D) {m n : ℕ} (K C : Set (Mx D m n)) (N : ℕ) (γ w : Mx D m n)
    (hwC : w ∈ C) (hw : realSize θ w ≤ 1) :
    maj θ K N γ ≤ 2 ^ N * maj θ (K + C) N (γ + w) := by
  unfold maj
  by_cases hγ : InBox K γ
  · have hbox : InBox (K + C) (γ + w) := by
      obtain ⟨k, hk, hk0⟩ := hγ
      refine ⟨k + w, Set.add_mem_add hk hwC, ?_⟩
      have : γ + w - (k + w) = γ - k := by abel
      rw [this]; exact hk0
    rw [if_pos hγ, if_pos hbox]
    have h0 := realSize_nonneg θ γ
    have h1 := realSize_nonneg θ (γ + w)
    have h2 : 1 + realSize θ (γ + w) ≤ 2 * (1 + realSize θ γ) := by
      have := realSize_add_le θ γ w; linarith
    have hp : (0:ℝ) < (1 + realSize θ (γ + w)) ^ N := by positivity
    have hq : (0:ℝ) < (1 + realSize θ γ) ^ N := by positivity
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hq hp, one_mul]
    calc (1 + realSize θ (γ + w)) ^ N ≤ (2 * (1 + realSize θ γ)) ^ N := by gcongr
      _ = 2 ^ N * (1 + realSize θ γ) ^ N := by rw [mul_pow]
  · rw [if_neg hγ]
    have := maj_nonneg θ (K + C) N (γ + w)
    unfold maj at this
    positivity

end GlobalTheory.MajSum

namespace GlobalTheory.MajSum

/- English proof (translation)
Establish `h : ∀ τ (i : Fin m) (j : Fin n), Formalism.IndefR.Datum.compAt θ τ (0 : Mx D m n) i j = 0`. Introduce `τ i j`. Use `show θ τ (infPart D 0) = 0`. Rewrite using `[RingHom.map_zero (infPart D), RingHom.map_zero (θ τ)]`. Unfold `realSize`.

Simplify using `only [h, norm_zero, Finset.sum_const_zero]`.
-/
theorem realSize_zero {D : D7} (θ : InfFam D) {m n : ℕ} : realSize θ (0 : Mx D m n) = 0 := by
  have h : ∀ τ (i : Fin m) (j : Fin n), Formalism.IndefR.Datum.compAt θ τ (0 : Mx D m n) i j = 0 := by
    intro τ i j
    show θ τ (infPart D 0) = 0
    rw [RingHom.map_zero (infPart D), RingHom.map_zero (θ τ)]
  unfold realSize
  simp only [h, norm_zero, Finset.sum_const_zero]

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `D θ hθ m n`. Take `⟨i1, i2, i3, i4, i5, -⟩` from `lattice_Mx D m n`. Use `haveI : BorelSpace (Mx D m n) := ⟨rfl⟩`. Use `haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance`. Set `μ : Measure (Mx D m n)` to `Measure.addHaar`.

Establish `hcont : Continuous (realSize θ : Mx D m n → ℝ)` using `((GlobalTheory.T.adelicMatrixSchwartzMajorant_measurable_rationalShift D θ hθ).1 m n ∅ isCompact_empty).2.1`. Take `⟨N, hN⟩` from `GlobalTheory.T.integrable_majorant_coordinate_coset_measure D θ hθ m n (fun _ _ => True) 0 μ inferInstance (Filter.Eventually.of_forall fun x i j h => (h trivial).elim) (fun t _ => by`. Establish `e : (fun x : Mx D m n => x + t) = fun x => t + x` using `funext fun x => add_comm x t`. Rewrite using `[e]`. Conclude with `map_add_left_eq_self μ t)`.

Use `⟨N, fun K hK => ?_⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨U, hUo, hU⟩ : ∃ U : Set (Mx D m n), IsOpen U ∧ ∀ γ ∈ ratMx D m n, γ ∈ U ↔ γ = 0 := by`. Establish `h0 : IsOpen ({0} : Set (ratMx D m n))` using `@isOpen_discrete (ratMx D m n) _ i5 _`. Take `⟨U, hUo, hUe⟩` from `isOpen_induced_iff.mp h0`. Use `⟨U, hUo, fun γ hγ => ?_⟩` and prove the remaining obligations.

Use `Set.ext_iff.mp hUe ⟨γ, hγ⟩` as an intermediate fact. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff] at this`. Rewrite using `[this]`. Conclude with `⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩`. Establish `h0U : (0 : Mx D m n) ∈ U` using `(hU 0 (zero_mem _)).2 rfl`.

Establish `hsub : {p : Mx D m n × Mx D m n | p.1 - p.2 ∈ U} ∈ nhds ((0 : Mx D m n), (0 : Mx D m n))`. Establish `hc : Continuous fun p : Mx D m n × Mx D m n => p.1 - p.2` using `continuous_fst.sub continuous_snd`. Use `hc.continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Simplify using `using hUo.mem_nhds h0U`. Take `⟨A, hA, B, hB, hAB⟩` from `mem_nhds_prod_iff.mp hsub`.

Take `⟨C, hCc, hC⟩` from `exists_compact_mem_nhds (0 : Mx D m n)`. Establish `hR : {w : Mx D m n | realSize θ w < 1} ∈ nhds (0 : Mx D m n)`. Use `(isOpen_lt hcont continuous_const).mem_nhds ?_` and prove the remaining obligations. Use `show realSize θ (0 : Mx D m n) < 1`. Rewrite using `[realSize_zero]`.

Conclude with `one_pos`. Use `set W := interior (A ∩ B ∩ C ∩ {w : Mx D m n | realSize θ w < 1}) with hWdef`. Establish `hW0 : (0 : Mx D m n) ∈ W` using `mem_interior_iff_mem_nhds.2 (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hA hB) hC) hR)`. Establish `hμW : μ W ≠ 0` using `(isOpen_interior.measure_pos μ ⟨0, hW0⟩).ne'`. Set `s : ratMx D m n → Set (Mx D m n)` to `fun γ => (fun x => -(γ : Mx D m n) + x) ⁻¹' W`.

Establish `hs : ∀ γ, MeasurableSet (s γ)` using `fun γ => (isOpen_interior.preimage (continuous_const.add continuous_id)).measurableSet`. Establish `hdisj : Pairwise (Function.onFun Disjoint s)`. Introduce `γ γ' hne`. Use `Set.disjoint_left.2 fun x hx hx' => hne ?_` and prove the remaining obligations. Establish `hxA : -(γ : Mx D m n) + x ∈ A` using `(interior_subset hx).1.1.1`.

Establish `hxB : -(γ' : Mx D m n) + x ∈ B` using `(interior_subset hx').1.1.2`. Establish `hmem : (-(γ : Mx D m n) + x, -(γ' : Mx D m n) + x) ∈ {p : Mx D m n × Mx D m n | p.1 - p.2 ∈ U}` using `hAB ⟨hxA, hxB⟩`. Simplify using `only [Set.mem_setOf_eq] at hmem`. Establish `e : -(γ : Mx D m n) + x - (-(γ' : Mx D m n) + x) = (γ' : Mx D m n) - γ` using `by abel`. Rewrite `hmem` using `[e]`.

Use `(hU _ (sub_mem γ'.2 γ.2)).1 hmem` as an intermediate fact. Conclude with `Subtype.ext (sub_eq_zero.1 this).symm`. Use `set K' := K + C`. Establish `hK' : IsCompact K'` using `hK.add hCc`. Establish `hfin : ∫⁻ x, ENNReal.ofReal (maj θ K' N x) ∂μ < ⊤` using `(hN K' hK').lintegral_lt_top`.

Establish `key : ∀ γ : ratMx D m n, ENNReal.ofReal (maj θ K N γ) * μ W ≤ 2 ^ N * ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ`. Introduce `γ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[setLIntegral_const]`. Use `congr 1`.

Conclude with `(measure_preimage_add μ (-(γ : Mx D m n)) W).symm`. Use `_ ≤ ∫⁻ x in s γ, 2 ^ N * ENNReal.ofReal (maj θ K' N x) ∂μ := by`. Use `setLIntegral_mono' (hs γ) fun x hx => ?_` and prove the remaining obligations. Establish `hw` using `interior_subset hx`. Establish `h1` using `maj_le_shift θ K C N (γ : Mx D m n) (-(γ : Mx D m n) + x) hw.1.2 (le_of_lt hw.2)`.

Rewrite `h1` using `[add_neg_cancel_left]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]`. Use `_ = 2 ^ N * ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ := lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)`. Establish `hsum : (∑' γ : ratMx D m n, ENNReal.ofReal (maj θ K N γ)) * μ W ≤ 2 ^ N * ∫⁻ x, ENNReal.ofReal (maj θ K' N x) ∂μ`.

Rewrite using `[← ENNReal.tsum_mul_right]`. Combine the equalities or inequalities in the displayed calculation. Introduce `htop`. Rewrite `hsum` using `[htop, ENNReal.top_mul hμW]`. Conclude with `(ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofNat_lt_top) hfin).ne (top_le_iff.1 hsum)`.
-/
theorem tsum_maj_ne_top : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ m n : ℕ, ∃ N : ℕ, ∀ K : Set (Mx D m n), IsCompact K →
    (∑' y : ratMx D m n, ENNReal.ofReal (maj θ K N y)) ≠ ⊤ := by
  intro D θ hθ m n
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let μ : Measure (Mx D m n) := Measure.addHaar
  have hcont : Continuous (realSize θ : Mx D m n → ℝ) :=
    ((GlobalTheory.T.adelicMatrixSchwartzMajorant_measurable_rationalShift D θ hθ).1 m n ∅ isCompact_empty).2.1
  obtain ⟨N, hN⟩ := GlobalTheory.T.integrable_majorant_coordinate_coset_measure D θ hθ m n (fun _ _ => True) 0 μ inferInstance
    (Filter.Eventually.of_forall fun x i j h => (h trivial).elim)
    (fun t _ => by
      have e : (fun x : Mx D m n => x + t) = fun x => t + x := funext fun x => add_comm x t
      rw [e]; exact map_add_left_eq_self μ t)
  refine ⟨N, fun K hK => ?_⟩

  obtain ⟨U, hUo, hU⟩ : ∃ U : Set (Mx D m n), IsOpen U ∧ ∀ γ ∈ ratMx D m n, γ ∈ U ↔ γ = 0 := by
    have h0 : IsOpen ({0} : Set (ratMx D m n)) := @isOpen_discrete (ratMx D m n) _ i5 _
    obtain ⟨U, hUo, hUe⟩ := isOpen_induced_iff.mp h0
    refine ⟨U, hUo, fun γ hγ => ?_⟩
    have := Set.ext_iff.mp hUe ⟨γ, hγ⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at this
    rw [this]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have h0U : (0 : Mx D m n) ∈ U := (hU 0 (zero_mem _)).2 rfl
  have hsub : {p : Mx D m n × Mx D m n | p.1 - p.2 ∈ U} ∈ nhds ((0 : Mx D m n), (0 : Mx D m n)) := by
    have hc : Continuous fun p : Mx D m n × Mx D m n => p.1 - p.2 := continuous_fst.sub continuous_snd
    refine hc.continuousAt.preimage_mem_nhds ?_
    simpa using hUo.mem_nhds h0U
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hsub
  obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds (0 : Mx D m n)
  have hR : {w : Mx D m n | realSize θ w < 1} ∈ nhds (0 : Mx D m n) := by
    refine (isOpen_lt hcont continuous_const).mem_nhds ?_
    show realSize θ (0 : Mx D m n) < 1
    rw [realSize_zero]; exact one_pos
  set W := interior (A ∩ B ∩ C ∩ {w : Mx D m n | realSize θ w < 1}) with hWdef
  have hW0 : (0 : Mx D m n) ∈ W :=
    mem_interior_iff_mem_nhds.2 (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hA hB) hC) hR)
  have hμW : μ W ≠ 0 := (isOpen_interior.measure_pos μ ⟨0, hW0⟩).ne'

  let s : ratMx D m n → Set (Mx D m n) := fun γ => (fun x => -(γ : Mx D m n) + x) ⁻¹' W
  have hs : ∀ γ, MeasurableSet (s γ) := fun γ =>
    (isOpen_interior.preimage (continuous_const.add continuous_id)).measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint s) := by
    intro γ γ' hne
    refine Set.disjoint_left.2 fun x hx hx' => hne ?_
    have hxA : -(γ : Mx D m n) + x ∈ A := (interior_subset hx).1.1.1
    have hxB : -(γ' : Mx D m n) + x ∈ B := (interior_subset hx').1.1.2
    have hmem : (-(γ : Mx D m n) + x, -(γ' : Mx D m n) + x) ∈ {p : Mx D m n × Mx D m n | p.1 - p.2 ∈ U} :=
      hAB ⟨hxA, hxB⟩
    simp only [Set.mem_setOf_eq] at hmem
    have e : -(γ : Mx D m n) + x - (-(γ' : Mx D m n) + x) = (γ' : Mx D m n) - γ := by abel
    rw [e] at hmem
    have := (hU _ (sub_mem γ'.2 γ.2)).1 hmem
    exact Subtype.ext (sub_eq_zero.1 this).symm
  set K' := K + C
  have hK' : IsCompact K' := hK.add hCc
  have hfin : ∫⁻ x, ENNReal.ofReal (maj θ K' N x) ∂μ < ⊤ := (hN K' hK').lintegral_lt_top
  have key : ∀ γ : ratMx D m n, ENNReal.ofReal (maj θ K N γ) * μ W ≤
      2 ^ N * ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ := by
    intro γ
    calc ENNReal.ofReal (maj θ K N γ) * μ W = ∫⁻ _x in s γ, ENNReal.ofReal (maj θ K N γ) ∂μ := by
          rw [setLIntegral_const]
          congr 1
          exact (measure_preimage_add μ (-(γ : Mx D m n)) W).symm
      _ ≤ ∫⁻ x in s γ, 2 ^ N * ENNReal.ofReal (maj θ K' N x) ∂μ := by
          refine setLIntegral_mono' (hs γ) fun x hx => ?_
          have hw := interior_subset hx
          have h1 := maj_le_shift θ K C N (γ : Mx D m n) (-(γ : Mx D m n) + x) hw.1.2 (le_of_lt hw.2)
          rw [add_neg_cancel_left] at h1
          calc ENNReal.ofReal (maj θ K N γ) ≤ ENNReal.ofReal (2 ^ N * maj θ K' N x) :=
                ENNReal.ofReal_le_ofReal h1
            _ = 2 ^ N * ENNReal.ofReal (maj θ K' N x) := by
                rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
      _ = 2 ^ N * ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ :=
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hsum : (∑' γ : ratMx D m n, ENNReal.ofReal (maj θ K N γ)) * μ W ≤
      2 ^ N * ∫⁻ x, ENNReal.ofReal (maj θ K' N x) ∂μ := by
    rw [← ENNReal.tsum_mul_right]
    calc _ ≤ ∑' γ : ratMx D m n, 2 ^ N * ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ :=
          ENNReal.tsum_le_tsum key
      _ = 2 ^ N * ∑' γ : ratMx D m n, ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ := ENNReal.tsum_mul_left
      _ = 2 ^ N * ∫⁻ x in ⋃ γ, s γ, ENNReal.ofReal (maj θ K' N x) ∂μ := by rw [lintegral_iUnion hs hdisj]
      _ ≤ 2 ^ N * ∫⁻ x, ENNReal.ofReal (maj θ K' N x) ∂μ := by
          gcongr; exact Measure.restrict_le_self
  intro htop
  rw [htop, ENNReal.top_mul hμW] at hsum
  exact (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofNat_lt_top) hfin).ne (top_le_iff.1 hsum)

end GlobalTheory.MajSum
