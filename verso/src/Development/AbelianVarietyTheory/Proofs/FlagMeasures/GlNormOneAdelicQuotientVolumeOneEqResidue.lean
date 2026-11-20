import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.NormOneVol

/- English proof (translation)
Take `⟨f, hf⟩` from `exists_measurableEmbedding_real X`. Use `set F : Set X := (C ∩ A) ∩ ⋂ t : T, {x | f x ≤ f (act t x)} with hFdef`. Establish `hF : MeasurableSet F` using `(hC.inter hA).inter (MeasurableSet.iInter fun t => measurableSet_le hf.measurable (hf.measurable.comp (hm t)))`. Establish `huniq : ∀ x ∈ F, ∀ g, act g x ∈ F → g = 1`. Introduce `x hx g hg`.

Establish `hgT : g ∈ T` using `(hT x hx.1.1 g).1 hg.1.1`. Establish `a1 : f x ≤ f (act g x)` using `Set.mem_iInter.1 hx.2 ⟨g, hgT⟩`. Establish `a2 : f (act g x) ≤ f (act g⁻¹ (act g x))` using `Set.mem_iInter.1 hg.2 ⟨g⁻¹, T.inv_mem hgT⟩`. Rewrite `a2` using `[← hmul, inv_mul_cancel, h1]`. Conclude with `hfree x hx.1.1 g (hf.injective (le_antisymm a2 a1))`.

Establish `hdisj : Pairwise (Function.onFun Disjoint fun g : Γ => act g ⁻¹' F)`. Introduce `g h hgh`. Use `Set.disjoint_left.2 fun x hx hx' => hgh ?_` and prove the remaining obligations. Establish `: act (h * g⁻¹) (act g x) ∈ F`. Rewrite using `[← hmul, inv_mul_cancel_right]`.

Conclude with `hx'`. Use `huniq _ hx _ this` as an intermediate fact. Conclude with `(mul_inv_eq_one.1 this).symm`. Establish `hcovT : ∀ x ∈ C ∩ A, ∃ t : T, act t x ∈ F`. Introduce `x hx`.

Take `⟨t, ht⟩` from `Finite.exists_min (fun t : T => f (act t x))`. Use `⟨t, ⟨(hT x hx.1 t).2 t.2, hinv _ _ hx.2⟩, Set.mem_iInter.2 fun s => ?_⟩` and prove the remaining obligations. Use `ht (s * t)` as an intermediate fact. Simplify `this` using `[hmul]`. Use `⟨F, hF, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Take `⟨g, hg⟩` from `hcov x hx`. Take `⟨t, ht⟩` from `hcovT _ ⟨hg, hinv _ _ hx⟩`. Conclude with `⟨t * g, by rwa [hmul]⟩`. Establish `e : C ∩ A = ⋃ t : T, act t ⁻¹' F`.

Use extensionality with `x`. Use `⟨fun hx => Set.mem_iUnion.2 (hcovT x hx), fun hx => ?_⟩` and prove the remaining obligations. Take `⟨t, ht⟩` from `Set.mem_iUnion.1 hx`. Establish `e : x = act (t : Γ)⁻¹ (act t x)` using `by rw [← hmul, inv_mul_cancel, h1]`. Rewrite using `[e]`.

Conclude with `⟨(hT _ ht.1.1 _).2 (T.inv_mem t.2), hinv _ _ ht.1.2⟩`. Rewrite using `[e, measure_iUnion (f := fun t : T => act t ⁻¹' F) (fun s t hst => hdisj (fun h => hst (Subtype.ext h))) (fun t => hm _ hF)]`. Simplify using `only [hμ _ _ hF]`. Use `Fintype.ofFinite T` as an intermediate fact. Simplify using `[tsum_fintype]`.

Introduce `D hD hDc`. Combine the equalities or inequalities in the displayed calculation. Use `measure_mono fun x hx => ?_` and prove the remaining obligations. Take `⟨g, hg⟩` from `hDc x hx.1.2`. Use `Set.mem_iUnion.2 ⟨g⁻¹, ?_, by simpa using hg⟩` and prove the remaining obligations.

Use `show act g⁻¹ (act g⁻¹⁻¹ x) ∈ F`. Rewrite using `[← hmul, mul_inv_cancel, h1]` and apply the resulting hypothesis. Use `_ ≤ ∑' g : Γ, μ (act g⁻¹ ⁻¹' (act g ⁻¹' F ∩ D)) := measure_iUnion_le _`. Use `_ = ∑' g : Γ, μ (act g ⁻¹' F ∩ D) := by`. Use `tsum_congr fun g => hμ _ _ ((hm _ hF).inter hD)` and prove the remaining obligations.

Use `_ = μ (⋃ g : Γ, act g ⁻¹' F ∩ D) := by`. Use `(measure_iUnion (fun g h hgh => ?_) (fun g => (hm _ hF).inter hD)).symm` and prove the remaining obligations. Conclude with `(hdisj hgh).mono Set.inter_subset_left Set.inter_subset_left`. Use `_ ≤ μ D := measure_mono (Set.iUnion_subset fun g => Set.inter_subset_right)`.
-/
theorem exists_domain {Γ X : Type} [Group Γ] [Countable Γ] [MeasurableSpace X] [StandardBorelSpace X]
    (μ : Measure X) (act : Γ → X → X) (h1 : ∀ x, act 1 x = x)
    (hmul : ∀ g h x, act (g * h) x = act g (act h x)) (hm : ∀ g, Measurable (act g))
    (hμ : ∀ g s, MeasurableSet s → μ (act g ⁻¹' s) = μ s)
    (T : Subgroup Γ) [Finite T] (C A : Set X) (hC : MeasurableSet C) (hA : MeasurableSet A)
    (hinv : ∀ g, ∀ x ∈ A, act g x ∈ A) (hcov : ∀ x ∈ A, ∃ g, act g x ∈ C)
    (hT : ∀ x ∈ C, ∀ g, act g x ∈ C ↔ g ∈ T) (hfree : ∀ x ∈ C, ∀ g, act g x = x → g = 1) :
    ∃ F : Set X, MeasurableSet F ∧ (∀ x ∈ A, ∃ g, act g x ∈ F) ∧
      (Nat.card T : ENNReal) * μ F = μ (C ∩ A) ∧
      ∀ D : Set X, MeasurableSet D → (∀ x ∈ A, ∃ g, act g x ∈ D) → μ F ≤ μ D := by
  classical
  obtain ⟨f, hf⟩ := exists_measurableEmbedding_real X
  set F : Set X := (C ∩ A) ∩ ⋂ t : T, {x | f x ≤ f (act t x)} with hFdef
  have hF : MeasurableSet F := (hC.inter hA).inter
    (MeasurableSet.iInter fun t => measurableSet_le hf.measurable (hf.measurable.comp (hm t)))
  have huniq : ∀ x ∈ F, ∀ g, act g x ∈ F → g = 1 := by
    intro x hx g hg
    have hgT : g ∈ T := (hT x hx.1.1 g).1 hg.1.1
    have a1 : f x ≤ f (act g x) := Set.mem_iInter.1 hx.2 ⟨g, hgT⟩
    have a2 : f (act g x) ≤ f (act g⁻¹ (act g x)) := Set.mem_iInter.1 hg.2 ⟨g⁻¹, T.inv_mem hgT⟩
    rw [← hmul, inv_mul_cancel, h1] at a2
    exact hfree x hx.1.1 g (hf.injective (le_antisymm a2 a1))
  have hdisj : Pairwise (Function.onFun Disjoint fun g : Γ => act g ⁻¹' F) := by
    intro g h hgh
    refine Set.disjoint_left.2 fun x hx hx' => hgh ?_
    have : act (h * g⁻¹) (act g x) ∈ F := by
      rw [← hmul, inv_mul_cancel_right]; exact hx'
    have := huniq _ hx _ this
    exact (mul_inv_eq_one.1 this).symm
  have hcovT : ∀ x ∈ C ∩ A, ∃ t : T, act t x ∈ F := by
    intro x hx
    obtain ⟨t, ht⟩ := Finite.exists_min (fun t : T => f (act t x))
    refine ⟨t, ⟨(hT x hx.1 t).2 t.2, hinv _ _ hx.2⟩, Set.mem_iInter.2 fun s => ?_⟩
    have := ht (s * t)
    simpa [hmul] using this
  refine ⟨F, hF, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨g, hg⟩ := hcov x hx
    obtain ⟨t, ht⟩ := hcovT _ ⟨hg, hinv _ _ hx⟩
    exact ⟨t * g, by rwa [hmul]⟩
  · have e : C ∩ A = ⋃ t : T, act t ⁻¹' F := by
      ext x
      refine ⟨fun hx => Set.mem_iUnion.2 (hcovT x hx), fun hx => ?_⟩
      obtain ⟨t, ht⟩ := Set.mem_iUnion.1 hx
      have e : x = act (t : Γ)⁻¹ (act t x) := by rw [← hmul, inv_mul_cancel, h1]
      rw [e]
      exact ⟨(hT _ ht.1.1 _).2 (T.inv_mem t.2), hinv _ _ ht.1.2⟩
    rw [e, measure_iUnion (f := fun t : T => act t ⁻¹' F) (fun s t hst => hdisj (fun h => hst (Subtype.ext h))) (fun t => hm _ hF)]
    simp only [hμ _ _ hF]
    have := Fintype.ofFinite T
    simp [tsum_fintype]
  · intro D hD hDc
    calc μ F ≤ μ (⋃ g : Γ, act g⁻¹ ⁻¹' (act g ⁻¹' F ∩ D)) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨g, hg⟩ := hDc x hx.1.2
          refine Set.mem_iUnion.2 ⟨g⁻¹, ?_, by simpa using hg⟩
          show act g⁻¹ (act g⁻¹⁻¹ x) ∈ F
          rwa [← hmul, mul_inv_cancel, h1]
      _ ≤ ∑' g : Γ, μ (act g⁻¹ ⁻¹' (act g ⁻¹' F ∩ D)) := measure_iUnion_le _
      _ = ∑' g : Γ, μ (act g ⁻¹' F ∩ D) := by
          refine tsum_congr fun g => hμ _ _ ((hm _ hF).inter hD)
      _ = μ (⋃ g : Γ, act g ⁻¹' F ∩ D) := by
          refine (measure_iUnion (fun g h hgh => ?_) (fun g => (hm _ hF).inter hD)).symm
          exact (hdisj hgh).mono Set.inter_subset_left Set.inter_subset_left
      _ ≤ μ D := measure_mono (Set.iUnion_subset fun g => Set.inter_subset_right)

open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone in
open scoped Pointwise Classical in
/- English proof (translation)
Break down `le_or_gt s 0 with hs | hs` into its components or cases. Establish `: fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ s} = ∅`. Use `Set.eq_empty_of_forall_notMem fun x hx => ?_` and prove the remaining obligations. Use `norm_pos_of_mem hx.1` as an intermediate fact. Establish `h2 : mixedEmbedding.norm x ≤ s` using `hx.2`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[this, ENNReal.ofReal_of_nonpos hs]`. Simplify using the standard rewrite rules. Establish `hn : Module.finrank ℚ K ≠ 0` using `Module.finrank_pos.ne' set c : ℝ := s ^ ((Module.finrank ℚ K : ℝ)⁻¹) with hc`. Establish `hc0 : 0 < c` using `Real.rpow_pos_of_pos hs _`.

Establish `hcs : c ^ Module.finrank ℚ K = s` using `Real.rpow_inv_natCast_pow hs.le hn`. Establish `: fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ s} = c • normLeOne K`. Use extensionality with `x`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem₀ hc0.ne', mem_normLeOne, smul_mem_iff_mem (inv_ne_zero hc0.ne'), mixedEmbedding.norm_smul, abs_of_pos (inv_pos.2 hc0), inv_pow, hcs, inv_mul_le_iff₀ hs, mul_one]`. Both sides reduce to the same expression.

Rewrite using `[this, Measure.addHaar_smul, mixedEmbedding.finrank, hcs, abs_of_pos hs, mul_comm]`.
-/
theorem volume_cone_le (K : Type) [Field K] [NumberField K] (s : ℝ) :
    volume (fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ s}) =
      volume (normLeOne K) * ENNReal.ofReal s := by
  rcases le_or_gt s 0 with hs | hs
  · have : fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ s} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x hx => ?_
      have := norm_pos_of_mem hx.1
      have h2 : mixedEmbedding.norm x ≤ s := hx.2
      linarith
    rw [this, ENNReal.ofReal_of_nonpos hs]; simp
  · have hn : Module.finrank ℚ K ≠ 0 := Module.finrank_pos.ne'
    set c : ℝ := s ^ ((Module.finrank ℚ K : ℝ)⁻¹) with hc
    have hc0 : 0 < c := Real.rpow_pos_of_pos hs _
    have hcs : c ^ Module.finrank ℚ K = s := Real.rpow_inv_natCast_pow hs.le hn
    have : fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ s} = c • normLeOne K := by
      ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc0.ne', mem_normLeOne,
        smul_mem_iff_mem (inv_ne_zero hc0.ne'), mixedEmbedding.norm_smul, abs_of_pos (inv_pos.2 hc0),
        inv_pow, hcs, inv_mul_le_iff₀ hs, mul_one]
      rfl
    rw [this, Measure.addHaar_smul, mixedEmbedding.finrank, hcs, abs_of_pos hs, mul_comm]

open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone in
open scoped Classical in
/- English proof (translation)
Establish `hN : Measurable (fun x : mixedSpace K => mixedEmbedding.norm x)` using `(mixedEmbedding.continuous_norm K).measurable`. Establish `hV : volume (normLeOne K) ≠ ⊤`. Rewrite using `[volume_normLeOne]`. Use `finiteness`. Use `set e := Real.exp 1 with he`.

Establish `he1 : 1 < e` using `Real.one_lt_exp_iff.2 one_pos`. Use `set S := fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ e} with hS`. Establish `hSm : MeasurableSet S` using `(measurableSet_fundamentalCone K).inter (measurableSet_le hN measurable_const)`. Establish `: IsFiniteMeasure (volume.restrict S)` using `⟨by`. Rewrite using `[Measure.restrict_apply_univ, hS, volume_cone_le]`.

Conclude with `ENNReal.mul_lt_top hV.lt_top ENNReal.ofReal_lt_top⟩`. Establish `hmap : (volume.restrict S).map (fun x : mixedSpace K => mixedEmbedding.norm x) = volume (normLeOne K) • volume.restrict (Set.Ioc 0 e)`. Use `Measure.ext_of_Iic _ _ fun t => ?_` and prove the remaining obligations. Rewrite using `[Measure.map_apply hN measurableSet_Iic, Measure.restrict_apply' hSm, Measure.smul_apply, Measure.restrict_apply measurableSet_Iic, smul_eq_mul]`. Establish `e1 : (fun x : mixedSpace K => mixedEmbedding.norm x) ⁻¹' Set.Iic t ∩ S = fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ min t e}`.

Use extensionality with `x`. Simplify using `[hS]`. The claim follows by propositional logic. Establish `e2 : Set.Iic t ∩ Set.Ioc 0 e = Set.Ioc 0 (min t e)`. Use extensionality with `x`.

Simplify using the standard rewrite rules. The claim follows by propositional logic. Rewrite using `[e1, e2, volume_cone_le, Real.volume_Ioc, sub_zero]`. Establish `e3 : fundamentalCone K ∩ {x | 1 ≤ mixedEmbedding.norm x ∧ mixedEmbedding.norm x < e} = (fun x : mixedSpace K => mixedEmbedding.norm x) ⁻¹' Set.Ico 1 e ∩ S`. Use extensionality with `x`.

Simplify using `only [hS, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ico, Set.mem_setOf_eq]`. Conclude with `⟨fun h => ⟨h.2, h.1, h.2.2.le⟩, fun h => ⟨h.2.1, h.1⟩⟩`. Rewrite using `[e3, ← Measure.restrict_restrict (hN measurableSet_Ico), ← setLIntegral_map (f := fun t : ℝ => ENNReal.ofReal t⁻¹) measurableSet_Ico (by fun_prop) hN, hmap, Measure.restrict_smul, lintegral_smul_measure, Measure.restrict_restrict measurableSet_Ico]`. Establish `e4 : Set.Ico 1 e ∩ Set.Ioc 0 e = Set.Ico 1 e` using `Set.inter_eq_left.2 fun x hx => ⟨by linarith [hx.1], hx.2.le⟩`. Establish `hint : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 e` using `intervalIntegral.intervalIntegrable_inv (f := id) (fun x hx => by`.

Rewrite using `[Set.uIcc_of_le he1.le] at hx; exact (by linarith [hx.1] : 0 < x).ne') continuousOn_id`. Rewrite using `[e4, Measure.restrict_congr_set Ico_ae_eq_Ioc, ← ofReal_integral_eq_lintegral_ofReal hint.1, ← intervalIntegral.integral_of_le he1.le, integral_inv_of_pos one_pos (by linarith), div_one, he, Real.log_exp]`. Simplify using the standard rewrite rules. Use `filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx`. Conclude with `inv_nonneg.2 (by linarith [hx.1])`.
-/
theorem lintegral_cone_slab (K : Type) [Field K] [NumberField K] :
    ∫⁻ x in fundamentalCone K ∩ {x | 1 ≤ mixedEmbedding.norm x ∧ mixedEmbedding.norm x < Real.exp 1},
      ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ = volume (normLeOne K) := by
  have hN : Measurable (fun x : mixedSpace K => mixedEmbedding.norm x) :=
    (mixedEmbedding.continuous_norm K).measurable
  have hV : volume (normLeOne K) ≠ ⊤ := by
    rw [volume_normLeOne]; finiteness
  set e := Real.exp 1 with he
  have he1 : 1 < e := Real.one_lt_exp_iff.2 one_pos
  set S := fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ e} with hS
  have hSm : MeasurableSet S := (measurableSet_fundamentalCone K).inter (measurableSet_le hN measurable_const)
  have : IsFiniteMeasure (volume.restrict S) := ⟨by
    rw [Measure.restrict_apply_univ, hS, volume_cone_le]
    exact ENNReal.mul_lt_top hV.lt_top ENNReal.ofReal_lt_top⟩
  have hmap : (volume.restrict S).map (fun x : mixedSpace K => mixedEmbedding.norm x) =
      volume (normLeOne K) • volume.restrict (Set.Ioc 0 e) := by
    refine Measure.ext_of_Iic _ _ fun t => ?_
    rw [Measure.map_apply hN measurableSet_Iic, Measure.restrict_apply' hSm, Measure.smul_apply,
      Measure.restrict_apply measurableSet_Iic, smul_eq_mul]
    have e1 : (fun x : mixedSpace K => mixedEmbedding.norm x) ⁻¹' Set.Iic t ∩ S =
        fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ min t e} := by
      ext x; simp [hS]; tauto
    have e2 : Set.Iic t ∩ Set.Ioc 0 e = Set.Ioc 0 (min t e) := by
      ext x; simp; tauto
    rw [e1, e2, volume_cone_le, Real.volume_Ioc, sub_zero]
  have e3 : fundamentalCone K ∩ {x | 1 ≤ mixedEmbedding.norm x ∧ mixedEmbedding.norm x < e} =
      (fun x : mixedSpace K => mixedEmbedding.norm x) ⁻¹' Set.Ico 1 e ∩ S := by
    ext x
    simp only [hS, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ico, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨h.2, h.1, h.2.2.le⟩, fun h => ⟨h.2.1, h.1⟩⟩
  rw [e3, ← Measure.restrict_restrict (hN measurableSet_Ico),
    ← setLIntegral_map (f := fun t : ℝ => ENNReal.ofReal t⁻¹) measurableSet_Ico (by fun_prop) hN, hmap,
    Measure.restrict_smul, lintegral_smul_measure, Measure.restrict_restrict measurableSet_Ico]
  have e4 : Set.Ico 1 e ∩ Set.Ioc 0 e = Set.Ico 1 e :=
    Set.inter_eq_left.2 fun x hx => ⟨by linarith [hx.1], hx.2.le⟩
  have hint : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 e :=
    intervalIntegral.intervalIntegrable_inv (f := id) (fun x hx => by
      rw [Set.uIcc_of_le he1.le] at hx; exact (by linarith [hx.1] : 0 < x).ne') continuousOn_id
  rw [e4, Measure.restrict_congr_set Ico_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal hint.1, ← intervalIntegral.integral_of_le he1.le,
    integral_inv_of_pos one_pos (by linarith), div_one, he, Real.log_exp]
  · simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact inv_nonneg.2 (by linarith [hx.1])

section Lattices
variable {E : Type} [Field E] [NumberField E]

open scoped nonZeroDivisors

/- English proof (translation)
Use extensionality with `i`. Rewrite using `[Subsingleton.elim i 0]`. Simplify using `[Matrix.mulVec, dotProduct]`.
-/
theorem mulVec_one (γ : Matrix (Fin 1) (Fin 1) E) (y : Fin 1 → E) : γ *ᵥ y = γ 0 0 • y := by
  ext i
  rw [Subsingleton.elim i 0]
  simp [Matrix.mulVec, dotProduct]

/- English proof (translation)
Use `γ.det_ne_zero` as an intermediate fact. Simplify `this` using `[Matrix.det_unique]`.
-/
theorem gl_one_ne_zero (γ : GL (Fin 1) E) : (γ : Matrix (Fin 1) (Fin 1) E) 0 0 ≠ 0 := by
  have := γ.det_ne_zero
  simpa [Matrix.det_unique] using this

/- English proof (translation)
Assemble the required witnesses or components as `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of fun _ _ => c) (by simpa [Matrix.det_unique] using hc), rfl⟩`.
-/
theorem exists_gl_one {c : E} (hc : c ≠ 0) : ∃ γ : GL (Fin 1) E, (γ : Matrix (Fin 1) (Fin 1) E) 0 0 = c :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of fun _ _ => c) (by simpa [Matrix.det_unique] using hc), rfl⟩

/- English proof (translation)
Use extensionality with `i`. Rewrite using `[Subsingleton.elim i 0]`.
-/
theorem eq_const (y : Fin 1 → E) : y = fun _ => y 0 := by
  ext i; rw [Subsingleton.elim i 0]

/- English proof (translation)
Set `I : FractionalIdeal (𝓞 E)⁰ E` to `⟨Λ.map (LinearMap.proj 0), FractionalIdeal.isFractional_of_fg (h.fg.map _)⟩`. Establish `hI : ∀ y, y ∈ Λ ↔ y 0 ∈ I`. Introduce `y`. Use `⟨fun hy => ⟨y, hy, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨z, hz, hzy⟩`.

Establish `: y = z` using `by rw [eq_const y, eq_const z]; ext; exact hzy.symm`. Rewrite using `[this]` and apply the resulting hypothesis. Establish `h0 : I ≠ 0`. Introduce `h0`. Establish `h1 : (Λ : Set (Fin 1 → E)) ⊆ (⊥ : Submodule E (Fin 1 → E))`.

Introduce `y hy`. Use `(hI y).1 hy` as an intermediate fact. Rewrite `this` using `[h0, FractionalIdeal.mem_zero_iff]`. Rewrite using `[eq_const y, this]`. Conclude with `Submodule.zero_mem _`.

Establish `h2` using `Submodule.span_le.2 h1`. Rewrite `h2` using `[h.span_eq_top]`. Conclude with `absurd (top_le_iff.1 h2) bot_ne_top`. Conclude with `⟨Units.mk0 I h0, hI⟩`.
-/
theorem exists_ideal (Λ : Submodule (𝓞 E) (Fin 1 → E)) (h : Submodule.IsLattice E Λ) :
    ∃ I : (FractionalIdeal (𝓞 E)⁰ E)ˣ, ∀ y, y ∈ Λ ↔ y 0 ∈ (I : FractionalIdeal (𝓞 E)⁰ E) := by
  let I : FractionalIdeal (𝓞 E)⁰ E :=
    ⟨Λ.map (LinearMap.proj 0), FractionalIdeal.isFractional_of_fg (h.fg.map _)⟩
  have hI : ∀ y, y ∈ Λ ↔ y 0 ∈ I := by
    intro y
    refine ⟨fun hy => ⟨y, hy, rfl⟩, ?_⟩
    rintro ⟨z, hz, hzy⟩
    have : y = z := by rw [eq_const y, eq_const z]; ext; exact hzy.symm
    rwa [this]
  have h0 : I ≠ 0 := by
    intro h0
    have h1 : (Λ : Set (Fin 1 → E)) ⊆ (⊥ : Submodule E (Fin 1 → E)) := by
      intro y hy
      have := (hI y).1 hy
      rw [h0, FractionalIdeal.mem_zero_iff] at this
      rw [eq_const y, this]; exact Submodule.zero_mem _
    have h2 := Submodule.span_le.2 h1
    rw [h.span_eq_top] at h2
    exact absurd (top_le_iff.1 h2) bot_ne_top
  exact ⟨Units.mk0 I h0, hI⟩

/- English proof (translation)
Set `e : E →ₗ[𝓞 E] (Fin 1 → E)` to `LinearMap.pi fun _ => LinearMap.id`. Establish `hm : ∀ y, y ∈ ((I : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E).map e ↔ y 0 ∈ (I : FractionalIdeal (𝓞 E)⁰ E)`. Introduce `y`. Use `⟨?_, fun hy => ⟨y 0, hy, (eq_const y).symm⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨z, hz, rfl⟩`.

Conclude with `hz`. Use `⟨_, ⟨(FractionalIdeal.fg_unit I).map e, ?_⟩, hm⟩` and prove the remaining obligations. Take `⟨x, hx0, hx⟩` from `FractionalIdeal.exists_ne_zero_mem_isInteger I.ne_zero`. Establish `hx0' : algebraMap (𝓞 E) E x ≠ 0` using `by simpa using hx0`. Rewrite using `[eq_top_iff]`.

Introduce `y _`. Establish `: y = (y 0 / algebraMap (𝓞 E) E x) • fun _ : Fin 1 => algebraMap (𝓞 E) E x`. Use extensionality with `i`. Rewrite using `[Subsingleton.elim i 0]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ((hm _).2 hx))`.
-/
theorem exists_lattice (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    ∃ Λ : Submodule (𝓞 E) (Fin 1 → E), Submodule.IsLattice E Λ ∧
      ∀ y, y ∈ Λ ↔ y 0 ∈ (I : FractionalIdeal (𝓞 E)⁰ E) := by
  let e : E →ₗ[𝓞 E] (Fin 1 → E) := LinearMap.pi fun _ => LinearMap.id
  have hm : ∀ y, y ∈ ((I : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E).map e ↔
      y 0 ∈ (I : FractionalIdeal (𝓞 E)⁰ E) := by
    intro y
    refine ⟨?_, fun hy => ⟨y 0, hy, (eq_const y).symm⟩⟩
    rintro ⟨z, hz, rfl⟩
    exact hz
  refine ⟨_, ⟨(FractionalIdeal.fg_unit I).map e, ?_⟩, hm⟩
  obtain ⟨x, hx0, hx⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger I.ne_zero
  have hx0' : algebraMap (𝓞 E) E x ≠ 0 := by simpa using hx0
  rw [eq_top_iff]
  intro y _
  have : y = (y 0 / algebraMap (𝓞 E) E x) • fun _ : Fin 1 => algebraMap (𝓞 E) E x := by
    ext i; rw [Subsingleton.elim i 0]; simp only [Pi.smul_apply, smul_eq_mul]; field_simp
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ((hm _).2 hx))

/- English proof (translation)
Rewrite using `[← Units.val_inj, Units.val_mul, coe_toPrincipalIdeal, mul_comm]`. Prove the components needed by the constructor for the conclusion. Introduce `h t`. Rewrite using `[← h, FractionalIdeal.mem_singleton_mul]`. Use `⟨?_, fun ht => ⟨t, ht, rfl⟩⟩` and prove the remaining obligations.

Introduce and unpack `⟨y, hy, e⟩`. Rewrite using `[mul_left_cancel₀ c.ne_zero e]` and apply the resulting hypothesis. Introduce `h`. Use extensionality with `t`. Rewrite using `[FractionalIdeal.mem_singleton_mul]`.

Use `⟨?_, fun ht => ⟨(c : E)⁻¹ * t, (h _).1 (by rwa [mul_inv_cancel_left₀ c.ne_zero]), by` and prove the remaining obligations. Rewrite using `[mul_inv_cancel_left₀ c.ne_zero]⟩⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `(h y).2 hy`.
-/
theorem mul_principal_eq_iff (I J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (c : Eˣ) :
    I * toPrincipalIdeal (𝓞 E) E c = J ↔
      ∀ t : E, (c : E) * t ∈ (J : FractionalIdeal (𝓞 E)⁰ E) ↔ t ∈ (I : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [← Units.val_inj, Units.val_mul, coe_toPrincipalIdeal, mul_comm]
  constructor
  · intro h t
    rw [← h, FractionalIdeal.mem_singleton_mul]
    refine ⟨?_, fun ht => ⟨t, ht, rfl⟩⟩
    rintro ⟨y, hy, e⟩
    rwa [mul_left_cancel₀ c.ne_zero e]
  · intro h
    ext t
    rw [FractionalIdeal.mem_singleton_mul]
    refine ⟨?_, fun ht => ⟨(c : E)⁻¹ * t, (h _).1 (by rwa [mul_inv_cancel_left₀ c.ne_zero]), by
      rw [mul_inv_cancel_left₀ c.ne_zero]⟩⟩
    rintro ⟨y, hy, rfl⟩
    exact (h y).2 hy

/- English proof (translation)
Use `choose ψ hψ using fun Λ : {Λ : Submodule (𝓞 E) (Fin 1 → E) // Submodule.IsLattice E Λ} => exists_ideal Λ.1 Λ.2`. Set `q` to `QuotientGroup.mk' (toPrincipalIdeal (𝓞 E) E).range`. Establish `key : ∀ Λ Λ', (∃ γ : GL (Fin 1) E, ∀ y, (γ : Matrix (Fin 1) (Fin 1) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1) ↔ q (ψ Λ) = q (ψ Λ')`. Introduce `Λ Λ'`. Rewrite using `[QuotientGroup.mk'_eq_mk']`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ, hγ⟩`. Use `⟨_, ⟨Units.mk0 _ (gl_one_ne_zero γ), rfl⟩, (mul_principal_eq_iff _ _ _).2 fun t => ?_⟩` and prove the remaining obligations. Use `hγ (fun _ => t)` as an intermediate fact. Rewrite `this` using `[mulVec_one, hψ, hψ]`.

Conclude with `this`. Introduce and unpack `⟨_, ⟨c, rfl⟩, h⟩`. Take `⟨γ, hγ⟩` from `exists_gl_one c.ne_zero`. Use `⟨γ, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[mulVec_one, hψ, hψ, hγ]`.

Conclude with `(mul_principal_eq_iff _ _ _).1 h _`. Use `⟨(Equiv.ofBijective (Quot.lift (fun Λ => q (ψ Λ)) fun a b h => (key a b).1 h) ⟨?_, ?_⟩).trans (ClassGroup.equiv E).symm.toEquiv⟩` and prove the remaining obligations. Introduce and unpack `⟨a⟩ ⟨b⟩ h`. Conclude with `Quot.sound ((key a b).2 h)`. Introduce `x`.

Take `⟨I, rfl⟩` from `QuotientGroup.mk'_surjective _ x`. Take `⟨Λ, hΛ, h⟩` from `exists_lattice I`. Use `⟨Quot.mk _ ⟨Λ, hΛ⟩, ?_⟩` and prove the remaining obligations. Use `show q (ψ ⟨Λ, hΛ⟩) = q I`. Use `congr 1`.

Use extensionality with `t`. Conclude with `(hψ ⟨Λ, hΛ⟩ fun _ => t).symm.trans (h fun _ => t)`.
-/
theorem nonempty_equiv_classGroup :
    Nonempty (Quot (fun Λ Λ' : {Λ : Submodule (𝓞 E) (Fin 1 → E) // Submodule.IsLattice E Λ} =>
      ∃ γ : GL (Fin 1) E, ∀ y, (γ : Matrix (Fin 1) (Fin 1) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1) ≃ ClassGroup (𝓞 E)) := by
  choose ψ hψ using fun Λ : {Λ : Submodule (𝓞 E) (Fin 1 → E) // Submodule.IsLattice E Λ} =>
    exists_ideal Λ.1 Λ.2
  let q := QuotientGroup.mk' (toPrincipalIdeal (𝓞 E) E).range
  have key : ∀ Λ Λ', (∃ γ : GL (Fin 1) E, ∀ y, (γ : Matrix (Fin 1) (Fin 1) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1) ↔
      q (ψ Λ) = q (ψ Λ') := by
    intro Λ Λ'
    rw [QuotientGroup.mk'_eq_mk']
    constructor
    · rintro ⟨γ, hγ⟩
      refine ⟨_, ⟨Units.mk0 _ (gl_one_ne_zero γ), rfl⟩, (mul_principal_eq_iff _ _ _).2 fun t => ?_⟩
      have := hγ (fun _ => t)
      rw [mulVec_one, hψ, hψ] at this
      exact this
    · rintro ⟨_, ⟨c, rfl⟩, h⟩
      obtain ⟨γ, hγ⟩ := exists_gl_one c.ne_zero
      refine ⟨γ, fun y => ?_⟩
      rw [mulVec_one, hψ, hψ, hγ]
      exact (mul_principal_eq_iff _ _ _).1 h _
  refine ⟨(Equiv.ofBijective (Quot.lift (fun Λ => q (ψ Λ)) fun a b h => (key a b).1 h) ⟨?_, ?_⟩).trans
    (ClassGroup.equiv E).symm.toEquiv⟩
  · rintro ⟨a⟩ ⟨b⟩ h
    exact Quot.sound ((key a b).2 h)
  · intro x
    obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective _ x
    obtain ⟨Λ, hΛ, h⟩ := exists_lattice I
    refine ⟨Quot.mk _ ⟨Λ, hΛ⟩, ?_⟩
    show q (ψ ⟨Λ, hΛ⟩) = q I
    congr 1
    ext t
    exact (hψ ⟨Λ, hΛ⟩ fun _ => t).symm.trans (h fun _ => t)

/- English proof (translation)
Take `⟨I, hI⟩` from `exists_ideal Λ h`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ, hγ, hx⟩`. Establish `h1 : I * toPrincipalIdeal (𝓞 E) E (Units.mk0 _ (gl_one_ne_zero γ)) = I` using `(mul_principal_eq_iff _ _ _).2 fun t => by`. Use `hγ (fun _ => t)` as an intermediate fact.

Rewrite `this` using `[mulVec_one, hI, hI]`. Conclude with `this`. Rewrite `h1` using `[mul_eq_left, toPrincipalIdeal_eq_iff, Units.val_one, ← FractionalIdeal.spanSingleton_one, FractionalIdeal.spanSingleton_eq_spanSingleton]`. Take `⟨u, hu⟩` from `h1`. Use `⟨u⁻¹, fun w a b => ?_⟩` and prove the remaining obligations.

Rewrite using `[hx, Subsingleton.elim a 0, Subsingleton.elim b 0]`. Use `congr 1`. Use `congrArg (fun t => u⁻¹ • t) hu` as an intermediate fact. Simplify using `only [inv_smul_smul, Units.val_mk0] at this`. Rewrite using `[this, Units.smul_def, Algebra.smul_def, mul_one]`.

Introduce and unpack `⟨u, hu⟩`. Take `⟨γ, hγ⟩` from `exists_gl_one (c := ((u : 𝓞 E) : E)) (by simp)`. Use `⟨γ, fun y => ?_, fun w a b => ?_⟩` and prove the remaining obligations. Rewrite using `[mulVec_one, hγ]`. Establish `: ((u : 𝓞 E) : E) • y = u • y`.

Rewrite using `[Units.smul_def, ← algebraMap_smul E (u : 𝓞 E) y]`. Rewrite using `[this]`. Conclude with `Λ.smul_mem_iff' u`. Rewrite using `[hu, Subsingleton.elim a 0, Subsingleton.elim b 0, hγ]`.
-/
theorem mem_autGL_iff (Λ : Submodule (𝓞 E) (Fin 1 → E)) (h : Submodule.IsLattice E Λ) (x : MatInf E 1) :
    x ∈ autGL E 1 Λ ↔ ∃ u : (𝓞 E)ˣ, ∀ w a b, x w a b = w.embedding ((u : 𝓞 E) : E) := by
  obtain ⟨I, hI⟩ := exists_ideal Λ h
  constructor
  · rintro ⟨γ, hγ, hx⟩
    have h1 : I * toPrincipalIdeal (𝓞 E) E (Units.mk0 _ (gl_one_ne_zero γ)) = I :=
      (mul_principal_eq_iff _ _ _).2 fun t => by
        have := hγ (fun _ => t)
        rw [mulVec_one, hI, hI] at this
        exact this
    rw [mul_eq_left, toPrincipalIdeal_eq_iff, Units.val_one, ← FractionalIdeal.spanSingleton_one,
      FractionalIdeal.spanSingleton_eq_spanSingleton] at h1
    obtain ⟨u, hu⟩ := h1
    refine ⟨u⁻¹, fun w a b => ?_⟩
    rw [hx, Subsingleton.elim a 0, Subsingleton.elim b 0]
    congr 1
    have := congrArg (fun t => u⁻¹ • t) hu
    simp only [inv_smul_smul, Units.val_mk0] at this
    rw [this, Units.smul_def, Algebra.smul_def, mul_one]
  · rintro ⟨u, hu⟩
    obtain ⟨γ, hγ⟩ := exists_gl_one (c := ((u : 𝓞 E) : E)) (by simp)
    refine ⟨γ, fun y => ?_, fun w a b => ?_⟩
    · rw [mulVec_one, hγ]
      have : ((u : 𝓞 E) : E) • y = u • y := by
        rw [Units.smul_def, ← algebraMap_smul E (u : 𝓞 E) y]
      rw [this]
      exact Λ.smul_mem_iff' u
    · rw [hu, Subsingleton.elim a 0, Subsingleton.elim b 0, hγ]

end Lattices

section Transport
variable (E : Type) [Field E] [NumberField E]

open NumberField.mixedEmbedding NumberField.InfinitePlace

noncomputable def act (u : (𝓞 E)ˣ) (x : InfinitePlace E → Fin 1 → Fin 1 → ℂ) :
    InfinitePlace E → Fin 1 → Fin 1 → ℂ := fun w => w.embedding ((u : 𝓞 E) : E) • x w

noncomputable def toMixed (x : InfinitePlace E → Fin 1 → Fin 1 → ℂ) : mixedSpace E :=
  (0, fun w => x w.1 0 0)

variable {E}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun w => not_isReal_iff_isComplex.2 (hE.isComplex w.1) w.2⟩`.
-/
theorem isEmpty_real (hE : IsTotallyComplex E) : IsEmpty {w : InfinitePlace E // IsReal w} :=
  ⟨fun w => not_isReal_iff_isComplex.2 (hE.isComplex w.1) w.2⟩

/- English proof (translation)
Use `isEmpty_real hE` as an intermediate fact. Use `Prod.ext (Subsingleton.elim _ _) ?_` and prove the remaining obligations. Use extensionality with `w`. Simplify using `[toMixed, act]`.
-/
theorem toMixed_act (hE : IsTotallyComplex E) (u : (𝓞 E)ˣ) (x : InfinitePlace E → Fin 1 → Fin 1 → ℂ) :
    toMixed E (act E u x) = u • toMixed E x := by
  have := isEmpty_real hE
  refine Prod.ext (Subsingleton.elim _ _) ?_
  ext w
  simp [toMixed, act]

/- English proof (translation)
Rewrite using `[mixedEmbedding.norm_apply]`. Use `show _ = ∏ w, ‖(Matrix.of (x w)).det‖ ^ 2`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[normAtPlace_apply_of_isComplex (hE.isComplex w), mult_isComplex ⟨w, hE.isComplex w⟩]`. Simplify using `[toMixed, Matrix.det_unique]`.
-/
theorem norm_toMixed (hE : IsTotallyComplex E) (x : InfinitePlace E → Fin 1 → Fin 1 → ℂ) :
    mixedEmbedding.norm (toMixed E x) = detNorm E 1 x := by
  rw [mixedEmbedding.norm_apply]
  show _ = ∏ w, ‖(Matrix.of (x w)).det‖ ^ 2
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [normAtPlace_apply_of_isComplex (hE.isComplex w), mult_isComplex ⟨w, hE.isComplex w⟩]
  simp [toMixed, Matrix.det_unique]

open scoped Classical in
/- English proof (translation)
Use `isEmpty_real hE` as an intermediate fact. Establish `h1 : MeasurePreserving (fun (x : InfinitePlace E → Fin 1 → Fin 1 → ℂ) (w : InfinitePlace E) => x w 0 0) volume volume` using `volume_preserving_pi fun w => (volume_preserving_funUnique (Fin 1) ℂ).comp (volume_preserving_funUnique (Fin 1) (Fin 1 → ℂ))`. Establish `h2` using `(volume_measurePreserving_piCongrLeft (fun _ : InfinitePlace E => ℂ) (Equiv.subtypeUnivEquiv (p := IsComplex) hE.isComplex)).symm`. Establish `h3 : MeasurePreserving (fun z : {w : InfinitePlace E // IsComplex w} → ℂ => ((0, z) : mixedSpace E)) volume volume`. Use `⟨measurable_prodMk_left, ?_⟩` and prove the remaining obligations.

Rewrite using `[Measure.volume_eq_prod, volume_pi (α := fun _ : {w : InfinitePlace E // IsReal w} => ℝ), Measure.pi_of_empty _ 0, Measure.dirac_prod]`. Conclude with `h3.comp (h2.comp h1)`.
-/
theorem measurePreserving_toMixed (hE : IsTotallyComplex E) : MeasurePreserving (toMixed E) volume volume := by
  have := isEmpty_real hE
  have h1 : MeasurePreserving (fun (x : InfinitePlace E → Fin 1 → Fin 1 → ℂ) (w : InfinitePlace E) => x w 0 0)
      volume volume :=
    volume_preserving_pi fun w =>
      (volume_preserving_funUnique (Fin 1) ℂ).comp (volume_preserving_funUnique (Fin 1) (Fin 1 → ℂ))
  have h2 := (volume_measurePreserving_piCongrLeft (fun _ : InfinitePlace E => ℂ)
    (Equiv.subtypeUnivEquiv (p := IsComplex) hE.isComplex)).symm
  have h3 : MeasurePreserving (fun z : {w : InfinitePlace E // IsComplex w} → ℂ => ((0, z) : mixedSpace E))
      volume volume := by
    refine ⟨measurable_prodMk_left, ?_⟩
    rw [Measure.volume_eq_prod, volume_pi (α := fun _ : {w : InfinitePlace E // IsReal w} => ℝ),
      Measure.pi_of_empty _ 0, Measure.dirac_prod]
  exact h3.comp (h2.comp h1)

/- English proof (translation)
Unfold `act`. Use `fun_prop`.
-/
theorem measurable_act (u : (𝓞 E)ˣ) : Measurable (act E u) := by
  unfold act; fun_prop

/- English proof (translation)
Set `L : (InfinitePlace E → Fin 1 → Fin 1 → ℂ) →ₗ[ℂ] (InfinitePlace E → Fin 1 → Fin 1 → ℂ)` to `LinearMap.pi fun w => (w.embedding ((u : 𝓞 E) : E) • LinearMap.id).comp (LinearMap.proj w)`. Establish `hd : LinearMap.det (L.restrictScalars ℝ) = 1`. Rewrite using `[LinearMap.det_restrictScalars, Algebra.norm_complex_apply, LinearMap.det_pi, map_prod]`. Use `prod_eq_abs_norm ((u : 𝓞 E) : E)` as an intermediate fact. Rewrite `this` using `[NumberField.Units.norm]`.

Move the coercions through the operations in `at this`. Rewrite using `[← this]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[mult_isComplex ⟨w, hE.isComplex w⟩, LinearMap.det_smul, LinearMap.det_id, Complex.normSq_eq_norm_sq, ← norm_embedding_eq]`. Simplify using `[Module.finrank_pi_fintype]`.

Use `⟨measurable_act u, ?_⟩` and prove the remaining obligations. Establish `: (volume : Measure (Fin 1 → ℂ)).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`. Establish `: (volume : Measure (Fin 1 → Fin 1 → ℂ)).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`. Establish `: (volume : Measure (InfinitePlace E → Fin 1 → Fin 1 → ℂ)).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`. Use `Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (InfinitePlace E → Fin 1 → Fin 1 → ℂ)) (f := L.restrictScalars ℝ) (by rw [hd]; norm_num)` as an intermediate fact.

Rewrite `this` using `[hd, inv_one, abs_one, ENNReal.ofReal_one, one_smul]`. Conclude with `this`.
-/
theorem measurePreserving_act (hE : IsTotallyComplex E) (u : (𝓞 E)ˣ) :
    MeasurePreserving (act E u) volume volume := by
  classical
  let L : (InfinitePlace E → Fin 1 → Fin 1 → ℂ) →ₗ[ℂ] (InfinitePlace E → Fin 1 → Fin 1 → ℂ) :=
    LinearMap.pi fun w => (w.embedding ((u : 𝓞 E) : E) • LinearMap.id).comp (LinearMap.proj w)
  have hd : LinearMap.det (L.restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, LinearMap.det_pi, map_prod]
    have := prod_eq_abs_norm ((u : 𝓞 E) : E)
    rw [NumberField.Units.norm] at this
    push_cast at this
    rw [← this]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isComplex ⟨w, hE.isComplex w⟩, LinearMap.det_smul, LinearMap.det_id, Complex.normSq_eq_norm_sq,
      ← norm_embedding_eq]
    simp [Module.finrank_pi_fintype]
  refine ⟨measurable_act u, ?_⟩
  have : (volume : Measure (Fin 1 → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin 1 → Fin 1 → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (InfinitePlace E → Fin 1 → Fin 1 → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (InfinitePlace E → Fin 1 → Fin 1 → ℂ)) (f := L.restrictScalars ℝ) (by rw [hd]; norm_num)
  rw [hd, inv_one, abs_one, ENNReal.ofReal_one, one_smul] at this
  exact this

open scoped Classical in
/- English proof (translation)
Establish `hN : Measurable (fun x : mixedSpace E => mixedEmbedding.norm x)` using `(mixedEmbedding.continuous_norm E).measurable`. Establish `hφ` using `measurePreserving_toMixed hE`. Establish `hdet : Measurable (fun x : InfinitePlace E → Fin 1 → Fin 1 → ℂ => detNorm E 1 x)`. Simplify using `only [← norm_toMixed hE]`. Conclude with `hN.comp hφ.measurable`.

Establish `hdact : ∀ u x, detNorm E 1 (act E u x) = detNorm E 1 x` using `fun u x => by`. Rewrite using `[← norm_toMixed hE, ← norm_toMixed hE, toMixed_act hE, norm_unit_smul]`. Set `μ : Measure (InfinitePlace E → Fin 1 → Fin 1 → ℂ)` to `volume.withDensity fun x => ENNReal.ofReal ((detNorm E 1 x)⁻¹ ^ 1)`. Set `A : Set (InfinitePlace E → Fin 1 → Fin 1 → ℂ)` to `{x | 1 ≤ detNorm E 1 x ∧ detNorm E 1 x < Real.exp 1}`. Establish `hA : MeasurableSet A` using `hdet (measurableSet_Ico (a := 1) (b := Real.exp 1))`.

Establish `hC : MeasurableSet (toMixed E ⁻¹' fundamentalCone E)` using `hφ.measurable (measurableSet_fundamentalCone E)`. Establish `: StandardBorelSpace (Fin 1 → ℂ)` using `StandardBorelSpace.pi_countable`. Establish `: StandardBorelSpace (Fin 1 → Fin 1 → ℂ)` using `StandardBorelSpace.pi_countable`. Establish `: StandardBorelSpace (InfinitePlace E → Fin 1 → Fin 1 → ℂ)` using `StandardBorelSpace.pi_countable`. Establish `: Countable (𝓞 E)` using `Countable.of_equiv _ (RingOfIntegers.basis E).equivFun.symm.toEquiv`.

Establish `: Countable (𝓞 E)ˣ` using `Units.val_injective.countable`. Take `⟨F, hF, hcov, hvol, hmin⟩` from `exists_domain μ (act E) (fun x => by ext; simp [act]) (fun g h x => by ext; simp [act, mul_assoc]) measurable_act (fun g s hs => by`. Rewrite using `[withDensity_apply _ hs, withDensity_apply _ (measurable_act g hs), ← (measurePreserving_act hE g).setLIntegral_comp_preimage hs (by fun_prop)]`. Simplify using `only [hdact])`. Use the proof step `(Units.torsion E) (toMixed E ⁻¹' fundamentalCone E) A hC hA`.

Use the proof step `(fun g x hx => by simpa only [A, Set.mem_setOf_eq, hdact] using hx)`. Use the proof step `(fun x hx => by`. Take `⟨u, hu⟩` from `fundamentalCone.exists_unit_smul_mem (x := toMixed E x) (by rw [norm_toMixed hE]; exact (lt_of_lt_of_le one_pos hx.1).ne')`. Conclude with `⟨u, by rwa [Set.mem_preimage, toMixed_act hE]⟩)`. Use the proof step `(fun x hx g => by`.

Rewrite using `[Set.mem_preimage, toMixed_act hE]`. Conclude with `fundamentalCone.unit_smul_mem_iff_mem_torsion hx g)`. Use the proof step `(fun x hx g hg => by`. Take `⟨w⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Establish `h0` using `fundamentalCone.normAtPlace_pos_of_mem hx w`.

Rewrite `h0` using `[normAtPlace_apply_of_isComplex (hE.isComplex w), norm_pos_iff]`. Establish `h1 : w.embedding ((g : 𝓞 E) : E) * x w 0 0 = x w 0 0` using `congrFun (congrFun (congrFun hg w) 0) 0`. Establish `h2 : w.embedding ((g : 𝓞 E) : E) = 1` using `(mul_eq_right₀ h0).1 h1`. Rewrite `h2` using `[map_eq_one_iff _ w.embedding.injective]`. Use `ext`.

Simplify using `using h2)`. Establish `hiff : ∀ (D : Set (MatInf E 1)) (x : MatInf E 1), (∃ γ ∈ autGL E 1 Λ, γ * x ∈ D) ↔ ∃ u, act E u x ∈ D`. Introduce `D x`. Establish `hm : ∀ (u : (𝓞 E)ˣ) (γ : MatInf E 1), (∀ w a b, γ w a b = w.embedding ((u : 𝓞 E) : E)) → γ * x = act E u x`. Introduce `u γ hγ`.

Use function extensionality and compare the values at `w a b`. Use `show (Matrix.of (γ w) * Matrix.of (x w)) a b = w.embedding ((u : 𝓞 E) : E) * x w a b`. Rewrite using `[Subsingleton.elim a 0]`. Simplify using `[Matrix.mul_apply, hγ]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨γ, hγ, hx⟩`. Take `⟨u, hu⟩` from `(mem_autGL_iff Λ h γ).1 hγ`. Conclude with `⟨u, by rwa [← hm u γ hu]⟩`. Introduce and unpack `⟨u, hu⟩`. Use `⟨fun w _ _ => w.embedding ((u : 𝓞 E) : E), (mem_autGL_iff Λ h _).2 ⟨u, fun _ _ _ => rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hm u _ fun _ _ _ => rfl]` and apply the resulting hypothesis. Establish `hc : covol (autGL E 1 Λ) (haarGL E 1) {x | 1 ≤ detNorm E 1 x ∧ detNorm E 1 x < Real.exp 1} = μ F`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `iInf_le_of_le F (iInf_le_of_le hF (iInf_le_of_le (fun x hx => (hiff F x).2 (hcov x hx)) le_rfl))`. Conclude with `le_iInf fun D => le_iInf fun hD => le_iInf fun hDc => hmin D hD fun x hx => (hiff D x).1 (hDc x hx)`.

Rewrite using `[hc, Units.torsionOrder, hvol, ← lintegral_cone_slab, withDensity_apply _ (hC.inter hA), ← hφ.setLIntegral_comp_preimage (s := fundamentalCone E ∩ {x | 1 ≤ mixedEmbedding.norm x ∧ mixedEmbedding.norm x < Real.exp 1}) ((measurableSet_fundamentalCone E).inter (hN (measurableSet_Ico …`. Simplify using `only [A, pow_one, ← norm_toMixed hE]`. Both sides reduce to the same expression.
-/
theorem torsion_mul_covol (hE : IsTotallyComplex E) (Λ : Submodule (𝓞 E) (Fin 1 → E))
    (h : Submodule.IsLattice E Λ) :
    (Units.torsionOrder E : ENNReal) *
      covol (autGL E 1 Λ) (haarGL E 1) {x | 1 ≤ detNorm E 1 x ∧ detNorm E 1 x < Real.exp 1} =
      volume (fundamentalCone.normLeOne E) := by
  have hN : Measurable (fun x : mixedSpace E => mixedEmbedding.norm x) :=
    (mixedEmbedding.continuous_norm E).measurable
  have hφ := measurePreserving_toMixed hE
  have hdet : Measurable (fun x : InfinitePlace E → Fin 1 → Fin 1 → ℂ => detNorm E 1 x) := by
    simp only [← norm_toMixed hE]; exact hN.comp hφ.measurable
  have hdact : ∀ u x, detNorm E 1 (act E u x) = detNorm E 1 x := fun u x => by
    rw [← norm_toMixed hE, ← norm_toMixed hE, toMixed_act hE, norm_unit_smul]
  let μ : Measure (InfinitePlace E → Fin 1 → Fin 1 → ℂ) :=
    volume.withDensity fun x => ENNReal.ofReal ((detNorm E 1 x)⁻¹ ^ 1)
  let A : Set (InfinitePlace E → Fin 1 → Fin 1 → ℂ) := {x | 1 ≤ detNorm E 1 x ∧ detNorm E 1 x < Real.exp 1}
  have hA : MeasurableSet A := hdet (measurableSet_Ico (a := 1) (b := Real.exp 1))
  have hC : MeasurableSet (toMixed E ⁻¹' fundamentalCone E) := hφ.measurable (measurableSet_fundamentalCone E)
  have : StandardBorelSpace (Fin 1 → ℂ) := StandardBorelSpace.pi_countable
  have : StandardBorelSpace (Fin 1 → Fin 1 → ℂ) := StandardBorelSpace.pi_countable
  have : StandardBorelSpace (InfinitePlace E → Fin 1 → Fin 1 → ℂ) := StandardBorelSpace.pi_countable
  have : Countable (𝓞 E) := Countable.of_equiv _ (RingOfIntegers.basis E).equivFun.symm.toEquiv
  have : Countable (𝓞 E)ˣ := Units.val_injective.countable
  obtain ⟨F, hF, hcov, hvol, hmin⟩ := exists_domain μ (act E) (fun x => by ext; simp [act])
    (fun g h x => by ext; simp [act, mul_assoc]) measurable_act
    (fun g s hs => by
      rw [withDensity_apply _ hs, withDensity_apply _ (measurable_act g hs),
        ← (measurePreserving_act hE g).setLIntegral_comp_preimage hs (by fun_prop)]
      simp only [hdact])
    (Units.torsion E) (toMixed E ⁻¹' fundamentalCone E) A hC hA
    (fun g x hx => by simpa only [A, Set.mem_setOf_eq, hdact] using hx)
    (fun x hx => by
      obtain ⟨u, hu⟩ := fundamentalCone.exists_unit_smul_mem (x := toMixed E x)
        (by rw [norm_toMixed hE]; exact (lt_of_lt_of_le one_pos hx.1).ne')
      exact ⟨u, by rwa [Set.mem_preimage, toMixed_act hE]⟩)
    (fun x hx g => by
      rw [Set.mem_preimage, toMixed_act hE]
      exact fundamentalCone.unit_smul_mem_iff_mem_torsion hx g)
    (fun x hx g hg => by
      obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
      have h0 := fundamentalCone.normAtPlace_pos_of_mem hx w
      rw [normAtPlace_apply_of_isComplex (hE.isComplex w), norm_pos_iff] at h0
      have h1 : w.embedding ((g : 𝓞 E) : E) * x w 0 0 = x w 0 0 := congrFun (congrFun (congrFun hg w) 0) 0
      have h2 : w.embedding ((g : 𝓞 E) : E) = 1 := (mul_eq_right₀ h0).1 h1
      rw [map_eq_one_iff _ w.embedding.injective] at h2
      ext
      simpa using h2)
  have hiff : ∀ (D : Set (MatInf E 1)) (x : MatInf E 1),
      (∃ γ ∈ autGL E 1 Λ, γ * x ∈ D) ↔ ∃ u, act E u x ∈ D := by
    intro D x
    have hm : ∀ (u : (𝓞 E)ˣ) (γ : MatInf E 1), (∀ w a b, γ w a b = w.embedding ((u : 𝓞 E) : E)) →
        γ * x = act E u x := by
      intro u γ hγ
      funext w a b
      show (Matrix.of (γ w) * Matrix.of (x w)) a b = w.embedding ((u : 𝓞 E) : E) * x w a b
      rw [Subsingleton.elim a 0]
      simp [Matrix.mul_apply, hγ]
    constructor
    · rintro ⟨γ, hγ, hx⟩
      obtain ⟨u, hu⟩ := (mem_autGL_iff Λ h γ).1 hγ
      exact ⟨u, by rwa [← hm u γ hu]⟩
    · rintro ⟨u, hu⟩
      refine ⟨fun w _ _ => w.embedding ((u : 𝓞 E) : E), (mem_autGL_iff Λ h _).2 ⟨u, fun _ _ _ => rfl⟩, ?_⟩
      rwa [hm u _ fun _ _ _ => rfl]
  have hc : covol (autGL E 1 Λ) (haarGL E 1) {x | 1 ≤ detNorm E 1 x ∧ detNorm E 1 x < Real.exp 1} = μ F := by
    apply le_antisymm
    · exact iInf_le_of_le F (iInf_le_of_le hF (iInf_le_of_le (fun x hx => (hiff F x).2 (hcov x hx)) le_rfl))
    · exact le_iInf fun D => le_iInf fun hD => le_iInf fun hDc => hmin D hD fun x hx => (hiff D x).1 (hDc x hx)
  rw [hc, Units.torsionOrder, hvol, ← lintegral_cone_slab, withDensity_apply _ (hC.inter hA),
    ← hφ.setLIntegral_comp_preimage
      (s := fundamentalCone E ∩ {x | 1 ≤ mixedEmbedding.norm x ∧ mixedEmbedding.norm x < Real.exp 1}) ((measurableSet_fundamentalCone E).inter
      (hN (measurableSet_Ico (a := 1) (b := Real.exp 1)))) (by fun_prop)]
  simp only [A, pow_one, ← norm_toMixed hE]
  rfl

end Transport

/- English proof (translation)
Introduce `E _ _ hE`. Take `⟨e⟩` from `nonempty_equiv_classGroup (E := E)`. Establish `hw : (Units.torsionOrder E : ENNReal) ≠ 0` using `by exact_mod_cast (Units.torsionOrder_pos E).ne'`. Establish `hw' : (0 : ℝ) < Units.torsionOrder E` using `by exact_mod_cast (Units.torsionOrder_pos E)`. Rewrite using `[← ENNReal.mul_right_inj hw (ENNReal.natCast_ne_top _), glVol, ← ENNReal.tsum_mul_left, tsum_congr fun c => torsion_mul_covol hE _ (Quot.out c).2, ← e.symm.tsum_eq, tsum_fintype, Finset.sum_const, Finset.card_univ, mixedEmbedding.fundamentalCone.volume_normLeOne]`.

Establish `hr : InfinitePlace.nrRealPlaces E = 0` using `IsTotallyComplex.nrRealPlaces_eq_zero E`. Establish `hf : Formalism.HermitianLatticesTheory.fDeg E = InfinitePlace.nrComplexPlaces E`. Rewrite using `[Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hr, zero_add]`. Establish `hf0 : (Formalism.HermitianLatticesTheory.fDeg E : ℝ) ≠ 0`. Rewrite using `[Formalism.HermitianLatticesTheory.fDeg]`.

Conclude with `Fintype.card_ne_zero` after adjusting the coercions. Establish `hd : 0 < |(discr E : ℝ)|` using `abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero E))`. Establish `hv : Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E = Real.sqrt |(discr E : ℝ)| / 2 ^ Formalism.HermitianLatticesTheory.fDeg E`. Rewrite using `[Formalism.HermitianLatticesTheory.vInv, div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hd.le, Real.sqrt_eq_rpow]`. Use `congr 2`.

Clear the denominators using the available nonvanishing facts. Establish `hs` using `Real.sqrt_pos.2 hd`. Establish `key : (Units.torsionOrder E : ℝ) * (dedekindZeta_residue E * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E) = classNumber E * (Real.pi ^ InfinitePlace.nrComplexPlaces E * Units.regulator E)`. Rewrite using `[hv, dedekindZeta_residue_def, hr, hf, mul_pow]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[← ENNReal.ofReal_natCast (Units.torsionOrder E), ← ENNReal.ofReal_mul hw'.le, key, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow Real.pi_pos.le, hr, pow_zero, one_mul, nsmul_eq_mul, classNumber, ← NNReal.co …`.
-/
theorem glVol_one : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E →
    glVol E 1 = ENNReal.ofReal (dedekindZeta_residue E * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E) := by
  intro E _ _ hE
  classical
  obtain ⟨e⟩ := nonempty_equiv_classGroup (E := E)
  have hw : (Units.torsionOrder E : ENNReal) ≠ 0 := by exact_mod_cast (Units.torsionOrder_pos E).ne'
  have hw' : (0 : ℝ) < Units.torsionOrder E := by exact_mod_cast (Units.torsionOrder_pos E)
  rw [← ENNReal.mul_right_inj hw (ENNReal.natCast_ne_top _), glVol, ← ENNReal.tsum_mul_left,
    tsum_congr fun c => torsion_mul_covol hE _ (Quot.out c).2, ← e.symm.tsum_eq, tsum_fintype,
    Finset.sum_const, Finset.card_univ, mixedEmbedding.fundamentalCone.volume_normLeOne]
  have hr : InfinitePlace.nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  have hf : Formalism.HermitianLatticesTheory.fDeg E = InfinitePlace.nrComplexPlaces E := by
    rw [Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hr, zero_add]
  have hf0 : (Formalism.HermitianLatticesTheory.fDeg E : ℝ) ≠ 0 := by
    rw [Formalism.HermitianLatticesTheory.fDeg]; exact_mod_cast Fintype.card_ne_zero
  have hd : 0 < |(discr E : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero E))
  have hv : Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E = Real.sqrt |(discr E : ℝ)| / 2 ^ Formalism.HermitianLatticesTheory.fDeg E := by
    rw [Formalism.HermitianLatticesTheory.vInv, div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hd.le, Real.sqrt_eq_rpow]
    congr 2
    field_simp
  have hs := Real.sqrt_pos.2 hd
  have key : (Units.torsionOrder E : ℝ) * (dedekindZeta_residue E * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E) =
      classNumber E * (Real.pi ^ InfinitePlace.nrComplexPlaces E * Units.regulator E) := by
    rw [hv, dedekindZeta_residue_def, hr, hf, mul_pow]
    field_simp
  rw [← ENNReal.ofReal_natCast (Units.torsionOrder E), ← ENNReal.ofReal_mul hw'.le, key,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow Real.pi_pos.le, hr, pow_zero, one_mul, nsmul_eq_mul, classNumber,
    ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

end GlobalTheory.NormOneVol
