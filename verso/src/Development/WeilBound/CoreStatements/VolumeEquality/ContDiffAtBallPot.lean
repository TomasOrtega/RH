import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsFundSet

noncomputable section

namespace SheetDecomposition

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ENNReal ComplexOrder

/- English proof (translation)
Establish `hfin : ∀ k, {m | pc m = k ∧ t ∈ B m}.Finite`. Introduce `k`. Distinguish the cases in `hk : t ∈ FF k`. Conclude with `Set.finite_of_encard_eq_coe (ht k hk)`. Use `Set.finite_empty` and compare the differences between its conclusion and the goal.

Use extensionality with `m`. Simplify using `only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]`. Introduce and unpack `rfl hm`. Conclude with `hk (hB m hm)`. Establish `hS : {m | t ∈ B m}.Finite`.

Establish `hU : {m | t ∈ B m} = ⋃ k, {m | pc m = k ∧ t ∈ B m}`. Use extensionality with `m`. Simplify using the standard rewrite rules. Rewrite using `[hU]`. Conclude with `Set.finite_iUnion hfin`.

Use `set s := hS.toFinset with hs`. Establish `hzero : ∀ m ∉ s, (B m).indicator (g (pc m)) t = 0`. Introduce `m hm`. Rewrite `hm` using `[Set.Finite.mem_toFinset]`. Conclude with `Set.indicator_of_notMem (show t ∉ B m from hm) _`.

It suffices to establish `hsum : ∑ k, d k • (FF k).indicator (g k) t = ∑ m ∈ s, (B m).indicator (g (pc m)) t by`. Rewrite using `[hsum]`. Conclude with `hasSum_sum_of_ne_finset_zero hzero`. Establish `h1 : ∑ m ∈ s, (B m).indicator (g (pc m)) t = ∑ m ∈ s, g (pc m) t` using `Finset.sum_congr rfl (fun m hm => Set.indicator_of_mem (show t ∈ B m from hS.mem_toFinset.mp hm) _)`. Rewrite using `[h1, ← Finset.sum_fiberwise s pc (fun m => g (pc m) t)]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k _`. Establish `h2 : ∑ m ∈ s with pc m = k, g (pc m) t = ∑ m ∈ s with pc m = k, g k t` using `Finset.sum_congr rfl (fun m hm => by rw [(Finset.mem_filter.mp hm).2])`. Rewrite using `[h2, Finset.sum_const]`. Distinguish the cases in `hk : t ∈ FF k`.

Rewrite using `[Set.indicator_of_mem hk]`. Use `congr 1`. Establish `hset : ((s.filter (fun m => pc m = k)) : Set ℕ) = {m | pc m = k ∧ t ∈ B m}`. Use extensionality with `m`. Simplify using `[s, and_comm]`.

Establish `hc` using `ht k hk`. Rewrite `hc` using `[← hset, Set.encard_coe_eq_coe_finsetCard]`. Conclude with `hc.symm` after adjusting the coercions. Rewrite using `[Set.indicator_of_notMem hk, smul_zero]`. Establish `he : s.filter (fun m => pc m = k) = ∅`.

Use extensionality with `m`. Simplify using `only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, s, Set.Finite.mem_toFinset, Set.mem_setOf_eq]`. Introduce `hm h`. Conclude with `hk (h ▸ hB m hm)`. Rewrite using `[he, Finset.card_empty, zero_smul]`.
-/
theorem hasSum_sheets {X M : Type*} [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M] {np : ℕ}
    (FF : Fin np → Set X) (pc : ℕ → Fin np) (B : ℕ → Set X) (d : Fin np → ℕ)
    (hB : ∀ m, B m ⊆ FF (pc m)) (g : Fin np → X → M) (t : X)
    (ht : ∀ k, t ∈ FF k → {m | pc m = k ∧ t ∈ B m}.encard = d k) :
    HasSum (fun m => (B m).indicator (g (pc m)) t) (∑ k, d k • (FF k).indicator (g k) t) := by
  classical
  have hfin : ∀ k, {m | pc m = k ∧ t ∈ B m}.Finite := by
    intro k
    by_cases hk : t ∈ FF k
    · exact Set.finite_of_encard_eq_coe (ht k hk)
    · convert Set.finite_empty
      ext m
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      rintro rfl hm
      exact hk (hB m hm)
  have hS : {m | t ∈ B m}.Finite := by
    have hU : {m | t ∈ B m} = ⋃ k, {m | pc m = k ∧ t ∈ B m} := by
      ext m
      simp
    rw [hU]
    exact Set.finite_iUnion hfin
  set s := hS.toFinset with hs
  have hzero : ∀ m ∉ s, (B m).indicator (g (pc m)) t = 0 := by
    intro m hm
    rw [Set.Finite.mem_toFinset] at hm
    exact Set.indicator_of_notMem (show t ∉ B m from hm) _
  suffices hsum : ∑ k, d k • (FF k).indicator (g k) t = ∑ m ∈ s, (B m).indicator (g (pc m)) t by
    rw [hsum]
    exact hasSum_sum_of_ne_finset_zero hzero
  have h1 : ∑ m ∈ s, (B m).indicator (g (pc m)) t = ∑ m ∈ s, g (pc m) t :=
    Finset.sum_congr rfl (fun m hm => Set.indicator_of_mem (show t ∈ B m from hS.mem_toFinset.mp hm) _)
  rw [h1, ← Finset.sum_fiberwise s pc (fun m => g (pc m) t)]
  apply Finset.sum_congr rfl
  intro k _
  have h2 : ∑ m ∈ s with pc m = k, g (pc m) t = ∑ m ∈ s with pc m = k, g k t :=
    Finset.sum_congr rfl (fun m hm => by rw [(Finset.mem_filter.mp hm).2])
  rw [h2, Finset.sum_const]
  by_cases hk : t ∈ FF k
  · rw [Set.indicator_of_mem hk]
    congr 1
    have hset : ((s.filter (fun m => pc m = k)) : Set ℕ) = {m | pc m = k ∧ t ∈ B m} := by
      ext m
      simp [s, and_comm]
    have hc := ht k hk
    rw [← hset, Set.encard_coe_eq_coe_finsetCard] at hc
    exact_mod_cast hc.symm
  · rw [Set.indicator_of_notMem hk, smul_zero]
    have he : s.filter (fun m => pc m = k) = ∅ := by
      ext m
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, s, Set.Finite.mem_toFinset,
        Set.mem_setOf_eq]
      intro hm h
      exact hk (h ▸ hB m hm)
    rw [he, Finset.card_empty, zero_smul]

/- English proof (translation)
Use `set F : ℕ → X → ℝ := fun m => (B m).indicator (f (pc m)) with hFdef`. Establish `hFint : ∀ m, Integrable (F m) μ` using `fun m => ((hf (pc m)).mono_set (hB m)).integrable_indicator (hBm m)`. Establish `hInt : ∀ m, ∫ t in B m, f (pc m) t ∂μ = ∫ t, F m t ∂μ` using `fun m => (integral_indicator (hBm m)).symm`. Establish `hIntAbs : ∀ m, ∫ t in B m, |f (pc m) t| ∂μ = (∫⁻ t, ‖F m t‖ₑ ∂μ).toReal`. Introduce `m`.

Rewrite using `[← integral_norm_eq_lintegral_enorm (hFint m).aestronglyMeasurable, ← integral_indicator (hBm m)]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Simplify using `only [F, Set.indicator_apply]`. Apply the tactic sequence `split_ifs <;> simp [Real.norm_eq_abs]`.

Establish `hae : ∀ᵐ t ∂μ, ∀ k, t ∈ FF k → {m | pc m = k ∧ t ∈ B m}.encard = d k` using `ae_all_iff.mpr hc`. Establish `hmeas : ∀ k, AEMeasurable (fun t => (d k : ℝ≥0∞) * (FF k).indicator (fun x => ‖f k x‖ₑ) t) μ`. Introduce `k`. Apply `AEMeasurable.const_mul` to reduce the goal to its premises. Conclude with `(aemeasurable_indicator_iff (hF k)).mpr (hf k).aestronglyMeasurable.enorm`.

Establish `hlin : ∑' m, ∫⁻ t, ‖F m t‖ₑ ∂μ = ∑ k, (d k : ℝ≥0∞) * ∫⁻ t in FF k, ‖f k t‖ₑ ∂μ`. Rewrite using `[← lintegral_tsum (fun m => (hFint m).aestronglyMeasurable.enorm)]`. Establish `hae1 : ∀ᵐ t ∂μ, ∑' m, ‖F m t‖ₑ = ∑ k, (d k : ℝ≥0∞) * (FF k).indicator (fun x => ‖f k x‖ₑ) t` using `by filter_upwards [hae] with t ht`. Establish `h` using `hasSum_sheets FF pc B d hB (fun k x => ‖f k x‖ₑ) t ht`. Simplify using `only [nsmul_eq_mul] at h`.

Rewrite using `[← h.tsum_eq]`. Use `congr 1`. Use function extensionality and compare the values at `m`. Simplify using `only [F, Set.indicator_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[lintegral_congr_ae hae1, lintegral_finset_sum' _ (fun k _ => hmeas k)]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k _`. Rewrite using `[lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _), lintegral_indicator (hF k)]`. Establish `hne : ∑' m, ∫⁻ t, ‖F m t‖ₑ ∂μ ≠ ⊤`.

Rewrite using `[hlin]`. Conclude with `(ENNReal.sum_lt_top.mpr fun k _ => ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (hf k).hasFiniteIntegral).ne`. Prove the components needed by the constructor for the conclusion. Repeatedly rewrite using `[hIntAbs]`. Conclude with `ENNReal.summable_toReal hne`.

Repeatedly rewrite using `[hInt]`. Rewrite using `[← integral_tsum (fun m => (hFint m).aestronglyMeasurable) hne]`. Establish `hae2 : ∀ᵐ t ∂μ, ∑' m, F m t = ∑ k, (d k : ℝ) * (FF k).indicator (f k) t` using `by filter_upwards [hae] with t ht`. Establish `h` using `(hasSum_sheets FF pc B d hB f t ht).tsum_eq`. Simplify `h` using `only [nsmul_eq_mul]`.

Rewrite using `[integral_congr_ae hae2, integral_finset_sum _ (fun k _ => ((hf k).integrable_indicator (hF k)).const_mul _)]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k _`. Rewrite using `[integral_const_mul, integral_indicator (hF k)]`.
-/
theorem sum_sheets {X : Type*} [MeasurableSpace X] (μ : Measure X) {np : ℕ}
    (FF : Fin np → Set X) (pc : ℕ → Fin np) (B : ℕ → Set X) (d : Fin np → ℕ)
    (hF : ∀ k, MeasurableSet (FF k)) (hBm : ∀ m, MeasurableSet (B m))
    (hB : ∀ m, B m ⊆ FF (pc m)) (f : Fin np → X → ℝ)
    (hc : ∀ k, ∀ᵐ t ∂μ, t ∈ FF k → {m | pc m = k ∧ t ∈ B m}.encard = d k)
    (hf : ∀ k, IntegrableOn (f k) (FF k) μ) :
    Summable (fun m => ∫ t in B m, |f (pc m) t| ∂μ) ∧
      ∑' m, ∫ t in B m, f (pc m) t ∂μ = ∑ k, (d k : ℝ) * ∫ t in FF k, f k t ∂μ := by
  classical
  set F : ℕ → X → ℝ := fun m => (B m).indicator (f (pc m)) with hFdef
  have hFint : ∀ m, Integrable (F m) μ := fun m =>
    ((hf (pc m)).mono_set (hB m)).integrable_indicator (hBm m)
  have hInt : ∀ m, ∫ t in B m, f (pc m) t ∂μ = ∫ t, F m t ∂μ := fun m =>
    (integral_indicator (hBm m)).symm
  have hIntAbs : ∀ m, ∫ t in B m, |f (pc m) t| ∂μ = (∫⁻ t, ‖F m t‖ₑ ∂μ).toReal := by
    intro m
    rw [← integral_norm_eq_lintegral_enorm (hFint m).aestronglyMeasurable, ← integral_indicator (hBm m)]
    congr 1
    funext t
    simp only [F, Set.indicator_apply]
    split_ifs <;> simp [Real.norm_eq_abs]
  have hae : ∀ᵐ t ∂μ, ∀ k, t ∈ FF k → {m | pc m = k ∧ t ∈ B m}.encard = d k := ae_all_iff.mpr hc
  have hmeas : ∀ k, AEMeasurable (fun t => (d k : ℝ≥0∞) * (FF k).indicator (fun x => ‖f k x‖ₑ) t) μ := by
    intro k
    apply AEMeasurable.const_mul
    exact (aemeasurable_indicator_iff (hF k)).mpr (hf k).aestronglyMeasurable.enorm
  have hlin : ∑' m, ∫⁻ t, ‖F m t‖ₑ ∂μ = ∑ k, (d k : ℝ≥0∞) * ∫⁻ t in FF k, ‖f k t‖ₑ ∂μ := by
    rw [← lintegral_tsum (fun m => (hFint m).aestronglyMeasurable.enorm)]
    have hae1 : ∀ᵐ t ∂μ, ∑' m, ‖F m t‖ₑ =
        ∑ k, (d k : ℝ≥0∞) * (FF k).indicator (fun x => ‖f k x‖ₑ) t := by
      filter_upwards [hae] with t ht
      have h := hasSum_sheets FF pc B d hB (fun k x => ‖f k x‖ₑ) t ht
      simp only [nsmul_eq_mul] at h
      rw [← h.tsum_eq]
      congr 1
      funext m
      simp only [F, Set.indicator_apply]
      split_ifs <;> simp
    rw [lintegral_congr_ae hae1, lintegral_finset_sum' _ (fun k _ => hmeas k)]
    apply Finset.sum_congr rfl
    intro k _
    rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _), lintegral_indicator (hF k)]
  have hne : ∑' m, ∫⁻ t, ‖F m t‖ₑ ∂μ ≠ ⊤ := by
    rw [hlin]
    exact (ENNReal.sum_lt_top.mpr fun k _ =>
      ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (hf k).hasFiniteIntegral).ne
  constructor
  · simp_rw [hIntAbs]
    exact ENNReal.summable_toReal hne
  · simp_rw [hInt]
    rw [← integral_tsum (fun m => (hFint m).aestronglyMeasurable) hne]
    have hae2 : ∀ᵐ t ∂μ, ∑' m, F m t = ∑ k, (d k : ℝ) * (FF k).indicator (f k) t := by
      filter_upwards [hae] with t ht
      have h := (hasSum_sheets FF pc B d hB f t ht).tsum_eq
      simpa only [nsmul_eq_mul] using h
    rw [integral_congr_ae hae2,
      integral_finset_sum _ (fun k _ => ((hf k).integrable_indicator (hF k)).const_mul _)]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul, integral_indicator (hF k)]

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

/- English proof (translation)
Establish `hent : ∀ a b, ContDiff ℝ 2 fun t : Fin n → ℂ => ((1 - (ballMat q t τ)ᴴ * ballMat q t τ : Matrix (Fin j') (Fin j') ℂ)) a b`. Introduce `a b`. Simplify using `only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, ballMat, Matrix.of_apply]`. Apply `contDiff_const.sub` to reduce the goal to its premises. Apply `ContDiff.sum` to reduce the goal to its premises.

Introduce `c _`. Apply `ContDiff.mul` to reduce the goal to its premises. Conclude with `(Complex.conjCLE.contDiff).comp (contDiff_apply ℝ ℂ _)`. Conclude with `contDiff_apply ℝ ℂ _`. Simplify using `only [Matrix.det_apply]`.

Apply `ContDiff.sum` to reduce the goal to its premises. Introduce `σ _`. Apply `ContDiff.const_smul` to reduce the goal to its premises. Apply `contDiff_prod` to reduce the goal to its premises. Introduce `i _`.

Conclude with `hent _ _`.
-/
theorem contDiff_ballDet (q : Ψ × Fin j × Fin j' ≃ Fin n) (τ : Ψ) :
    ContDiff ℝ 2 fun t => (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det := by
  have hent : ∀ a b, ContDiff ℝ 2 fun t : Fin n → ℂ =>
      ((1 - (ballMat q t τ)ᴴ * ballMat q t τ : Matrix (Fin j') (Fin j') ℂ)) a b := by
    intro a b
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, ballMat, Matrix.of_apply]
    apply contDiff_const.sub
    apply ContDiff.sum
    intro c _
    apply ContDiff.mul
    · exact (Complex.conjCLE.contDiff).comp (contDiff_apply ℝ ℂ _)
    · exact contDiff_apply ℝ ℂ _
  simp only [Matrix.det_apply]
  apply ContDiff.sum
  intro σ _
  apply ContDiff.const_smul
  apply contDiff_prod
  intro i _
  exact hent _ _

/- English proof (translation)
Use `ContDiffAt.div_const (ContDiffAt.neg (ContDiffAt.sum fun τ _ => ?_)) _` and prove the remaining obligations. Use `ContDiffAt.log (Complex.reCLM.contDiff.comp (contDiff_ballDet q τ)).contDiffAt ?_` and prove the remaining obligations. Conclude with `(Complex.pos_iff.1 (ht τ).det_pos).1.ne'`.
-/
theorem contDiffAt_ballPot (q : Ψ × Fin j × Fin j' ≃ Fin n) {t : Fin n → ℂ} (ht : t ∈ ballDom q) :
    ContDiffAt ℝ 2 (fun t' => ballPot q t' / 2) t := by
  refine ContDiffAt.div_const (ContDiffAt.neg (ContDiffAt.sum fun τ _ => ?_)) _
  refine ContDiffAt.log (Complex.reCLM.contDiff.comp (contDiff_ballDet q τ)).contDiffAt ?_
  exact (Complex.pos_iff.1 (ht τ).det_pos).1.ne'

/- English proof (translation)
Introduce `τ`. Establish `: ballMat q 0 τ = 0` using `by ext a b; simp [ballMat]`. Rewrite using `[this]`. Simplify using `using Matrix.PosDef.one`.
-/
theorem zero_mem_ballDom (q : Ψ × Fin j × Fin j' ≃ Fin n) : (0 : Fin n → ℂ) ∈ ballDom q := by
  intro τ
  have : ballMat q 0 τ = 0 := by ext a b; simp [ballMat]
  rw [this]
  simpa using Matrix.PosDef.one

/- English proof (translation)
Establish `: ∀ τ, ballMat q 0 τ = 0` using `fun τ => by ext a b; simp [ballMat]`. Simplify using `[ballDens, ballPot, this]`.
-/
theorem ballDens_zero (q : Ψ × Fin j × Fin j' ≃ Fin n) : ballDens q 0 = 1 := by
  have : ∀ τ, ballMat q 0 τ = 0 := fun τ => by ext a b; simp [ballMat]
  simp [ballDens, ballPot, this]

/- English proof (translation)
Use `⟨q'.symm.trans ((Equiv.prodCongr e.symm (Equiv.refl _)).trans q), fun t => ?_⟩` and prove the remaining obligations. Establish `hB : ∀ τ', ballMat q' (fun i => t ((q'.symm.trans ((Equiv.prodCongr e.symm (Equiv.refl _)).trans q)) i)) τ' = ballMat q t (e.symm τ')`. Introduce `τ'`. Use extensionality with `a b`. Simplify using `[ballMat]`.

Simplify using `only [ballPot, hB]`. Use `congr 1`. Conclude with `(Equiv.sum_comp e.symm (fun τ => Real.log (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re)).symm`.
-/
theorem ballPot_renumber {Ψ' : Type} [Fintype Ψ'] (e : Ψ ≃ Ψ') (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (q' : Ψ' × Fin j × Fin j' ≃ Fin n) :
    ∃ σ : Equiv.Perm (Fin n), ∀ t, ballPot q t = ballPot q' (fun i => t (σ i)) := by
  refine ⟨q'.symm.trans ((Equiv.prodCongr e.symm (Equiv.refl _)).trans q), fun t => ?_⟩
  have hB : ∀ τ', ballMat q' (fun i => t ((q'.symm.trans
      ((Equiv.prodCongr e.symm (Equiv.refl _)).trans q)) i)) τ' = ballMat q t (e.symm τ') := by
    intro τ'
    ext a b
    simp [ballMat]
  simp only [ballPot, hB]
  congr 1
  exact (Equiv.sum_comp e.symm
    (fun τ => Real.log (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re)).symm

/- English proof (translation)
Use `set L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap (Matrix.toLin' (σ.permMatrix ℂ)) with hLdef`. Establish `hL : (fun (t : Fin n → ℂ) i => t (σ i)) = ⇑L`. Use function extensionality and compare the values at `s`. Simplify using `[L, Matrix.toLin'_apply, Matrix.permMatrix_mulVec]`. Both sides reduce to the same expression.

Rewrite using `[hL, L.fderiv]`. Establish `hdet : LinearMap.det (L : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = ((Equiv.Perm.sign σ : ℤ) : ℂ)`. Simplify using `[L, LinearMap.det_toLin', Matrix.det_permutation]`. Rewrite using `[hdet]`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]`.
-/
theorem norm_det_perm (σ : Equiv.Perm (Fin n)) (t : Fin n → ℂ) :
    ‖LinearMap.det ((fderiv ℂ (fun (t : Fin n → ℂ) i => t (σ i)) t : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))‖ = 1 := by
  set L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.toLin' (σ.permMatrix ℂ)) with hLdef
  have hL : (fun (t : Fin n → ℂ) i => t (σ i)) = ⇑L := by
    funext s
    simp [L, Matrix.toLin'_apply, Matrix.permMatrix_mulVec]
    rfl
  rw [hL, L.fderiv]
  have hdet : LinearMap.det (L : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = ((Equiv.Perm.sign σ : ℤ) : ℂ) := by
    simp [L, LinearMap.det_toLin', Matrix.det_permutation]
  rw [hdet]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

end SheetDecomposition
