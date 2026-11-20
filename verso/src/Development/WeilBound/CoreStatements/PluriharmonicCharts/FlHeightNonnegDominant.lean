import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FormPolyIsHomogeneousAndEval
import Development.AutomorphicSpectrum.Proofs.MetricProofs.KillNoneFormPoly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagHeightPolynomialWeightForm
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XBirat
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XFlArith
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineLevi
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace PositivityTheory.Xgp.block_hermitian_pullback

namespace FlPos

section Fs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨by simpa using contDiffAt_const, by simp [levi]⟩`. Consider the case `insert a s ha ih`. Establish `heq : (fun y => ∑ k ∈ insert a s, c k * f k y) = fun y => (fun y' => ∑ k ∈ s, c k * f k y') y + c a * f a y`. Use function extensionality and compare the values at `y`.

Rewrite using `[Finset.sum_insert ha]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Use `⟨ih.1.add (contDiffAt_const.mul (hf a)), ?_⟩` and prove the remaining obligations. Rewrite using `[levi_add_smul (f := fun y' => ∑ k ∈ s, c k * f k y') (g := f a) (c a) ih.1 (hf a) w]`.

Conclude with `add_nonneg ih.2 (mul_nonneg (hc a) (hl a w))`.
-/
theorem levi_wsum_nonneg {J : Type} [Fintype J] {z : J → ℂ} (c : K → ℝ) (hc : ∀ k, 0 ≤ c k)
    (f : K → (J → ℂ) → ℝ) (hf : ∀ k, ContDiffAt ℝ 2 (f k) z) (hl : ∀ k w, 0 ≤ levi (f k) z w)
    (w : J → ℂ) (s : Finset K) :
    ContDiffAt ℝ 2 (fun y => ∑ k ∈ s, c k * f k y) z ∧
      0 ≤ levi (fun y => ∑ k ∈ s, c k * f k y) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using contDiffAt_const, by simp [levi]⟩
  | insert a s ha ih =>
    have heq : (fun y => ∑ k ∈ insert a s, c k * f k y) =
        fun y => (fun y' => ∑ k ∈ s, c k * f k y') y + c a * f a y := by
      funext y
      rw [Finset.sum_insert ha]
      ring
    rw [heq]
    refine ⟨ih.1.add (contDiffAt_const.mul (hf a)), ?_⟩
    rw [levi_add_smul (f := fun y' => ∑ k ∈ s, c k * f k y') (g := f a) (c a) ih.1 (hf a) w]
    exact add_nonneg ih.2 (mul_nonneg (hc a) (hl a w))

/- English proof (translation)
Use `set F : K → ((Σ k, ι k) → ℂ) → ℝ := fun k y => Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩)) with hF`. Establish `hev : (fun y => Real.log ((fsHerm ι fun k => (a k : ℤ)).h y)) =ᶠ[𝓝 z] fun y => ∑ k ∈ Finset.univ, (a k : ℝ) * F k y`. Establish `hopen : ∀ k, ∀ᶠ y in 𝓝 z, ∃ i, y ⟨k, i⟩ ≠ 0` using `fun k => by`. Take `⟨i, hi⟩` from `hz k`. Conclude with `Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi) fun y hy => ⟨i, hy⟩`.

Use `filter_upwards [Filter.eventually_all.mpr hopen] with y hy`. Establish `hS : ∀ k, 0 < ∑ i, ‖y ⟨k, i⟩‖ ^ 2` using `fun k => by`. Take `⟨i, hi⟩` from `hy k`. Conclude with `Finset.sum_pos' (fun j _ => sq_nonneg ‖y ⟨k, j⟩‖) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩`. Rewrite using `[fsHerm_h]`.

Unfold `refNorm`. Rewrite using `[Real.log_prod fun k _ => (Real.rpow_pos_of_pos (hS k) _).ne']`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Real.log_rpow (hS k)]`. Establish `hρ : (fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩) = Real.sqrt (∑ i, ‖y ⟨k, i⟩‖ ^ 2)`.

Express the relevant statement in the definitionally equal form `‖WithLp.toLp 2 (fun i => y ⟨k, i⟩)‖ = _`. Rewrite using `[EuclideanSpace.norm_eq]`. Simplify using `only [hF]`. Rewrite using `[hρ, Real.log_sqrt (hS k).le]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hblock : ∀ k, ContDiffAt ℝ 2 (F k) z ∧ ∀ v, 0 ≤ levi (F k) z v`. Introduce `k`. Establish `hk0 : (fun i => z ⟨k, i⟩) ≠ 0`. Take `⟨i, hi⟩` from `hz k`.

Conclude with `fun h0 => hi (congrFun h0 i)`. Establish `hφ` using `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_contDiffAt_logρ_id (HilbertSamuel.ProjLine.isSmoothMetric_fs (J := ι k)) hk0`. Establish `hFk : F k = (fun u => Real.log ((fsMetric (ι k)).ρ u)) ∘ FubiniStudyLeviForm.blockProj ι k` using `rfl`. Use `⟨hFk ▸ hφ.comp z ((FubiniStudyLeviForm.blockProj ι k).restrictScalars ℝ).contDiff.contDiffAt, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[hFk, levi_comp v ((FubiniStudyLeviForm.blockProj ι k).analyticAt z) hφ]`.

Conclude with `HilbertSamuel.ProjLine.leviForm_log_fs_nonneg hk0 _`. Express the relevant statement in the definitionally equal form `0 ≤ levi _ z w`. Rewrite using `[levi_congr hev]`. Conclude with `(levi_wsum_nonneg (fun k => (a k : ℝ)) (fun k => Nat.cast_nonneg _) F (fun k => (hblock k).1) (fun k => (hblock k).2) w Finset.univ).2`.
-/
theorem fsHerm_levi (a : K → ℕ) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    0 ≤ leviForm (fun y => Real.log ((fsHerm ι fun k => (a k : ℤ)).h y)) z w := by
  classical
  set F : K → ((Σ k, ι k) → ℂ) → ℝ :=
    fun k y => Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩)) with hF
  have hev : (fun y => Real.log ((fsHerm ι fun k => (a k : ℤ)).h y)) =ᶠ[𝓝 z]
      fun y => ∑ k ∈ Finset.univ, (a k : ℝ) * F k y := by
    have hopen : ∀ k, ∀ᶠ y in 𝓝 z, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, hi⟩ := hz k
      exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
        fun y hy => ⟨i, hy⟩
    filter_upwards [Filter.eventually_all.mpr hopen] with y hy
    have hS : ∀ k, 0 < ∑ i, ‖y ⟨k, i⟩‖ ^ 2 := fun k => by
      obtain ⟨i, hi⟩ := hy k
      exact Finset.sum_pos' (fun j _ => sq_nonneg ‖y ⟨k, j⟩‖)
        ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
    rw [fsHerm_h]
    unfold refNorm
    rw [Real.log_prod fun k _ => (Real.rpow_pos_of_pos (hS k) _).ne']
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Real.log_rpow (hS k)]
    have hρ : (fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩) = Real.sqrt (∑ i, ‖y ⟨k, i⟩‖ ^ 2) := by
      change ‖WithLp.toLp 2 (fun i => y ⟨k, i⟩)‖ = _
      rw [EuclideanSpace.norm_eq]
    simp only [hF]
    rw [hρ, Real.log_sqrt (hS k).le]
    push_cast
    ring
  have hblock : ∀ k, ContDiffAt ℝ 2 (F k) z ∧ ∀ v, 0 ≤ levi (F k) z v := by
    intro k
    have hk0 : (fun i => z ⟨k, i⟩) ≠ 0 := by
      obtain ⟨i, hi⟩ := hz k
      exact fun h0 => hi (congrFun h0 i)
    have hφ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_contDiffAt_logρ_id
      (HilbertSamuel.ProjLine.isSmoothMetric_fs (J := ι k)) hk0
    have hFk : F k = (fun u => Real.log ((fsMetric (ι k)).ρ u)) ∘ FubiniStudyLeviForm.blockProj ι k := rfl
    refine ⟨hFk ▸ hφ.comp z ((FubiniStudyLeviForm.blockProj ι k).restrictScalars ℝ).contDiff.contDiffAt,
      fun v => ?_⟩
    rw [hFk, levi_comp v ((FubiniStudyLeviForm.blockProj ι k).analyticAt z) hφ]
    exact HilbertSamuel.ProjLine.leviForm_log_fs_nonneg hk0 _
  change 0 ≤ levi _ z w
  rw [levi_congr hev]
  exact (levi_wsum_nonneg (fun k => (a k : ℝ)) (fun k => Nat.cast_nonneg _) F
    (fun k => (hblock k).1) (fun k => (hblock k).2) w Finset.univ).2

/- English proof (translation)
Introduce `z _ μ hμ`. Rewrite using `[norm_prod, fsHerm_h]`. Unfold `refNorm`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_le_prod (fun k _ => Finset.prod_nonneg fun _ _ => norm_nonneg _) fun k _ => ?_` and prove the remaining obligations.

Establish `hS : 0 ≤ ∑ i, ‖z ⟨k, i⟩‖ ^ 2` using `Finset.sum_nonneg fun _ _ => sq_nonneg _`. Establish `hle : ∀ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖ ≤ Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ μ ⟨k, i⟩` using `fun i => by`. Rewrite using `[norm_pow]`. Use `pow_le_pow_left₀ (norm_nonneg _) (Real.le_sqrt_of_sq_le ?_) _` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_pow_eq_pow_sum, hμ k]`. Use `_ = (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ (((a k : ℤ) : ℝ) / 2) := by`. Rewrite using `[Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hS]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fsHerm_monomials (P : Ideal (MRing ι)) (a : K → ℕ) :
    MonomialsBounded P (fsHerm ι fun k => (a k : ℤ)) a := by
  intro z _ μ hμ
  rw [norm_prod, fsHerm_h]
  unfold refNorm
  rw [Fintype.prod_sigma]
  refine Finset.prod_le_prod (fun k _ => Finset.prod_nonneg fun _ _ => norm_nonneg _) fun k _ => ?_
  have hS : 0 ≤ ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hle : ∀ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖ ≤ Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ μ ⟨k, i⟩ := fun i => by
    rw [norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) (Real.le_sqrt_of_sq_le ?_) _
    exact Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  calc ∏ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖
      ≤ ∏ i, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ μ ⟨k, i⟩ :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hle i
    _ = Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ a k := by
        rw [Finset.prod_pow_eq_pow_sum, hμ k]
    _ = (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ (((a k : ℤ) : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hS]
        congr 1
        push_cast
        ring

end Fs

/- English proof (translation)
Establish `hcont : Continuous fun c : σ → ℝ => ∑ w : Fin n → σ, a w * ∏ j, c (w j)` using `by fun_prop`. Set `u : ℕ → σ → ℝ` to `fun m p => (⌊c p * ((m : ℝ) + 1)⌋₊ : ℝ) / ((m : ℝ) + 1)`. Establish `hu : Tendsto u atTop (𝓝 c)`. Use `tendsto_pi_nhds.2 fun p => ?_` and prove the remaining obligations. Conclude with `(tendsto_nat_floor_mul_div_atTop (hc p)).comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)`.

Use `ge_of_tendsto' ((hcont.tendsto c).comp hu) fun m => ?_` and prove the remaining obligations. Establish `hm` using `h fun p => ⌊c p * ((m : ℝ) + 1)⌋₊`. Establish `e : (∑ w : Fin n → σ, a w * ∏ j, u m (w j)) = (((m : ℝ) + 1) ^ n)⁻¹ * ∑ w : Fin n → σ, a w * ∏ j, (⌊c (w j) * ((m : ℝ) + 1)⌋₊ : ℝ)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations.

Simplify using `only [u, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Function.comp]`. Rewrite using `[e]`. Conclude with `mul_nonneg (by positivity) hm`.
-/
theorem wordSum_nonneg {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → σ) → ℝ)
    (h : ∀ c : σ → ℕ, 0 ≤ ∑ w : Fin n → σ, a w * ∏ j, (c (w j) : ℝ)) (c : σ → ℝ) (hc : ∀ p, 0 ≤ c p) :
    0 ≤ ∑ w : Fin n → σ, a w * ∏ j, c (w j) := by
  have hcont : Continuous fun c : σ → ℝ => ∑ w : Fin n → σ, a w * ∏ j, c (w j) := by
    fun_prop
  let u : ℕ → σ → ℝ := fun m p => (⌊c p * ((m : ℝ) + 1)⌋₊ : ℝ) / ((m : ℝ) + 1)
  have hu : Tendsto u atTop (𝓝 c) := by
    refine tendsto_pi_nhds.2 fun p => ?_
    exact (tendsto_nat_floor_mul_div_atTop (hc p)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine ge_of_tendsto' ((hcont.tendsto c).comp hu) fun m => ?_
  have hm := h fun p => ⌊c p * ((m : ℝ) + 1)⌋₊
  have e : (∑ w : Fin n → σ, a w * ∏ j, u m (w j)) =
      (((m : ℝ) + 1) ^ n)⁻¹ * ∑ w : Fin n → σ, a w * ∏ j, (⌊c (w j) * ((m : ℝ) + 1)⌋₊ : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [u, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, inv_pow]
    ring
  simp only [Function.comp]
  rw [e]
  exact mul_nonneg (by positivity) hm

section Flag

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

/- English proof (translation)
Establish `hrel : ∀ k, ∃ i, yFl Ψ N ⟨k, i⟩ ≠ 0`. Introduce `k`. Take `⟨i, hi⟩` from `hP.2.1.2.2 k`. Use `⟨i, fun h0 => hi ?_⟩` and prove the remaining obligations. Simplify using `[PFl, mCoordIdeal, RingHom.mem_ker, mConeMap, h0]`.

Take `⟨Ω', _, y', hy, hB⟩` from `PositivityTheory.Xgp.t_birat (FlBlock Ψ N) (FlIdx Ψ N) (ΩFl Ψ N) (yFl Ψ N) hrel`. Establish `hPy : mCoordIdeal y' = PFl Ψ N` using `hy`. Rewrite `hP`, the goal using `[← hPy]`. Establish `hD : 1 ≤ antisymDegree Ψ N` using `Nat.mul_pos Fintype.card_pos (Nat.choose_pos hN)`. Conclude with `hG _ _ Ω' y' (antisymDegree Ψ N) a _ ⊥ II hD hII hP hB rfl bot_le ⟨FlagHeightMultilinear.isSmoothHerm_fsHerm _, fun z hz w _ => fsHerm_levi a hz.1 w⟩ (fsHerm_monomials _ a) (fun z => by simp [fsHerm_h, refNorm])`.
-/
theorem self_nonneg [Nonempty Ψ] (hG : ArithmeticIntersectionNonneg) (II : IntersectionSystem) (hII : IsIntersectionSystem II)
    (hN : 2 ≤ N) (hP : IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1)) (a : FlBlock Ψ N → ℕ) :
    0 ≤ II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (antisymDegree Ψ N + 1)
      fun _ => fsHerm (FlIdx Ψ N) fun k => (a k : ℤ) := by
  have hrel : ∀ k, ∃ i, yFl Ψ N ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hP.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    simp [PFl, mCoordIdeal, RingHom.mem_ker, mConeMap, h0]
  obtain ⟨Ω', _, y', hy, hB⟩ := PositivityTheory.Xgp.t_birat (FlBlock Ψ N) (FlIdx Ψ N) (ΩFl Ψ N) (yFl Ψ N) hrel
  have hPy : mCoordIdeal y' = PFl Ψ N := hy
  rw [← hPy] at hP ⊢
  have hD : 1 ≤ antisymDegree Ψ N := Nat.mul_pos Fintype.card_pos (Nat.choose_pos hN)
  exact hG _ _ Ω' y' (antisymDegree Ψ N) a _ ⊥ II hD hII hP hB rfl bot_le
    ⟨FlagHeightMultilinear.isSmoothHerm_fsHerm _, fun z hz w _ => fsHerm_levi a hz.1 w⟩
    (fsHerm_monomials _ a) (fun z => by simp [fsHerm_h, refNorm])

end Flag

end FlPos

open FlPos in

/- English proof (translation)
Introduce `hIn II hII Ψ _ _ _ N hN lam hlam`. Establish `hP : IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1)` using `(PositivityTheory.Xgp.t_fl_arith Ψ N hN).1`. Establish `hI` using `hII.1 (FlBlock Ψ N) (FlIdx Ψ N)`. Use `set a : (Fin (antisymDegree Ψ N + 1) → Ψ × Fin N) → ℝ := fun w => II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (antisymDegree Ψ N + 1) fun r => yLineFl Ψ N (w r) with ha`. Establish `hnat : ∀ c : Ψ × Fin N → ℕ, 0 ≤ ∑ w, a w * ∏ j, (c (w j) : ℝ)`.

Introduce `c`. Establish `h` using `FlagHeightMultilinear.I_fsHerm_sum hI hP (fun _ p => (c p : ℤ)) (FlLines.yDeg Ψ N)`. Establish `hy0 : ∀ p q, 0 ≤ FlLines.yDeg Ψ N p q` using `fun p q => by`. Unfold `FlLines.yDeg`. Apply the tactic sequence `split_ifs <;> norm_num`.

Establish `hb : (fun q => (((∑ p, (c p : ℤ) • FlLines.yDeg Ψ N p) q).toNat : ℤ)) = ∑ p, (c p : ℤ) • FlLines.yDeg Ψ N p`. Use function extensionality and compare the values at `q`. Use `Int.toNat_of_nonneg ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_apply]`. Conclude with `Finset.sum_nonneg fun p _ => mul_nonneg (Int.natCast_nonneg _) (hy0 p q)`.

Establish `hs` using `self_nonneg hIn.2.1.2.2 II hII.1 hN hP fun q => ((∑ p, (c p : ℤ) • FlLines.yDeg Ψ N p) q).toNat`. Rewrite `hs` using `[hb, h]`. Use `hs.trans_eq (Finset.sum_congr rfl fun w _ => ?_)` and prove the remaining obligations. Rewrite using `[mul_comm]`. Simplify using `only [Int.cast_natCast]`.

Both sides reduce to the same expression. Establish `hzero : ∀ (w : Fin (antisymDegree Ψ N + 1) → Ψ × Fin N) (j : Fin (antisymDegree Ψ N + 1)), ¬ ((w j).2 : ℕ) + 1 < N → a w = 0`. Introduce `w j hj`. Establish `hy : FlLines.yDeg Ψ N (w j) = 0`. Use function extensionality and compare the values at `q`.

Establish `hq` using `q.2.2`. Establish `: ¬ ((q.2 : ℕ) = ((w j).2 : ℕ))` using `by omega`. Simplify using `[FlLines.yDeg, this]`. Conclude with `(FlagHeightMultilinear.fsMultilin hI hP).map_coord_zero (m := fun r => FlLines.yDeg Ψ N (w r)) j hy`. Rewrite using `[(flLines_polys hIn II hII Ψ N hN hP).1, eval_toWt_gap, (formPoly_isHomogeneous_and_eval _ _ _).2]`.

Establish `e : ∑ w, a w * ∏ j, gap lam (w j) = ∑ w, a w * ∏ j, (if ((w j).2 : ℕ) + 1 < N then gap lam (w j) else 0)`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Distinguish the cases in `hw : ∀ j, ((w j).2 : ℕ) + 1 < N`. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun j _ => (if_pos (hw j)).symm`.

Use `push_neg at hw`. Take `⟨j, hj⟩` from `hw`. Rewrite using `[hzero w j (not_lt.2 hj), zero_mul, zero_mul]`. Rewrite using `[e]`. Conclude with `wordSum_nonneg _ a hnat (fun p => if (p.2 : ℕ) + 1 < N then gap lam p else 0) fun p => by split_ifs with hp`.

Conclude with `hlam p hp`. Conclude with `le_rfl`.
-/
theorem flHeight_nonneg_dominant : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → ∀ lam : Ψ × Fin N → ℝ, Dominant lam → 0 ≤ eval lam (hFlPoly Ψ N II) := by
  intro hIn II hII Ψ _ _ _ N hN lam hlam
  have hP : IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) := (PositivityTheory.Xgp.t_fl_arith Ψ N hN).1
  have hI := hII.1 (FlBlock Ψ N) (FlIdx Ψ N)
  set a : (Fin (antisymDegree Ψ N + 1) → Ψ × Fin N) → ℝ := fun w =>
    II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (antisymDegree Ψ N + 1) fun r => yLineFl Ψ N (w r) with ha
  have hnat : ∀ c : Ψ × Fin N → ℕ, 0 ≤ ∑ w, a w * ∏ j, (c (w j) : ℝ) := by
    intro c
    have h := FlagHeightMultilinear.I_fsHerm_sum hI hP (fun _ p => (c p : ℤ)) (FlLines.yDeg Ψ N)
    have hy0 : ∀ p q, 0 ≤ FlLines.yDeg Ψ N p q := fun p q => by
      unfold FlLines.yDeg
      split_ifs <;> norm_num
    have hb : (fun q => (((∑ p, (c p : ℤ) • FlLines.yDeg Ψ N p) q).toNat : ℤ)) =
        ∑ p, (c p : ℤ) • FlLines.yDeg Ψ N p := by
      funext q
      refine Int.toNat_of_nonneg ?_
      rw [Finset.sum_apply]
      exact Finset.sum_nonneg fun p _ => mul_nonneg (Int.natCast_nonneg _) (hy0 p q)
    have hs := self_nonneg hIn.2.1.2.2 II hII.1 hN hP
      fun q => ((∑ p, (c p : ℤ) • FlLines.yDeg Ψ N p) q).toNat
    rw [hb, h] at hs
    refine hs.trans_eq (Finset.sum_congr rfl fun w _ => ?_)
    rw [mul_comm]
    simp only [Int.cast_natCast]
    rfl
  have hzero : ∀ (w : Fin (antisymDegree Ψ N + 1) → Ψ × Fin N) (j : Fin (antisymDegree Ψ N + 1)),
      ¬ ((w j).2 : ℕ) + 1 < N → a w = 0 := by
    intro w j hj
    have hy : FlLines.yDeg Ψ N (w j) = 0 := by
      funext q
      have hq := q.2.2
      have : ¬ ((q.2 : ℕ) = ((w j).2 : ℕ)) := by omega
      simp [FlLines.yDeg, this]
    exact (FlagHeightMultilinear.fsMultilin hI hP).map_coord_zero (m := fun r => FlLines.yDeg Ψ N (w r)) j hy
  rw [(flLines_polys hIn II hII Ψ N hN hP).1, eval_toWt_gap, (formPoly_isHomogeneous_and_eval _ _ _).2]
  have e : ∑ w, a w * ∏ j, gap lam (w j) =
      ∑ w, a w * ∏ j, (if ((w j).2 : ℕ) + 1 < N then gap lam (w j) else 0) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : ∀ j, ((w j).2 : ℕ) + 1 < N
    · congr 1
      exact Finset.prod_congr rfl fun j _ => (if_pos (hw j)).symm
    · push_neg at hw
      obtain ⟨j, hj⟩ := hw
      rw [hzero w j (not_lt.2 hj), zero_mul, zero_mul]
  rw [e]
  exact wordSum_nonneg _ a hnat (fun p => if (p.2 : ℕ) + 1 < N then gap lam p else 0) fun p => by
    split_ifs with hp
    · exact hlam p hp
    · exact le_rfl

end PositivityTheory.Xgp.block_hermitian_pullback
