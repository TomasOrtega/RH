import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSncCoordinatesComplexPointSmoothVarietyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealIndependentBasisLatticeFamilyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFibreExponentialsNearCentreStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelsIsHolomorphicLatticeFamilyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartRescaleFrameChangeStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

section Frame

variable {g r : ℕ}

def colMat (κ : Fin g → Fin r) (f : Fin r → Fin g → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun i j => f (κ j) i

/- English proof (translation)
Use extensionality with `i`. Simplify using `[colMat]`.
-/
theorem colMat_mulVec_single (κ : Fin g → Fin r) (f : Fin r → Fin g → ℂ) (j : Fin g) :
    colMat κ f *ᵥ Pi.single j 1 = f (κ j) := by
  ext i
  simp [colMat]

/- English proof (translation)
The claim follows from `Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => (continuous_apply i).comp (continuous_apply (κ j)))`.
-/
theorem continuous_det_colMat (κ : Fin g → Fin r) : Continuous fun f => (colMat κ f).det :=
  Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply i).comp (continuous_apply (κ j)))

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h, Matrix.one_mulVec]`.
-/
theorem mulVec_mulVec_inv {M : Matrix (Fin g) (Fin g) ℂ} (h : IsUnit M.det) (v : Fin g → ℂ) :
    M *ᵥ (M⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h, Matrix.one_mulVec]

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]`.
-/
theorem inv_mulVec_mulVec {M : Matrix (Fin g) (Fin g) ℂ} (h : IsUnit M.det) (v : Fin g → ℂ) :
    M⁻¹ *ᵥ (M *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]

/- English proof (translation)
Use `hb.map' ((Matrix.mulVecLin M⁻¹).restrictScalars ℝ) ?_` and prove the remaining obligations. Use `LinearMap.ker_eq_bot.2 (Function.LeftInverse.injective (g := fun v => M *ᵥ v) fun v => ?_)` and prove the remaining obligations. Conclude with `mulVec_mulVec_inv h v`.
-/
theorem linearIndependent_inv_mulVec {J : Type} {M : Matrix (Fin g) (Fin g) ℂ} (h : IsUnit M.det)
    {b : J → Fin g → ℂ} (hb : LinearIndependent ℝ b) : LinearIndependent ℝ fun i => M⁻¹ *ᵥ b i := by
  refine hb.map' ((Matrix.mulVecLin M⁻¹).restrictScalars ℝ) ?_
  refine LinearMap.ker_eq_bot.2 (Function.LeftInverse.injective (g := fun v => M *ᵥ v) fun v => ?_)
  exact mulVec_mulVec_inv h v

/- English proof (translation)
Use `⟨linearIndependent_inv_mulVec h hb.1, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[hK, hb.2]`. Establish `key : ∀ m : Fin r → ℤ, M⁻¹ *ᵥ (∑ j, m j • b j) = ∑ j, m j • (M⁻¹ *ᵥ b j)` using `fun m => by`. Express the relevant statement in the definitionally equal form `Matrix.mulVecLin M⁻¹ (∑ j, m j • b j) = ∑ j, m j • Matrix.mulVecLin M⁻¹ (b j)`. Simplify using `only [map_sum, map_zsmul]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm⟩`. Conclude with `⟨m, by rw [← key, ← hm, inv_mulVec_mulVec h]⟩`. Introduce and unpack `⟨m, hm⟩`. Conclude with `⟨m, by rw [hm, ← key, mulVec_mulVec_inv h]⟩`.
-/
theorem IsLatBasis.inv_mulVec {K K' : Set (Fin g → ℂ)} {b : Fin r → Fin g → ℂ} {M : Matrix (Fin g) (Fin g) ℂ}
    (h : IsUnit M.det) (hb : IsLatBasis K b) (hK : ∀ w, w ∈ K' ↔ M *ᵥ w ∈ K) :
    IsLatBasis K' fun i => M⁻¹ *ᵥ b i := by
  refine ⟨linearIndependent_inv_mulVec h hb.1, fun w => ?_⟩
  rw [hK, hb.2]
  have key : ∀ m : Fin r → ℤ, M⁻¹ *ᵥ (∑ j, m j • b j) = ∑ j, m j • (M⁻¹ *ᵥ b j) := fun m => by
    change Matrix.mulVecLin M⁻¹ (∑ j, m j • b j) = ∑ j, m j • Matrix.mulVecLin M⁻¹ (b j)
    simp only [map_sum, map_zsmul]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [← key, ← hm, inv_mulVec_mulVec h]⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [hm, ← key, mulVec_mulVec_inv h]⟩

/- English proof (translation)
Establish `hsp : Submodule.span ℂ (Set.range b) = ⊤`. Use `top_le_iff.1 (hs ▸ Submodule.span_le.2 fun w hw => ?_)` and prove the remaining obligations. Take `⟨m, rfl⟩` from `(hb.2 w).1 hw`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Int.cast_smul_eq_zsmul ℂ]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Take `⟨s, hsub, hss, hli⟩` from `exists_linearIndependent ℂ (Set.range b)`. Rewrite `hss` using `[hsp]`. Set `B` to `Module.Basis.mk hli (by rw [Subtype.range_coe, hss])`. Use `haveI : Finite s := (Set.finite_range b).subset hsub`.

Use `haveI : Fintype s := Fintype.ofFinite _`. Establish `hcard : Fintype.card s = g`. Rewrite using `[← Module.finrank_eq_card_basis B]`. Simplify using the standard rewrite rules. Set `f : Fin g ≃ s` to `(Fintype.equivFinOfCardEq hcard).symm`.

Use `choose idx hidx using fun x : s => hsub x.2`. Use `⟨fun j => idx (f j), ?_⟩` and prove the remaining obligations. Establish `hl : LinearIndependent ℂ (colMat (fun j => idx (f j)) b).col`. Establish `heq : (colMat (fun j => idx (f j)) b).col = Subtype.val ∘ f`. Use extensionality with `j i`.

Simplify using `[colMat, hidx, Matrix.col]`. Rewrite using `[heq]`. Conclude with `hli.comp f f.injective`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hl)`.
-/
theorem exists_frame {K : Set (Fin g → ℂ)} {b : Fin r → Fin g → ℂ} (hb : IsLatBasis K b)
    (hs : Submodule.span ℂ K = ⊤) : ∃ κ : Fin g → Fin r, IsUnit (colMat κ b).det := by
  have hsp : Submodule.span ℂ (Set.range b) = ⊤ := by
    refine top_le_iff.1 (hs ▸ Submodule.span_le.2 fun w hw => ?_)
    obtain ⟨m, rfl⟩ := (hb.2 w).1 hw
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℂ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨s, hsub, hss, hli⟩ := exists_linearIndependent ℂ (Set.range b)
  rw [hsp] at hss
  let B := Module.Basis.mk hli (by rw [Subtype.range_coe, hss])
  haveI : Finite s := (Set.finite_range b).subset hsub
  haveI : Fintype s := Fintype.ofFinite _
  have hcard : Fintype.card s = g := by
    rw [← Module.finrank_eq_card_basis B]
    simp
  let f : Fin g ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  choose idx hidx using fun x : s => hsub x.2
  refine ⟨fun j => idx (f j), ?_⟩
  have hl : LinearIndependent ℂ (colMat (fun j => idx (f j)) b).col := by
    have heq : (colMat (fun j => idx (f j)) b).col = Subtype.val ∘ f := by
      ext j i
      simp [colMat, hidx, Matrix.col]
    rw [heq]
    exact hli.comp f f.injective
  exact (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hl)

end Frame

section Analytic

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {g : ℕ}

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Conclude with `Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => h _ _)`.
-/
theorem analyticAt_det {M : V → Matrix (Fin g) (Fin g) ℂ} {z : V}
    (h : ∀ i j, AnalyticAt ℂ (fun x => M x i j) z) : AnalyticAt ℂ (fun x => (M x).det) z := by
  simp only [Matrix.det_apply']
  exact Finset.analyticAt_fun_sum _ fun σ _ =>
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => h _ _)

/- English proof (translation)
Establish `hadj : AnalyticAt ℂ (fun x => (M x).adjugate i j) z`. Simplify using `only [Matrix.adjugate_apply]`. Use `analyticAt_det fun a b => ?_` and prove the remaining obligations. Distinguish the cases in `hj : a = j`. Substitute `hj` using the available equality.

Simplify using `only [Matrix.updateRow_self]`. Conclude with `analyticAt_const`. Simplify using `only [Matrix.updateRow_ne hj]`. Conclude with `h a b`. Simplify using `only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]`.

Conclude with `((analyticAt_det h).inv hd).mul hadj`.
-/
theorem analyticAt_inv_apply {M : V → Matrix (Fin g) (Fin g) ℂ} {z : V}
    (h : ∀ i j, AnalyticAt ℂ (fun x => M x i j) z) (hd : (M z).det ≠ 0) (i j : Fin g) :
    AnalyticAt ℂ (fun x => (M x)⁻¹ i j) z := by
  have hadj : AnalyticAt ℂ (fun x => (M x).adjugate i j) z := by
    simp only [Matrix.adjugate_apply]
    refine analyticAt_det fun a b => ?_
    by_cases hj : a = j
    · subst hj
      simp only [Matrix.updateRow_self]
      exact analyticAt_const
    · simp only [Matrix.updateRow_ne hj]
      exact h a b
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact ((analyticAt_det h).inv hd).mul hadj

end Analytic

section Sections

open Metric

variable {n g r : ℕ}

/- English proof (translation)
Establish `h1 : ∀ i, b i ∈ K 0` using `fun i => (hb.2 _).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩`. Use `choose ξ h0 han hgr using fun i => hK.2.2.2 0 (mem_ball_self hρ) (b i) (h1 i)`. Set `ζ : (Fin n → ℂ) → Fin r → Fin g → ℂ` to `fun z i => ξ i z`. Establish `hζ0 : ζ 0 = b` using `funext h0`. Establish `hζ : AnalyticAt ℂ ζ 0` using `analyticAt_pi_iff.2 han`.

Establish `e1 : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), AnalyticAt ℂ ζ z` using `hζ.eventually_analyticAt`. Establish `e2 : ∀ i, ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ζ z i ∈ K z` using `fun i => by`. Establish `ht : Filter.Tendsto (fun z => (z, ξ i z)) (𝓝 (0 : Fin n → ℂ)) (𝓝 (0, b i))`. Use `continuousAt_id.prodMk (han i).continuousAt` as an intermediate fact. Rewrite `this` using `[ContinuousAt]`.

Simplify `this` using `[h0 i]`. Conclude with `(ht.eventually (hgr i)).mono fun z h => h.2 rfl`. Establish `hc : Filter.Tendsto ζ (𝓝 0) (𝓝 b)` using `hζ0 ▸ hζ.continuousAt`. Establish `e3 : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), LinearIndependent ℝ (ζ z)` using `hc.eventually hb.1.eventually`. Establish `e4 : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), IsUnit (colMat κ (ζ z)).det`.

Establish `h4 : ∀ᶠ f in 𝓝 b, (colMat κ f).det ≠ 0` using `(continuous_det_colMat κ).continuousAt.eventually_ne hκ.ne_zero`. Conclude with `(hc.eventually h4).mono fun z h => isUnit_iff_ne_zero.2 h`. Take `⟨ε, hε, hall⟩` from `Metric.eventually_nhds_iff_ball.1 (e1.and ((Filter.eventually_all.2 e2).and (e3.and e4)))`. Establish `h2 : 2 * (min ε ρ₁ / 2) = min ε ρ₁` using `by ring`. Establish `hsub : ball (0 : Fin n → ℂ) (2 * (min ε ρ₁ / 2)) ⊆ ball 0 ε`.

Rewrite using `[h2]`. Conclude with `ball_subset_ball (min_le_left _ _)`. Use `⟨min ε ρ₁ / 2, ζ, half_pos (lt_min hε hρ), h2.le.trans (min_le_right _ _), hζ0, fun z hz => (hall z (hsub hz)).1, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨_, h3, h4, h5⟩` from `hall z (hsub hz)`. Conclude with `⟨h3, h4, h5⟩`.
-/
theorem exists_sections {ρ₁ : ℝ} (hρ : 0 < ρ₁) {K : (Fin n → ℂ) → Set (Fin g → ℂ)}
    (hK : IsLatFam (ball 0 ρ₁) K) {b : Fin r → Fin g → ℂ} (hb : IsLatBasis (K 0) b) (κ : Fin g → Fin r)
    (hκ : IsUnit (colMat κ b).det) :
    ∃ (ρ : ℝ) (ζ : (Fin n → ℂ) → Fin r → Fin g → ℂ), 0 < ρ ∧ 2 * ρ ≤ ρ₁ ∧ ζ 0 = b ∧
      AnalyticOnNhd ℂ ζ (ball 0 (2 * ρ)) ∧ ∀ z ∈ ball (0 : Fin n → ℂ) (2 * ρ),
        (∀ i, ζ z i ∈ K z) ∧ LinearIndependent ℝ (ζ z) ∧ IsUnit (colMat κ (ζ z)).det := by
  have h1 : ∀ i, b i ∈ K 0 := fun i => (hb.2 _).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩
  choose ξ h0 han hgr using fun i => hK.2.2.2 0 (mem_ball_self hρ) (b i) (h1 i)
  let ζ : (Fin n → ℂ) → Fin r → Fin g → ℂ := fun z i => ξ i z
  have hζ0 : ζ 0 = b := funext h0
  have hζ : AnalyticAt ℂ ζ 0 := analyticAt_pi_iff.2 han
  have e1 : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), AnalyticAt ℂ ζ z := hζ.eventually_analyticAt
  have e2 : ∀ i, ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ζ z i ∈ K z := fun i => by
    have ht : Filter.Tendsto (fun z => (z, ξ i z)) (𝓝 (0 : Fin n → ℂ)) (𝓝 (0, b i)) := by
      have := continuousAt_id.prodMk (han i).continuousAt
      rw [ContinuousAt] at this
      simpa [h0 i] using this
    exact (ht.eventually (hgr i)).mono fun z h => h.2 rfl
  have hc : Filter.Tendsto ζ (𝓝 0) (𝓝 b) := hζ0 ▸ hζ.continuousAt
  have e3 : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), LinearIndependent ℝ (ζ z) := hc.eventually hb.1.eventually
  have e4 : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), IsUnit (colMat κ (ζ z)).det := by
    have h4 : ∀ᶠ f in 𝓝 b, (colMat κ f).det ≠ 0 :=
      (continuous_det_colMat κ).continuousAt.eventually_ne hκ.ne_zero
    exact (hc.eventually h4).mono fun z h => isUnit_iff_ne_zero.2 h
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff_ball.1
    (e1.and ((Filter.eventually_all.2 e2).and (e3.and e4)))
  have h2 : 2 * (min ε ρ₁ / 2) = min ε ρ₁ := by ring
  have hsub : ball (0 : Fin n → ℂ) (2 * (min ε ρ₁ / 2)) ⊆ ball 0 ε := by
    rw [h2]
    exact ball_subset_ball (min_le_left _ _)
  refine ⟨min ε ρ₁ / 2, ζ, half_pos (lt_min hε hρ), h2.le.trans (min_le_right _ _), hζ0,
    fun z hz => (hall z (hsub hz)).1, fun z hz => ?_⟩
  obtain ⟨_, h3, h4, h5⟩ := hall z (hsub hz)
  exact ⟨h3, h4, h5⟩

def frameSec (ρ : ℝ) (κ : Fin g → Fin r) (ζ : (Fin n → ℂ) → Fin r → Fin g → ℂ) :
    (Fin n → ℂ) → Fin r → Fin g → ℂ :=
  fun z i => (colMat κ (ζ (ρ • z)))⁻¹ *ᵥ ζ (ρ • z) i

/- English proof (translation)
Rewrite `hz`, the goal using `[mem_ball_zero_iff]`. Rewrite using `[norm_smul, Real.norm_eq_abs, abs_of_pos hρ, mul_comm]`. Conclude with `mul_lt_mul_of_pos_right hz hρ`.
-/
theorem smul_mem_ball {ρ : ℝ} (hρ : 0 < ρ) {z : Fin n → ℂ} {s : ℝ} (hz : z ∈ ball (0 : Fin n → ℂ) s) :
    ρ • z ∈ ball (0 : Fin n → ℂ) (s * ρ) := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, mul_comm]
  exact mul_lt_mul_of_pos_right hz hρ

/- English proof (translation)
Introduce `z hz`. Establish `hs` using `smul_mem_ball hρ hz`. Establish `hscale : AnalyticAt ℂ (fun x : Fin n → ℂ => ρ • x) z` using `(analyticAt_id.const_smul : AnalyticAt ℂ (ρ • (id : (Fin n → ℂ) → Fin n → ℂ)) z)`. Establish `hθ : AnalyticAt ℂ (fun x => ζ (ρ • x)) z` using `(han _ hs).comp hscale`. Establish `h1 : ∀ i, AnalyticAt ℂ (fun x => ζ (ρ • x) i) z` using `analyticAt_pi_iff.1 hθ`.

Establish `h2 : ∀ i j, AnalyticAt ℂ (fun x => ζ (ρ • x) i j) z` using `fun i => analyticAt_pi_iff.1 (h1 i)`. Establish `h3 : ∀ i j, AnalyticAt ℂ (fun x => colMat κ (ζ (ρ • x)) i j) z` using `fun i j => h2 (κ j) i`. Use `analyticAt_pi_iff.2 fun i => analyticAt_pi_iff.2 fun j => ?_` and prove the remaining obligations. Simplify using `only [frameSec, Matrix.mulVec, dotProduct]`. Conclude with `Finset.analyticAt_fun_sum _ fun k _ => (analyticAt_inv_apply h3 (hdet _ hs).ne_zero j k).mul (h2 i k)`.
-/
theorem analyticOnNhd_frameSec {ρ : ℝ} (hρ : 0 < ρ) (κ : Fin g → Fin r) {ζ : (Fin n → ℂ) → Fin r → Fin g → ℂ}
    (han : AnalyticOnNhd ℂ ζ (ball 0 (2 * ρ)))
    (hdet : ∀ z ∈ ball (0 : Fin n → ℂ) (2 * ρ), IsUnit (colMat κ (ζ z)).det) :
    AnalyticOnNhd ℂ (frameSec ρ κ ζ) (ball 0 2) := by
  intro z hz
  have hs := smul_mem_ball hρ hz
  have hscale : AnalyticAt ℂ (fun x : Fin n → ℂ => ρ • x) z :=
    (analyticAt_id.const_smul : AnalyticAt ℂ (ρ • (id : (Fin n → ℂ) → Fin n → ℂ)) z)
  have hθ : AnalyticAt ℂ (fun x => ζ (ρ • x)) z := (han _ hs).comp hscale
  have h1 : ∀ i, AnalyticAt ℂ (fun x => ζ (ρ • x) i) z := analyticAt_pi_iff.1 hθ
  have h2 : ∀ i j, AnalyticAt ℂ (fun x => ζ (ρ • x) i j) z := fun i => analyticAt_pi_iff.1 (h1 i)
  have h3 : ∀ i j, AnalyticAt ℂ (fun x => colMat κ (ζ (ρ • x)) i j) z := fun i j => h2 (κ j) i
  refine analyticAt_pi_iff.2 fun i => analyticAt_pi_iff.2 fun j => ?_
  simp only [frameSec, Matrix.mulVec, dotProduct]
  exact Finset.analyticAt_fun_sum _ fun k _ =>
    (analyticAt_inv_apply h3 (hdet _ hs).ne_zero j k).mul (h2 i k)

/- English proof (translation)
Establish `hsub : closedBall (0 : Fin n → ℂ) 1 ⊆ ball 0 2` using `closedBall_subset_ball (by norm_num)`. Take `⟨C, hC⟩` from `(isCompact_closedBall (0 : Fin n → ℂ) 1).exists_bound_of_continuousOn ((analyticOnNhd_frameSec hρ κ han hdet).continuousOn.mono hsub)`. Conclude with `⟨C, fun z hz => hC z (ball_subset_closedBall hz)⟩`.
-/
theorem exists_bound_frameSec {ρ : ℝ} (hρ : 0 < ρ) (κ : Fin g → Fin r) {ζ : (Fin n → ℂ) → Fin r → Fin g → ℂ}
    (han : AnalyticOnNhd ℂ ζ (ball 0 (2 * ρ)))
    (hdet : ∀ z ∈ ball (0 : Fin n → ℂ) (2 * ρ), IsUnit (colMat κ (ζ z)).det) :
    ∃ C : ℝ, ∀ z ∈ ball (0 : Fin n → ℂ) 1, ‖frameSec ρ κ ζ z‖ ≤ C := by
  have hsub : closedBall (0 : Fin n → ℂ) 1 ⊆ ball 0 2 := closedBall_subset_ball (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin n → ℂ) 1).exists_bound_of_continuousOn
    ((analyticOnNhd_frameSec hρ κ han hdet).continuousOn.mono hsub)
  exact ⟨C, fun z hz => hC z (ball_subset_closedBall hz)⟩

/- English proof (translation)
Rewrite using `[frameSec, ← colMat_mulVec_single κ (ζ (ρ • z)) j, inv_mulVec_mulVec h]`.
-/
theorem frameSec_single {ρ : ℝ} (κ : Fin g → Fin r) {ζ : (Fin n → ℂ) → Fin r → Fin g → ℂ}
    {z : Fin n → ℂ} (h : IsUnit (colMat κ (ζ (ρ • z))).det) (j : Fin g) :
    frameSec ρ κ ζ z (κ j) = Pi.single j 1 := by
  rw [frameSec, ← colMat_mulVec_single κ (ζ (ρ • z)) j, inv_mulVec_mulVec h]

end Sections

section Main

open Metric

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

/- English proof (translation)
Establish `h1 : e 0 = 1`. Establish `h2` using `he.1 0 0`. Rewrite `h2` using `[add_zero]`. Conclude with `left_eq_mul.1 h2`. Establish `hl : (e 0).left = (1 : Over.mk y ⟶ t.G).left` using `by rw [h1]`.

Use `GlobalTheory.T.span_periodLattice_complexSemiAbelian_eq_top X t.G y g e t.semi ⟨he.1, hs, hh, fun w => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Take `⟨v, ⟨hv, hd⟩, hu⟩` from `he.2.1 w`. Use `⟨Over.homMk v hv.1, hd, fun v' hv' => ?_⟩` and prove the remaining obligations. Establish `h3 : v'.left = v` using `hu _ ⟨⟨Over.w v', hv'.1.trans hl⟩, hv'⟩`. Conclude with `Over.OverMorphism.ext h3`.

Conclude with `he.2.2 v.left ⟨Over.w v, hv.trans hl⟩`.
-/
theorem span_of_isExpAt {X : Scheme.{0}} (t : SAB H X) (y : Sp ℂ ⟶ X) {g : ℕ}
    (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) (hs : Function.Surjective e)
    (hh : IsHolTo Set.univ fun z => (e z).left) (he : IsExpAt t y e) :
    Submodule.span ℂ {z | e z = 1} = ⊤ := by
  have h1 : e 0 = 1 := by
    have h2 := he.1 0 0
    rw [add_zero] at h2
    exact left_eq_mul.1 h2
  have hl : (e 0).left = (1 : Over.mk y ⟶ t.G).left := by rw [h1]
  refine GlobalTheory.T.span_periodLattice_complexSemiAbelian_eq_top X t.G y g e t.semi ⟨he.1, hs, hh, fun w => ?_, fun v hv => ?_⟩
  · obtain ⟨v, ⟨hv, hd⟩, hu⟩ := he.2.1 w
    refine ⟨Over.homMk v hv.1, hd, fun v' hv' => ?_⟩
    have h3 : v'.left = v := hu _ ⟨⟨Over.w v', hv'.1.trans hl⟩, hv'⟩
    exact Over.OverMorphism.ext h3
  · exact he.2.2 v.left ⟨Over.w v, hv.trans hl⟩

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {σ : c.F →+* ℂ}

/- English proof (translation)
Take `⟨g, ρ₁, ex, hρ₁, hball, hhol2, hexp⟩` from `GlobalTheory.T.exists_holomorphic_fibre_exponentials_near_centre E H Dw l Xo c O β Z σ _ e0 h0t hsymm`. Establish `hfib : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, e0.symm b ∈ e0.source ∧ ‖e0 (e0.symm b)‖ < ρ₁` using `fun b hb => ⟨e0.map_target (hball hb), by rw [e0.right_inv (hball hb)]; exact mem_ball_zero_iff.1 hb⟩`. Establish `hfam : IsLatFam (Metric.ball (0 : Fin n → ℂ) ρ₁) (fun b => {w | ex (e0.symm b) w = 1})` using `GlobalTheory.T.exponentialKernels_isHolomorphicLatticeFamily E H _ Z.t _ g (Metric.ball 0 ρ₁) (fun b => (e0.symm b).1 ≫ genι Z) (fun b => ex (e0.symm b)) Metric.isOpen_ball hhol2 fun b hb => (hexp _ (hfib b hb).1 (hfib b hb).2).2`. Establish `h00` using `Metric.mem_ball_self (x := (0 : Fin n → ℂ)) hρ₁`. Take `⟨r, b, hb⟩` from `GlobalTheory.T.exists_real_independent_basis_lattice_family _ g _ _ 0 hfam h00`.

Establish `hsurj` using `(hexp _ (hfib 0 h00).1 (hfib 0 h00).2).1`. Establish `hspan : Submodule.span ℂ {w | ex (e0.symm 0) w = 1} = ⊤`. Use `span_of_isExpAt Z.t _ (ex (e0.symm 0)) hsurj ?_ (hexp _ (hfib 0 h00).1 (hfib 0 h00).2).2` and prove the remaining obligations. Establish `h` using `HolPeriods.isHolTo_comp hhol2 isOpen_univ (φ := fun w : Fin g → ℂ => ((0 : Fin n → ℂ), w)) ((differentiableOn_const _).prodMk differentiableOn_id) fun w _ => ⟨h00, trivial⟩`. Conclude with `h`.

Take `⟨κ, hκ⟩` from `exists_frame hb hspan`. Take `⟨ρ, ζ, hρ, hle, hζ0, han, hz⟩` from `exists_sections hρ₁ hfam hb κ hκ`. Establish `hsub : Metric.ball (0 : Fin n → ℂ) (2 * ρ) ⊆ Metric.ball 0 ρ₁` using `Metric.ball_subset_ball hle`. Use `⟨g, r, ρ, ex, ζ, κ, hρ, hsub.trans hball, ?_, fun x hx hn => hexp x hx (hn.trans_le hle), hζ0 ▸ hb, han, fun z hz' => ⟨fun i => (hz z hz').1 i, (hz z hz').2⟩⟩` and prove the remaining obligations. Conclude with `LocLift.isHolTo_mono hhol2 (Metric.isOpen_ball.prod isOpen_univ) (Set.prod_mono hsub subset_rfl)`.
-/
theorem exists_chart_sections {n : ℕ} (e0 : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ))
    (h0t : (0 : Fin n → ℂ) ∈ e0.target) (hsymm : IsHolTo e0.target (fun z => (e0.symm z).1)) :
    ∃ (g r : ℕ) (ρ : ℝ) (ex : ExpMaps Z σ g) (ζ : (Fin n → ℂ) → Fin r → Fin g → ℂ) (κ : Fin g → Fin r),
      0 < ρ ∧ Metric.ball 0 (2 * ρ) ⊆ e0.target ∧
      IsHolTo (Metric.ball 0 (2 * ρ) ×ˢ Set.univ)
        (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e0.symm zw.1) zw.2).left) ∧
      (∀ x ∈ e0.source, ‖e0 x‖ < 2 * ρ → Function.Surjective (ex x) ∧ IsExpAt Z.t (x.1 ≫ genι Z) (ex x)) ∧
      IsLatBasis {w | ex (e0.symm 0) w = 1} (ζ 0) ∧ AnalyticOnNhd ℂ ζ (ball 0 (2 * ρ)) ∧
      ∀ z ∈ ball (0 : Fin n → ℂ) (2 * ρ), (∀ i, ex (e0.symm z) (ζ z i) = 1) ∧
        LinearIndependent ℝ (ζ z) ∧ IsUnit (colMat κ (ζ z)).det := by
  obtain ⟨g, ρ₁, ex, hρ₁, hball, hhol2, hexp⟩ := GlobalTheory.T.exists_holomorphic_fibre_exponentials_near_centre E H Dw l Xo c O β Z σ _ e0 h0t hsymm
  have hfib : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, e0.symm b ∈ e0.source ∧ ‖e0 (e0.symm b)‖ < ρ₁ := fun b hb =>
    ⟨e0.map_target (hball hb), by rw [e0.right_inv (hball hb)]; exact mem_ball_zero_iff.1 hb⟩
  have hfam : IsLatFam (Metric.ball (0 : Fin n → ℂ) ρ₁) (fun b => {w | ex (e0.symm b) w = 1}) :=
    GlobalTheory.T.exponentialKernels_isHolomorphicLatticeFamily E H _ Z.t _ g (Metric.ball 0 ρ₁) (fun b => (e0.symm b).1 ≫ genι Z) (fun b => ex (e0.symm b))
      Metric.isOpen_ball hhol2 fun b hb => (hexp _ (hfib b hb).1 (hfib b hb).2).2
  have h00 := Metric.mem_ball_self (x := (0 : Fin n → ℂ)) hρ₁
  obtain ⟨r, b, hb⟩ := GlobalTheory.T.exists_real_independent_basis_lattice_family _ g _ _ 0 hfam h00
  have hsurj := (hexp _ (hfib 0 h00).1 (hfib 0 h00).2).1
  have hspan : Submodule.span ℂ {w | ex (e0.symm 0) w = 1} = ⊤ := by
    refine span_of_isExpAt Z.t _ (ex (e0.symm 0)) hsurj ?_ (hexp _ (hfib 0 h00).1 (hfib 0 h00).2).2
    have h := HolPeriods.isHolTo_comp hhol2 isOpen_univ (φ := fun w : Fin g → ℂ => ((0 : Fin n → ℂ), w))
      ((differentiableOn_const _).prodMk differentiableOn_id) fun w _ => ⟨h00, trivial⟩
    exact h
  obtain ⟨κ, hκ⟩ := exists_frame hb hspan
  obtain ⟨ρ, ζ, hρ, hle, hζ0, han, hz⟩ := exists_sections hρ₁ hfam hb κ hκ
  have hsub : Metric.ball (0 : Fin n → ℂ) (2 * ρ) ⊆ Metric.ball 0 ρ₁ := Metric.ball_subset_ball hle
  refine ⟨g, r, ρ, ex, ζ, κ, hρ, hsub.trans hball, ?_, fun x hx hn => hexp x hx (hn.trans_le hle),
    hζ0 ▸ hb, han, fun z hz' => ⟨fun i => (hz z hz').1 i, (hz z hz').2⟩⟩
  exact LocLift.isHolTo_mono hhol2 (Metric.isOpen_ball.prod isOpen_univ)
    (Set.prod_mono hsub subset_rfl)

/- English proof (translation)
Take `⟨g, r, ρ, ex, ζ, κ, hρ, hball, hhol2, hexp, hlat, han, hz⟩` from `exists_chart_sections e0 h0t hsymm`. Establish `hsubρ : ball (0 : Fin n → ℂ) ρ ⊆ ball 0 (2 * ρ)` using `ball_subset_ball (by linarith)`. Establish `hdet : ∀ z ∈ ball (0 : Fin n → ℂ) (2 * ρ), IsUnit (colMat κ (ζ z)).det` using `fun z hz' => (hz z hz').2.2`. Establish `hdiff : DifferentiableOn ℂ (fun z => colMat κ (ζ z)) (ball 0 ρ)`. Establish `h : DifferentiableOn ℂ (fun z => (fun i j => ζ z (κ j) i : Fin g → Fin g → ℂ)) (ball 0 ρ)`.

Use `differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j => fun z hz' => ?_` and prove the remaining obligations. Establish `hd : DifferentiableAt ℂ ζ z` using `(han z (hsubρ hz')).differentiableAt`. Conclude with `(differentiableAt_pi.1 (differentiableAt_pi.1 hd (κ j)) i).differentiableWithinAt`. Conclude with `h`. Take `⟨e, ex', hch, hsrc, hee, hex'⟩` from `GlobalTheory.T.exists_exponentialChart_rescale_frameChange E H Dw l Xo c O β Z σ n g e0 ex ρ (fun z => colMat κ (ζ z)) hρ (hsubρ.trans hball) hhol hsymm (LocLift.isHolTo_mono hhol2 (isOpen_ball.prod isOpen_univ) (Set.prod_mono hsubρ subset_rfl)) (fun x hx hn => (hexp x hx (by lin …`.

Establish `e00 : e0 (e0.symm 0) = 0` using `e0.right_inv h0t`. Establish `hx0 : e0.symm 0 ∈ e.source`. Rewrite using `[hsrc]`. Use `⟨e0.map_target h0t, ?_⟩` and prove the remaining obligations. Simplify `hρ` using `[e00]`.

Establish `h0b : (0 : Fin n → ℂ) ∈ ball (0 : Fin n → ℂ) (2 * ρ)` using `mem_ball_self (by linarith)`. Establish `key : ∀ z ∈ ball (0 : Fin n → ℂ) 1, e.symm z ∈ e.source ∧ e.symm z = e0.symm (ρ • z) ∧ e0 (e.symm z) = ρ • z` using `fun z hzb => by`. Establish `hzt : z ∈ e.target` using `hch.1.symm ▸ hzb`. Establish `hs` using `e.map_target hzt`. Establish `h1` using `e.right_inv hzt`.

Rewrite `h1` using `[hee _ hs]`. Establish `h2 : e0 (e.symm z) = ρ • z` using `(inv_smul_eq_iff₀ hρ.ne').1 h1`. Establish `hs0 : e.symm z ∈ e0.source` using `(hsrc ▸ hs : e.symm z ∈ e0.source ∩ _).1`. Conclude with `⟨hs, by rw [← h2, e0.left_inv hs0], h2⟩`. Establish `hsc : ∀ z ∈ ball (0 : Fin n → ℂ) 1, ρ • z ∈ ball (0 : Fin n → ℂ) (2 * ρ)` using `fun z hzb => by`.

Establish `h1` using `smul_mem_ball hρ hzb`. Rewrite `h1` using `[_root_.one_mul]`. Conclude with `hsubρ h1`. Use `⟨g, r, e, ex', frameSec ρ κ ζ, hx0, ?_, hch, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hee _ hx0, e00, smul_zero]`.

Introduce `x hx`. Rewrite using `[hbd x (hsrc ▸ hx : x ∈ e0.source ∩ _).1]`. Use `forall₂_congr fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hee x hx]`. Simplify using `[hρ.ne']`.

Introduce `u`. Establish `hx0' : ‖e0 (e0.symm 0)‖ < 2 * ρ`. Rewrite using `[e00, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨w, rfl⟩` from `(hexp _ (e0.map_target h0t) hx0').1 u`.

Use `⟨(colMat κ (ζ 0))⁻¹ *ᵥ w, ?_⟩` and prove the remaining obligations. Rewrite using `[hex' _ hx0, e00, mulVec_mulVec_inv (hdet 0 h0b)]`. Conclude with `(analyticOnNhd_frameSec hρ κ han hdet).mono (ball_subset_ball (by norm_num))`. Introduce `z hzb`. Conclude with `linearIndependent_inv_mulVec (hdet _ (hsc z hzb)) (hz _ (hsc z hzb)).2.1`.

Introduce `z hzb i`. Take `⟨h1, h2, h3⟩` from `key z hzb`. Rewrite using `[hex' _ h1, h3, frameSec, mulVec_mulVec_inv (hdet _ (hsc z hzb)), h2]`. Conclude with `(hz _ (hsc z hzb)).1 i`. Establish `h1 : frameSec ρ κ ζ 0 = fun i => (colMat κ (ζ 0))⁻¹ *ᵥ ζ 0 i`.

Use function extensionality and compare the values at `i`. Simplify using `[frameSec]`. Rewrite using `[h1]`. Use `IsLatBasis.inv_mulVec (hdet 0 h0b) hlat fun w => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq]`.

Rewrite using `[hex' _ hx0, e00]`. Conclude with `exists_bound_frameSec hρ κ han hdet`. Conclude with `fun j => ⟨κ j, fun z hzb => frameSec_single κ (hdet _ (hsc z hzb)) j⟩`.
-/
theorem exists_framed_of_chart {n a : ℕ} (e0 : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ))
    (h0t : (0 : Fin n → ℂ) ∈ e0.target) (hhol : ∀ j, HolAlong e0.source fun x => e0 x j)
    (hsymm : IsHolTo e0.target (fun z => (e0.symm z).1))
    (hbd : ∀ x ∈ e0.source, Inner x ↔ ∀ k : Fin n, (k : ℕ) < a → e0 x k ≠ 0) :
    ∃ (g r₀ : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g)
      (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ), e0.symm 0 ∈ e.source ∧ e (e0.symm 0) = 0 ∧ IsExpChart e ex ∧
      (∀ x ∈ e.source, Inner x ↔ ∀ k : Fin n, (k : ℕ) < a → e x k ≠ 0) ∧ Function.Surjective (ex (e0.symm 0)) ∧
      AnalyticOnNhd ℂ ζ (ball 0 1) ∧ (∀ z ∈ ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) ∧
      (∀ z ∈ ball (0 : Fin n → ℂ) 1, ∀ i, ex (e.symm z) (ζ z i) = 1) ∧
      IsLatBasis {w | ex (e0.symm 0) w = 1} (ζ 0) ∧ (∃ C : ℝ, ∀ z ∈ ball (0 : Fin n → ℂ) 1, ‖ζ z‖ ≤ C) ∧
      ∀ j : Fin g, ∃ i, ∀ z ∈ ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1 := by
  obtain ⟨g, r, ρ, ex, ζ, κ, hρ, hball, hhol2, hexp, hlat, han, hz⟩ := exists_chart_sections e0 h0t hsymm
  have hsubρ : ball (0 : Fin n → ℂ) ρ ⊆ ball 0 (2 * ρ) := ball_subset_ball (by linarith)
  have hdet : ∀ z ∈ ball (0 : Fin n → ℂ) (2 * ρ), IsUnit (colMat κ (ζ z)).det := fun z hz' => (hz z hz').2.2
  have hdiff : DifferentiableOn ℂ (fun z => colMat κ (ζ z)) (ball 0 ρ) := by
    have h : DifferentiableOn ℂ (fun z => (fun i j => ζ z (κ j) i : Fin g → Fin g → ℂ)) (ball 0 ρ) := by
      refine differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j => fun z hz' => ?_
      have hd : DifferentiableAt ℂ ζ z := (han z (hsubρ hz')).differentiableAt
      exact (differentiableAt_pi.1 (differentiableAt_pi.1 hd (κ j)) i).differentiableWithinAt
    exact h
  obtain ⟨e, ex', hch, hsrc, hee, hex'⟩ := GlobalTheory.T.exists_exponentialChart_rescale_frameChange E H Dw l Xo c O β Z σ n g e0 ex ρ
    (fun z => colMat κ (ζ z)) hρ (hsubρ.trans hball) hhol hsymm
    (LocLift.isHolTo_mono hhol2 (isOpen_ball.prod isOpen_univ) (Set.prod_mono hsubρ subset_rfl))
    (fun x hx hn => (hexp x hx (by linarith)).2) hdiff (fun z hz' => hdet z (hsubρ hz'))
  have e00 : e0 (e0.symm 0) = 0 := e0.right_inv h0t
  have hx0 : e0.symm 0 ∈ e.source := by
    rw [hsrc]
    refine ⟨e0.map_target h0t, ?_⟩
    simpa [e00] using hρ
  have h0b : (0 : Fin n → ℂ) ∈ ball (0 : Fin n → ℂ) (2 * ρ) := mem_ball_self (by linarith)
  have key : ∀ z ∈ ball (0 : Fin n → ℂ) 1, e.symm z ∈ e.source ∧ e.symm z = e0.symm (ρ • z) ∧
      e0 (e.symm z) = ρ • z := fun z hzb => by
    have hzt : z ∈ e.target := hch.1.symm ▸ hzb
    have hs := e.map_target hzt
    have h1 := e.right_inv hzt
    rw [hee _ hs] at h1
    have h2 : e0 (e.symm z) = ρ • z := (inv_smul_eq_iff₀ hρ.ne').1 h1
    have hs0 : e.symm z ∈ e0.source := (hsrc ▸ hs : e.symm z ∈ e0.source ∩ _).1
    exact ⟨hs, by rw [← h2, e0.left_inv hs0], h2⟩
  have hsc : ∀ z ∈ ball (0 : Fin n → ℂ) 1, ρ • z ∈ ball (0 : Fin n → ℂ) (2 * ρ) := fun z hzb => by
    have h1 := smul_mem_ball hρ hzb
    rw [_root_.one_mul] at h1
    exact hsubρ h1
  refine ⟨g, r, e, ex', frameSec ρ κ ζ, hx0, ?_, hch, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hee _ hx0, e00, smul_zero]
  · intro x hx
    rw [hbd x (hsrc ▸ hx : x ∈ e0.source ∩ _).1]
    refine forall₂_congr fun k _ => ?_
    rw [hee x hx]
    simp [hρ.ne']
  · intro u
    have hx0' : ‖e0 (e0.symm 0)‖ < 2 * ρ := by
      rw [e00, norm_zero]
      linarith
    obtain ⟨w, rfl⟩ := (hexp _ (e0.map_target h0t) hx0').1 u
    refine ⟨(colMat κ (ζ 0))⁻¹ *ᵥ w, ?_⟩
    rw [hex' _ hx0, e00, mulVec_mulVec_inv (hdet 0 h0b)]
  · exact (analyticOnNhd_frameSec hρ κ han hdet).mono (ball_subset_ball (by norm_num))
  · intro z hzb
    exact linearIndependent_inv_mulVec (hdet _ (hsc z hzb)) (hz _ (hsc z hzb)).2.1
  · intro z hzb i
    obtain ⟨h1, h2, h3⟩ := key z hzb
    rw [hex' _ h1, h3, frameSec, mulVec_mulVec_inv (hdet _ (hsc z hzb)), h2]
    exact (hz _ (hsc z hzb)).1 i
  · have h1 : frameSec ρ κ ζ 0 = fun i => (colMat κ (ζ 0))⁻¹ *ᵥ ζ 0 i := by
      funext i
      simp [frameSec]
    rw [h1]
    refine IsLatBasis.inv_mulVec (hdet 0 h0b) hlat fun w => ?_
    simp only [Set.mem_setOf_eq]
    rw [hex' _ hx0, e00]
  · exact exists_bound_frameSec hρ κ han hdet
  · exact fun j => ⟨κ j, fun z hzb => frameSec_single κ (hdet _ (hsc z hzb)) j⟩

end Main

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Y T σ x₀`. Take `⟨a, e0, hx₀, he0, hhol, hsymm, hbd⟩` from `GlobalTheory.T.exists_snc_coordinates_complexPoint_smoothVariety c.F (gen T.Z) (genStr T.Z) Dw.dim (genBd T.Z) σ T.smooth T.snc x₀`. Establish `hsym0 : e0.symm 0 = x₀` using `by rw [← he0]; exact e0.left_inv hx₀`. Establish `h0t : (0 : Fin Dw.dim → ℂ) ∈ e0.target` using `he0 ▸ e0.map_source hx₀`. Take `⟨g, r₀, e, ex, ζ, h⟩` from `exists_framed_of_chart (a := a) e0 h0t hhol hsymm hbd`.

Rewrite `h` using `[hsym0]`. Conclude with `⟨Dw.dim, a, g, r₀, e, ex, ζ, h⟩`.
-/
theorem exists_framed_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (x₀ : CxPts (genStr T.Z) σ), ∃ (n a g r₀ : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ), x₀ ∈ e.source ∧ e x₀ = 0 ∧ IsExpChart e ex ∧ (∀ x ∈ e.source, Inner x ↔ ∀ k : Fin n, (k : ℕ) < a → e x k ≠ 0) ∧ Function.Surjective (ex x₀) ∧ AnalyticOnNhd ℂ ζ (Metric.ball 0 1) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ex (e.symm z) (ζ z i) = 1) ∧ IsLatBasis {w | ex x₀ w = 1} (ζ 0) ∧ (∃ C : ℝ, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ‖ζ z‖ ≤ C) ∧ ∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1 := by
  intro E _ _ _ H Dw l Xo c O _ β Y T σ x₀
  obtain ⟨a, e0, hx₀, he0, hhol, hsymm, hbd⟩ :=
    GlobalTheory.T.exists_snc_coordinates_complexPoint_smoothVariety c.F (gen T.Z) (genStr T.Z) Dw.dim (genBd T.Z) σ T.smooth T.snc x₀
  have hsym0 : e0.symm 0 = x₀ := by rw [← he0]; exact e0.left_inv hx₀
  have h0t : (0 : Fin Dw.dim → ℂ) ∈ e0.target := he0 ▸ e0.map_source hx₀
  obtain ⟨g, r₀, e, ex, ζ, h⟩ := exists_framed_of_chart (a := a) e0 h0t hhol hsymm hbd
  rw [hsym0] at h
  exact ⟨Dw.dim, a, g, r₀, e, ex, ζ, h⟩

end GlobalTheory.ShFam.Hor.LogCh
