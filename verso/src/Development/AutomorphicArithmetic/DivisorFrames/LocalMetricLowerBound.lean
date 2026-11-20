import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolAdapted
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefUniformBoundsNearPointStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open CategoryTheory AlgebraicGeometry GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo
open GlobalTheory.MatDeriv GlobalTheory.GradedNorm Matrix
open scoped ComplexOrder
open GlobalTheory.ShFam.Hor GlobalTheory.HermFrame GlobalTheory.Toroidal

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (h i k) (norm_le_pi_norm v k) (norm_nonneg _) hb`. Use `_ = m * b * ‖v‖ := by simp [mul_assoc]`.
-/
private theorem norm_mulVec_le_of_entry {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i k, ‖M i k‖ ≤ b) (v : Fin m → ℂ) : ‖M *ᵥ v‖ ≤ m * b * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖(M *ᵥ v) i‖ = ‖∑ k, M i k * v k‖ := rfl
    _ ≤ ∑ k, ‖M i k * v k‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin m, b * ‖v‖ := Finset.sum_le_sum fun k _ => by
        rw [norm_mul]
        exact mul_le_mul (h i k) (norm_le_pi_norm v k) (norm_nonneg _) hb
    _ = m * b * ‖v‖ := by simp [mul_assoc]

/- English proof (translation)
Establish `hc : ContinuousAt H w₀` using `continuousAt_pi.2 fun a => continuousAt_pi.2 fun b => (h1 a b).continuousAt`. Take `⟨c, C, hc0, hC0, hq⟩` from `GlobalTheory.T.posDef_uniform_bounds_near_point E (Fin m) H w₀ hc hp`. Establish `hu : IsUnit (H w₀).det` using `(isUnit_iff_isUnit_det _).1 hp.isUnit`. Establish `hinv : ContinuousAt (fun w => (H w)⁻¹) w₀`. Use `ContinuousAt.comp (f := H) (g := fun A : Matrix (Fin m) (Fin m) ℂ => A⁻¹) ?_ hc` and prove the remaining obligations.

Use `continuousAt_matrix_inv _ ?_` and prove the remaining obligations. Rewrite using `[Ring.inverse_eq_inv']`. Conclude with `continuousAt_inv₀ hu.ne_zero`. Set `f : E → (Fin m → Fin m → ℂ × (E →L[ℝ] ℂ))` to `fun z i k => ((H z)⁻¹ i k, fderiv ℝ (fun x => H x i k) z)`. Establish `hf : ContinuousAt f w₀` using `continuousAt_pi.2 fun i => continuousAt_pi.2 fun k => (continuousAt_pi.1 (continuousAt_pi.1 hinv i) k).prodMk ((h1 i k).fderiv_right (m := 0) (by norm_num)).continuousAt`.

Use `set B := ‖f w₀‖ + 1 with hBdef`. Establish `hB : 0 ≤ B` using `by positivity`. Use `⟨c, max C (m * B * (m * B)), hc0, le_max_of_le_left hC0, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hf.norm.eventually_lt continuousAt_const (lt_add_one ‖f w₀‖), hq, Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k => (h1 i k).eventually (by simp)] with z hz hqz ha`. Establish `hik : ∀ i k, ‖f z i k‖ ≤ B` using `fun i k => (norm_le_pi_norm (f z i) k).trans ((norm_le_pi_norm (f z) i).trans hz.le)`.

Use `⟨fun a b => (ha a b).differentiableAt (by norm_num), fun v => ⟨(hqz v).1, (hqz v).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)), fun ξ => ?_⟩⟩` and prove the remaining obligations. Establish `hd : ∀ (η : E) i k, ‖dMat H z η i k‖ ≤ B * ‖η‖` using `fun η i k => (fderiv ℝ (fun x => H x i k) z).le_of_opNorm_le ((norm_snd_le (f z i k)).trans (hik i k)) η`. Establish `hw : ∀ i k, ‖wirt H z ξ i k‖ ≤ B * ‖ξ‖` using `fun i k => by`. Establish `e : wirt H z ξ i k = (1 / 2 : ℂ) * (dMat H z ξ i k - Complex.I * dMat H z (Complex.I • ξ) i k)` using `rfl`. Establish `a1` using `hd ξ i k`.

Establish `a2` using `hd (Complex.I • ξ) i k`. Rewrite `a2` using `[norm_smul, Complex.norm_I, one_mul]`. Establish `a3` using `norm_sub_le (dMat H z ξ i k) (Complex.I * dMat H z (Complex.I • ξ) i k)`. Rewrite `a3` using `[norm_mul, Complex.norm_I, one_mul]`. Rewrite using `[e, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← mulVec_mulVec]`. Apply the tactic sequence `have b1 := norm_mulVec_le_of_entry (H z)⁻¹ hB (fun i k => (norm_fst_le (f z i k)).trans (hik i k)) (wirt H z ξ *ᵥ v)`. Apply the tactic sequence `have b2 := norm_mulVec_le_of_entry (wirt H z ξ) (by positivity) hw v`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem local_bounds {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ}
    (H : E → Matrix (Fin m) (Fin m) ℂ) (w₀ : E) (h1 : ∀ a b, ContDiffAt ℝ 1 (fun w => H w a b) w₀)
    (hp : (H w₀).PosDef) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ w in nhds w₀, (∀ a b, DifferentiableAt ℝ (fun w => H w a b) w) ∧
      ∀ v : Fin m → ℂ, c * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ H w *ᵥ v).re ∧ (star v ⬝ᵥ H w *ᵥ v).re ≤ C * ‖v‖ ^ 2 ∧
        ∀ ξ : E, ‖((H w)⁻¹ * wirt H w ξ) *ᵥ v‖ ≤ C * ‖ξ‖ * ‖v‖ := by
  have hc : ContinuousAt H w₀ := continuousAt_pi.2 fun a => continuousAt_pi.2 fun b => (h1 a b).continuousAt
  obtain ⟨c, C, hc0, hC0, hq⟩ := GlobalTheory.T.posDef_uniform_bounds_near_point E (Fin m) H w₀ hc hp
  have hu : IsUnit (H w₀).det := (isUnit_iff_isUnit_det _).1 hp.isUnit
  have hinv : ContinuousAt (fun w => (H w)⁻¹) w₀ := by
    refine ContinuousAt.comp (f := H) (g := fun A : Matrix (Fin m) (Fin m) ℂ => A⁻¹) ?_ hc
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hu.ne_zero
  let f : E → (Fin m → Fin m → ℂ × (E →L[ℝ] ℂ)) := fun z i k =>
    ((H z)⁻¹ i k, fderiv ℝ (fun x => H x i k) z)
  have hf : ContinuousAt f w₀ := continuousAt_pi.2 fun i => continuousAt_pi.2 fun k =>
    (continuousAt_pi.1 (continuousAt_pi.1 hinv i) k).prodMk
      ((h1 i k).fderiv_right (m := 0) (by norm_num)).continuousAt
  set B := ‖f w₀‖ + 1 with hBdef
  have hB : 0 ≤ B := by positivity
  refine ⟨c, max C (m * B * (m * B)), hc0, le_max_of_le_left hC0, ?_⟩
  filter_upwards [hf.norm.eventually_lt continuousAt_const (lt_add_one ‖f w₀‖), hq,
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k => (h1 i k).eventually (by simp)] with z hz hqz ha
  have hik : ∀ i k, ‖f z i k‖ ≤ B := fun i k =>
    (norm_le_pi_norm (f z i) k).trans ((norm_le_pi_norm (f z) i).trans hz.le)
  refine ⟨fun a b => (ha a b).differentiableAt (by norm_num), fun v => ⟨(hqz v).1,
    (hqz v).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)), fun ξ => ?_⟩⟩
  have hd : ∀ (η : E) i k, ‖dMat H z η i k‖ ≤ B * ‖η‖ := fun η i k =>
    (fderiv ℝ (fun x => H x i k) z).le_of_opNorm_le ((norm_snd_le (f z i k)).trans (hik i k)) η
  have hw : ∀ i k, ‖wirt H z ξ i k‖ ≤ B * ‖ξ‖ := fun i k => by
    have e : wirt H z ξ i k = (1 / 2 : ℂ) * (dMat H z ξ i k - Complex.I * dMat H z (Complex.I • ξ) i k) := rfl
    have a1 := hd ξ i k
    have a2 := hd (Complex.I • ξ) i k
    rw [norm_smul, Complex.norm_I, one_mul] at a2
    have a3 := norm_sub_le (dMat H z ξ i k) (Complex.I * dMat H z (Complex.I • ξ) i k)
    rw [norm_mul, Complex.norm_I, one_mul] at a3
    rw [e, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
    linarith
  rw [← mulVec_mulVec]
  have b1 := norm_mulVec_le_of_entry (H z)⁻¹ hB (fun i k => (norm_fst_le (f z i k)).trans (hik i k)) (wirt H z ξ *ᵥ v)
  have b2 := norm_mulVec_le_of_entry (wirt H z ξ) (by positivity) hw v
  calc _ ≤ m * B * (m * (B * ‖ξ‖) * ‖v‖) := b1.trans (mul_le_mul_of_nonneg_left b2 (by positivity))
    _ = m * B * (m * B) * ‖ξ‖ * ‖v‖ := by ring
    _ ≤ _ := by gcongr; exact le_max_right _ _

/- English proof (translation)
Introduce `D O x P _ _ _ c σ ch U g hA y₀ hy₀`. Establish `hF` using `hA.2.2.2.2.2 (x.eigMet (embOf O.κ.e σ)) Set.univ isOpen_univ (OddPrimesWithRootsOfUnity.smoothOn_eigMet _ _)`. Establish `hmem : ch.e y₀ ∈ ch.e '' (U ∩ {p | (O.Φ.C c).down p ∈ Set.univ})` using `⟨y₀, ⟨hy₀, Set.mem_univ _⟩, rfl⟩`. Establish `hloc` using `fun τ : D.host.E →+* ℂ => local_bounds (GlobalTheory.BdGram.gramIn O (x.eigMet (embOf O.κ.e σ)) ch g τ) (ch.e y₀) (fun a b => (((hF τ).smooth b a).contDiffAt ((hF τ).isOpen.mem_nhds hmem)).of_le (by exact_mod_cast le_top)) (by simpa using ((hF τ).posDef _ hmem).transpose)`. Use `choose c₀ C₀ hc₀ hC₀ hev using hloc`.

Establish `hcont : ContinuousAt ch.e y₀` using `ch.e.continuousAt (hA.2.1 hy₀)`. Establish `hall` using `hcont.eventually (Filter.eventually_all.2 hev)`. Take `⟨V, hV, hVo, hyV⟩` from `eventually_nhds_iff.1 hall`. Establish `hS : 0 ≤ ∑ τ, 1 / c₀ τ` using `Finset.sum_nonneg fun τ _ => (one_div_pos.2 (hc₀ τ)).le`. Establish `hcle : ∀ τ, 1 / (1 + ∑ τ, 1 / c₀ τ) ≤ c₀ τ` using `fun τ => by`.

Establish `h1 : 1 / c₀ τ ≤ ∑ τ, 1 / c₀ τ` using `Finset.single_le_sum (f := fun τ => 1 / c₀ τ) (fun τ _ => (one_div_pos.2 (hc₀ τ)).le) (Finset.mem_univ τ)`. Conclude with `(one_div_le (by positivity) (hc₀ τ)).2 (by linarith)`. Establish `hCle : ∀ τ, C₀ τ ≤ ∑ τ, C₀ τ` using `fun τ => Finset.single_le_sum (fun τ _ => hC₀ τ) (Finset.mem_univ τ)`. Use `⟨V ∩ U, 1 / (1 + ∑ τ, 1 / c₀ τ), ∑ τ, C₀ τ, hVo.inter hA.1, ⟨hyV, hy₀⟩, Set.inter_subset_right, by positivity, fun y hy τ => ?_⟩` and prove the remaining obligations. Take `⟨hd, hb⟩` from `hV y hy.1 τ`.

Use `⟨hd, fun v => ?_⟩` and prove the remaining obligations. Take `⟨b1, b2, b3⟩` from `hb v`. Conclude with `⟨(mul_le_mul_of_nonneg_right (hcle τ) (by positivity)).trans b1, b2.trans (mul_le_mul_of_nonneg_right (hCle τ) (by positivity)), fun ξ => (b3 ξ).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCle τ) (norm_nonneg _)) (norm_nonneg _))⟩`.
-/
theorem UpperTheory.local_metric_lower_bound :
    OnCore fun D O x P => ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (U : Set (GlobalTheory.CxPts (O.var c).str σ)) (g : ∀ p : GlobalTheory.CxPts (O.var c).str σ, (O.Φ.C c).FrameAt p), GlobalTheory.BdGram.IsHolAdapted O ch U g →
      ∀ y₀ ∈ U, ∃ (V : Set (GlobalTheory.CxPts (O.var c).str σ)) (c₀ C₀ : ℝ), IsOpen V ∧ y₀ ∈ V ∧ V ⊆ U ∧ 0 < c₀ ∧
        ∀ y ∈ V, ∀ τ : D.host.E →+* ℂ, (∀ a b, DifferentiableAt ℝ (fun w => GlobalTheory.BdGram.gramIn O (x.eigMet (embOf O.κ.e σ)) ch g τ w a b) (ch.e y)) ∧
          ∀ v : Fin (O.S.Dw.mult τ) → ℂ, c₀ * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ GlobalTheory.BdGram.gramIn O (x.eigMet (embOf O.κ.e σ)) ch g τ (ch.e y) *ᵥ v).re ∧
            (star v ⬝ᵥ GlobalTheory.BdGram.gramIn O (x.eigMet (embOf O.κ.e σ)) ch g τ (ch.e y) *ᵥ v).re ≤ C₀ * ‖v‖ ^ 2 ∧
            ∀ ξ : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim, ‖((GlobalTheory.BdGram.gramIn O (x.eigMet (embOf O.κ.e σ)) ch g τ (ch.e y))⁻¹ * wirt (GlobalTheory.BdGram.gramIn O (x.eigMet (embOf O.κ.e σ)) ch g τ) (ch.e y) ξ) *ᵥ v‖ ≤ C₀ * ‖ξ‖ * ‖v‖ := by
  intro D O x P _ _ _ c σ ch U g hA y₀ hy₀
  have hF := hA.2.2.2.2.2 (x.eigMet (embOf O.κ.e σ)) Set.univ isOpen_univ (OddPrimesWithRootsOfUnity.smoothOn_eigMet _ _)
  have hmem : ch.e y₀ ∈ ch.e '' (U ∩ {p | (O.Φ.C c).down p ∈ Set.univ}) := ⟨y₀, ⟨hy₀, Set.mem_univ _⟩, rfl⟩
  have hloc := fun τ : D.host.E →+* ℂ => local_bounds (GlobalTheory.BdGram.gramIn O (x.eigMet (embOf O.κ.e σ)) ch g τ) (ch.e y₀)
    (fun a b => (((hF τ).smooth b a).contDiffAt ((hF τ).isOpen.mem_nhds hmem)).of_le (by exact_mod_cast le_top))
    (by simpa using ((hF τ).posDef _ hmem).transpose)
  choose c₀ C₀ hc₀ hC₀ hev using hloc
  have hcont : ContinuousAt ch.e y₀ := ch.e.continuousAt (hA.2.1 hy₀)
  have hall := hcont.eventually (Filter.eventually_all.2 hev)
  obtain ⟨V, hV, hVo, hyV⟩ := eventually_nhds_iff.1 hall
  have hS : 0 ≤ ∑ τ, 1 / c₀ τ := Finset.sum_nonneg fun τ _ => (one_div_pos.2 (hc₀ τ)).le
  have hcle : ∀ τ, 1 / (1 + ∑ τ, 1 / c₀ τ) ≤ c₀ τ := fun τ => by
    have h1 : 1 / c₀ τ ≤ ∑ τ, 1 / c₀ τ :=
      Finset.single_le_sum (f := fun τ => 1 / c₀ τ) (fun τ _ => (one_div_pos.2 (hc₀ τ)).le) (Finset.mem_univ τ)
    exact (one_div_le (by positivity) (hc₀ τ)).2 (by linarith)
  have hCle : ∀ τ, C₀ τ ≤ ∑ τ, C₀ τ := fun τ =>
    Finset.single_le_sum (fun τ _ => hC₀ τ) (Finset.mem_univ τ)
  refine ⟨V ∩ U, 1 / (1 + ∑ τ, 1 / c₀ τ), ∑ τ, C₀ τ, hVo.inter hA.1, ⟨hyV, hy₀⟩, Set.inter_subset_right,
    by positivity, fun y hy τ => ?_⟩
  obtain ⟨hd, hb⟩ := hV y hy.1 τ
  refine ⟨hd, fun v => ?_⟩
  obtain ⟨b1, b2, b3⟩ := hb v
  exact ⟨(mul_le_mul_of_nonneg_right (hcle τ) (by positivity)).trans b1,
    b2.trans (mul_le_mul_of_nonneg_right (hCle τ) (by positivity)), fun ξ => (b3 ξ).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCle τ) (norm_nonneg _)) (norm_nonneg _))⟩
