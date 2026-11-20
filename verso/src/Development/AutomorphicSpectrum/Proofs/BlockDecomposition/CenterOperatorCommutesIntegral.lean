import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace Topology
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.ZOpAvg

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/- English proof (translation)
The claim follows from `isOpen_ne.preimage (Continuous.matrix_det continuous_id)`.
-/
theorem isOpen_invertible_matrices (n : ℕ) : IsOpen (GLs n) :=
  isOpen_ne.preimage (Continuous.matrix_det continuous_id)

def Sm (U : ℝ → Mat n → V) : Prop :=
  ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n)

section Gen

variable {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]

/- English proof (translation)
Establish `hd : DifferentiableAt ℝ (Function.uncurry U) (t, x)` using `(hU.contDiffAt ((isOpen_univ.prod hS).mem_nhds ⟨Set.mem_univ _, hx⟩)).differentiableAt (by simp)`. Establish `hi : HasFDerivAt (fun y : E => (t, y)) (ContinuousLinearMap.inr ℝ ℝ E) x` using `hasFDerivAt_prodMk_right t x`. Conclude with `hd.hasFDerivAt.comp x hi`.
-/
theorem fderiv_slice {S : Set E} (hS : IsOpen S) {U : ℝ → E → W}
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ S)) {t : ℝ} {x : E} (hx : x ∈ S) :
    HasFDerivAt (U t) ((fderiv ℝ (Function.uncurry U) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) x := by
  have hd : DifferentiableAt ℝ (Function.uncurry U) (t, x) :=
    (hU.contDiffAt ((isOpen_univ.prod hS).mem_nhds ⟨Set.mem_univ _, hx⟩)).differentiableAt (by simp)
  have hi : HasFDerivAt (fun y : E => (t, y)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
    hasFDerivAt_prodMk_right t x
  exact hd.hasFDerivAt.comp x hi

/- English proof (translation)
Establish `h1 : ContDiff ℝ ∞ (fun p : ℝ × E => ((0 : ℝ), c p.2))` using `contDiff_const.prodMk (hc.comp contDiff_snd)`. Establish `h0 : ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry U)) (Set.univ ×ˢ S)` using `ContDiffOn.fderiv_of_isOpen hU (isOpen_univ.prod hS) (by simp)`. Establish `h2` using `h0.clm_apply h1.contDiffOn`. Use `h2.congr ?_` and prove the remaining obligations. Introduce and unpack `⟨t, x⟩ ⟨-, hx⟩`.

Simplify using `[Function.uncurry, (fderiv_slice hS hU hx).fderiv]`.
-/
theorem gen_sm {S : Set E} (hS : IsOpen S) {U : ℝ → E → W}
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ S)) {c : E → E} (hc : ContDiff ℝ ∞ c) :
    ContDiffOn ℝ ∞ (Function.uncurry fun t x => fderiv ℝ (U t) x (c x)) (Set.univ ×ˢ S) := by
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × E => ((0 : ℝ), c p.2)) :=
    contDiff_const.prodMk (hc.comp contDiff_snd)
  have h0 : ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry U)) (Set.univ ×ˢ S) :=
    ContDiffOn.fderiv_of_isOpen hU (isOpen_univ.prod hS) (by simp)
  have h2 := h0.clm_apply h1.contDiffOn
  refine h2.congr ?_
  rintro ⟨t, x⟩ ⟨-, hx⟩
  simp [Function.uncurry, (fderiv_slice hS hU hx).fderiv]

/- English proof (translation)
Use `Continuous.integrable_of_hasCompactSupport (hg.smul hφ) ?_` and prove the remaining obligations. Conclude with `hgc.smul_right`.
-/
theorem int_real {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {φ : ℝ → W} (hφ : Continuous φ) : Integrable (fun t => g t • φ t) := by
  refine Continuous.integrable_of_hasCompactSupport (hg.smul hφ) ?_
  exact hgc.smul_right

/- English proof (translation)
Take `⟨r, hr, hball⟩` from `Metric.nhds_basis_closedBall.mem_iff.1 (hS.mem_nhds hx)`. Establish `hSo : IsOpen ((Set.univ : Set ℝ) ×ˢ S)` using `isOpen_univ.prod hS`. Establish `hcU : ContinuousOn (Function.uncurry U) (Set.univ ×ˢ S)` using `hU.continuousOn`. Establish `hsl : ∀ y ∈ S, Continuous (fun t => U t y)` using `fun y hy => hcU.comp_continuous (f := fun t : ℝ => (t, y)) (by fun_prop) (fun t => ⟨Set.mem_univ _, hy⟩)`. Establish `hDc : ContinuousOn (fun p : ℝ × E => fderiv ℝ (U p.1) p.2) (Set.univ ×ˢ S)`.

Establish `h0 : ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry U)) (Set.univ ×ˢ S)` using `ContDiffOn.fderiv_of_isOpen hU hSo (by simp)`. Establish `h1 : ContinuousOn (fun p : ℝ × E => (fderiv ℝ (Function.uncurry U) p).comp (ContinuousLinearMap.inr ℝ ℝ E)) (Set.univ ×ˢ S)` using `h0.continuousOn.clm_comp continuousOn_const`. Use `h1.congr ?_` and prove the remaining obligations. Introduce and unpack `⟨t, y⟩ ⟨-, hy⟩`. Conclude with `(fderiv_slice hS hU hy).fderiv`.

Take `⟨T, hT⟩` from `hgc.isCompact.isBounded.subset_closedBall (0 : ℝ)`. Establish `hK : IsCompact (Metric.closedBall (0 : ℝ) T ×ˢ Metric.closedBall x r)` using `(isCompact_closedBall _ _).prod (isCompact_closedBall _ _)`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn (hDc.mono (Set.prod_mono (Set.subset_univ _) hball))`. Establish `hdiff : ∀ (t : ℝ) (y : E), y ∈ S → HasFDerivAt (U t) (fderiv ℝ (U t) y) y` using `fun t y hy => (fderiv_slice hS hU hy).differentiableAt.hasFDerivAt`. Establish `hcD : Continuous (fun t => fderiv ℝ (U t) x)` using `hDc.comp_continuous (f := fun t : ℝ => (t, x)) (by fun_prop) (fun t => ⟨Set.mem_univ _, hx⟩)`.

Establish `hIntD` using `int_real hg hgc hcD`. Establish `key : HasFDerivAt (fun x' => ∫ t, g t • U t x') (∫ t, g t • fderiv ℝ (U t) x) x`. Use `hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.closedBall x r) (F := fun x' t => g t • U t x') (F' := fun x' t => g t • fderiv ℝ (U t) x') (bound := fun t => |g t| * C) (Metric.closedBall_mem_nhds x hr) ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Use `filter_upwards [hS.mem_nhds hx] with y hy`. Conclude with `(int_real hg hgc (hsl y hy)).aestronglyMeasurable`.

Conclude with `int_real hg hgc (hsl x hx)`. Conclude with `hIntD.aestronglyMeasurable`. Use `Filter.Eventually.of_forall fun t y hy => ?_` and prove the remaining obligations. Distinguish the cases in `ht : t ∈ tsupport g`. Use `hC (t, y) ⟨hT ht, hy⟩` as an intermediate fact.

Rewrite using `[norm_smul, Real.norm_eq_abs]`. Conclude with `mul_le_mul_of_nonneg_left this (abs_nonneg _)`. Establish `hz : g t = 0` using `image_eq_zero_of_notMem_tsupport ht`. Simplify using `[hz]`. Establish `: Continuous (fun t => |g t| * C)` using `(continuous_abs.comp hg).mul continuous_const`.

Use `Continuous.integrable_of_hasCompactSupport this ?_` and prove the remaining obligations. Conclude with `(hgc.comp_left (g := fun a : ℝ => |a|) (by simp)).mul_right`. Use `Filter.Eventually.of_forall fun t y hy => ?_` and prove the remaining obligations. Conclude with `(hdiff t y (hball hy)).const_smul (g t)`. Rewrite using `[key.fderiv, ContinuousLinearMap.integral_apply hIntD]`.

Both sides reduce to the same expression.
-/
theorem gen_avg [ProperSpace E] [CompleteSpace W] {S : Set E} (hS : IsOpen S) {U : ℝ → E → W}
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ S)) {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {x : E} (hx : x ∈ S) (v : E) :
    fderiv ℝ (fun x' => ∫ t, g t • U t x') x v = ∫ t, g t • fderiv ℝ (U t) x v := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hS.mem_nhds hx)
  have hSo : IsOpen ((Set.univ : Set ℝ) ×ˢ S) := isOpen_univ.prod hS
  have hcU : ContinuousOn (Function.uncurry U) (Set.univ ×ˢ S) := hU.continuousOn
  have hsl : ∀ y ∈ S, Continuous (fun t => U t y) := fun y hy =>
    hcU.comp_continuous (f := fun t : ℝ => (t, y)) (by fun_prop) (fun t => ⟨Set.mem_univ _, hy⟩)
  have hDc : ContinuousOn (fun p : ℝ × E => fderiv ℝ (U p.1) p.2) (Set.univ ×ˢ S) := by
    have h0 : ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry U)) (Set.univ ×ˢ S) :=
      ContDiffOn.fderiv_of_isOpen hU hSo (by simp)
    have h1 : ContinuousOn (fun p : ℝ × E =>
        (fderiv ℝ (Function.uncurry U) p).comp (ContinuousLinearMap.inr ℝ ℝ E)) (Set.univ ×ˢ S) :=
      h0.continuousOn.clm_comp continuousOn_const
    refine h1.congr ?_
    rintro ⟨t, y⟩ ⟨-, hy⟩
    exact (fderiv_slice hS hU hy).fderiv
  obtain ⟨T, hT⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hK : IsCompact (Metric.closedBall (0 : ℝ) T ×ˢ Metric.closedBall x r) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hDc.mono (Set.prod_mono (Set.subset_univ _) hball))
  have hdiff : ∀ (t : ℝ) (y : E), y ∈ S → HasFDerivAt (U t) (fderiv ℝ (U t) y) y := fun t y hy =>
    (fderiv_slice hS hU hy).differentiableAt.hasFDerivAt
  have hcD : Continuous (fun t => fderiv ℝ (U t) x) :=
    hDc.comp_continuous (f := fun t : ℝ => (t, x)) (by fun_prop) (fun t => ⟨Set.mem_univ _, hx⟩)
  have hIntD := int_real hg hgc hcD
  have key : HasFDerivAt (fun x' => ∫ t, g t • U t x') (∫ t, g t • fderiv ℝ (U t) x) x := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.closedBall x r)
      (F := fun x' t => g t • U t x') (F' := fun x' t => g t • fderiv ℝ (U t) x')
      (bound := fun t => |g t| * C) (Metric.closedBall_mem_nhds x hr) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [hS.mem_nhds hx] with y hy
      exact (int_real hg hgc (hsl y hy)).aestronglyMeasurable
    · exact int_real hg hgc (hsl x hx)
    · exact hIntD.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t y hy => ?_
      by_cases ht : t ∈ tsupport g
      · have := hC (t, y) ⟨hT ht, hy⟩
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
      · have hz : g t = 0 := image_eq_zero_of_notMem_tsupport ht
        simp [hz]
    · have : Continuous (fun t => |g t| * C) := (continuous_abs.comp hg).mul continuous_const
      refine Continuous.integrable_of_hasCompactSupport this ?_
      exact (hgc.comp_left (g := fun a : ℝ => |a|) (by simp)).mul_right
    · refine Filter.Eventually.of_forall fun t y hy => ?_
      exact (hdiff t y (hball hy)).const_smul (g t)
  rw [key.fderiv, ContinuousLinearMap.integral_apply hIntD]
  rfl

end Gen

/- English proof (translation)
Establish `: (fun y : Mat n => y * X) = ((LinearMap.mulRight ℝ X : Mat n →ₗ[ℝ] Mat n).toContinuousLinearMap : Mat n → Mat n)`. Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `ContinuousLinearMap.contDiff _`.
-/
theorem contDiff_mulRight (X : Mat n) : ContDiff ℝ ∞ (fun y : Mat n => y * X) := by
  have : (fun y : Mat n => y * X) = ((LinearMap.mulRight ℝ X : Mat n →ₗ[ℝ] Mat n).toContinuousLinearMap : Mat n → Mat n) := by
    funext y; simp
  rw [this]
  exact ContinuousLinearMap.contDiff _

/- English proof (translation)
The claim follows from `gen_sm (isOpen_invertible_matrices n) hU (contDiff_mulRight X)`.
-/
theorem sm_Rd (X : Mat n) {U : ℝ → Mat n → V} (hU : Sm U) : Sm (fun t => Rd X (U t)) :=
  gen_sm (isOpen_invertible_matrices n) hU (contDiff_mulRight X)

/- English proof (translation)
Establish `h : ContinuousOn (Function.uncurry U) (Set.univ ×ˢ GLs n)` using `hU.continuousOn`. Conclude with `h.comp_continuous (f := fun t : ℝ => (t, x)) (by fun_prop) (fun t => ⟨Set.mem_univ _, hx⟩)`.
-/
theorem cont_slice {U : ℝ → Mat n → V} (hU : Sm U) {x : Mat n} (hx : x ∈ GLs n) :
    Continuous (fun t => U t x) := by
  have h : ContinuousOn (Function.uncurry U) (Set.univ ×ˢ GLs n) := hU.continuousOn
  exact h.comp_continuous (f := fun t : ℝ => (t, x)) (by fun_prop) (fun t => ⟨Set.mem_univ _, hx⟩)

/- English proof (translation)
Use `HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) |T|) ?_` and prove the remaining obligations. Introduce `t ht`. Use `hg.2.2 t (lt_of_le_of_lt (le_abs_self T) ?_)` and prove the remaining obligations. Simplify `ht` using `[Metric.mem_closedBall, Real.dist_eq]`.
-/
theorem bump_support {g : ℝ → ℝ} {T : ℝ} (hg : IsBump g T) : HasCompactSupport g := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) |T|) ?_
  intro t ht
  refine hg.2.2 t (lt_of_le_of_lt (le_abs_self T) ?_)
  simpa [Metric.mem_closedBall, Real.dist_eq] using ht

/- English proof (translation)
Simplify `int_real hg.1.continuous (bump_support hg) (cont_slice hU hx)` using `only [Complex.coe_smul]`.
-/
theorem int_sm {U : ℝ → Mat n → V} {g : ℝ → ℝ} {T : ℝ} (hU : Sm U) (hg : IsBump g T) {x : Mat n} (hx : x ∈ GLs n) :
    Integrable (fun t => (g t : ℂ) • U t x) := by
  simpa only [Complex.coe_smul] using int_real hg.1.continuous (bump_support hg) (cont_slice hU hx)

/- English proof (translation)
Use `haveI : ProperSpace (Mat n) := FiniteDimensional.proper ℝ _`. Simplify using `only [Complex.coe_smul]`. Conclude with `gen_avg (isOpen_invertible_matrices n) hU hg.1.continuous (bump_support hg) hx (x * X)`.
-/
theorem rd_avg [CompleteSpace V] (X : Mat n) {U : ℝ → Mat n → V} {g : ℝ → ℝ} {T : ℝ} (hU : Sm U) (hg : IsBump g T)
    {x : Mat n} (hx : x ∈ GLs n) :
    Rd X (fun x' => ∫ t, (g t : ℂ) • U t x') x = ∫ t, (g t : ℂ) • Rd X (U t) x := by
  haveI : ProperSpace (Mat n) := FiniteDimensional.proper ℝ _
  simp only [Complex.coe_smul]
  exact gen_avg (isOpen_invertible_matrices n) hU hg.1.continuous (bump_support hg) hx (x * X)

def Good (L : (Mat n → V) → (Mat n → V)) : Prop :=
  (∀ U : ℝ → Mat n → V, Sm U → Sm (fun t => L (U t))) ∧
  (∀ F F' : Mat n → V, (∀ y ∈ GLs n, F y = F' y) → ∀ x ∈ GLs n, L F x = L F' x) ∧
  ∀ (U : ℝ → Mat n → V) (g : ℝ → ℝ) (T : ℝ), Sm U → IsBump g T → ∀ x ∈ GLs n,
    L (fun x' => ∫ t, (g t : ℂ) • U t x') x = ∫ t, (g t : ℂ) • L (U t) x

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ h => h, fun _ _ h => h, fun _ _ _ _ _ _ _ => rfl⟩`.
-/
theorem good_id : Good (n := n) (V := V) (fun f => f) :=
  ⟨fun _ h => h, fun _ _ h => h, fun _ _ _ _ _ _ _ => rfl⟩

/- English proof (translation)
Use `⟨fun U _ => ?_, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => by simp⟩` and prove the remaining obligations. Conclude with `(contDiffOn_const (c := (0 : V))).congr (fun _ _ => rfl)`.
-/
theorem good_zero : Good (n := n) (V := V) (fun _ => 0) := by
  refine ⟨fun U _ => ?_, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => by simp⟩
  exact (contDiffOn_const (c := (0 : V))).congr (fun _ _ => rfl)

/- English proof (translation)
Use `⟨fun U hU => h₁.1 _ (h₂.1 U hU), fun F F' h => h₁.2.1 _ _ (h₂.2.1 F F' h), ?_⟩` and prove the remaining obligations. Introduce `U g T hU hg x hx`. Use `show L₁ (L₂ _) x = ∫ t, (g t : ℂ) • L₁ (L₂ (U t)) x`. Rewrite using `[h₁.2.1 _ (fun x' => ∫ t, (g t : ℂ) • L₂ (U t) x') (h₂.2.2 U g T hU hg) x hx]`. Conclude with `h₁.2.2 _ g T (h₂.1 U hU) hg x hx`.
-/
theorem good_comp {L₁ L₂ : (Mat n → V) → (Mat n → V)} (h₁ : Good L₁) (h₂ : Good L₂) :
    Good (fun f => L₁ (L₂ f)) := by
  refine ⟨fun U hU => h₁.1 _ (h₂.1 U hU), fun F F' h => h₁.2.1 _ _ (h₂.2.1 F F' h), ?_⟩
  intro U g T hU hg x hx
  show L₁ (L₂ _) x = ∫ t, (g t : ℂ) • L₁ (L₂ (U t)) x
  rw [h₁.2.1 _ (fun x' => ∫ t, (g t : ℂ) • L₂ (U t) x') (h₂.2.2 U g T hU hg) x hx]
  exact h₁.2.2 _ g T (h₂.1 U hU) hg x hx

/- English proof (translation)
Use `⟨fun U hU => ?_, fun F F' h x hx => ?_, ?_⟩` and prove the remaining obligations. Conclude with `((h₁.1 U hU).add (h₂.1 U hU)).congr (fun _ _ => rfl)`. Simplify using `only [Pi.add_apply, h₁.2.1 F F' h x hx, h₂.2.1 F F' h x hx]`. Introduce `U g T hU hg x hx`. Simplify using `only [Pi.add_apply, smul_add]`.

Rewrite using `[integral_add (int_sm (h₁.1 U hU) hg hx) (int_sm (h₂.1 U hU) hg hx), h₁.2.2 U g T hU hg x hx, h₂.2.2 U g T hU hg x hx]`.
-/
theorem good_add {L₁ L₂ : (Mat n → V) → (Mat n → V)} (h₁ : Good L₁) (h₂ : Good L₂) :
    Good (fun f => L₁ f + L₂ f) := by
  refine ⟨fun U hU => ?_, fun F F' h x hx => ?_, ?_⟩
  · exact ((h₁.1 U hU).add (h₂.1 U hU)).congr (fun _ _ => rfl)
  · simp only [Pi.add_apply, h₁.2.1 F F' h x hx, h₂.2.1 F F' h x hx]
  · intro U g T hU hg x hx
    simp only [Pi.add_apply, smul_add]
    rw [integral_add (int_sm (h₁.1 U hU) hg hx) (int_sm (h₂.1 U hU) hg hx),
      h₁.2.2 U g T hU hg x hx, h₂.2.2 U g T hU hg x hx]

/- English proof (translation)
Use `⟨fun U hU => ?_, fun F F' e x hx => ?_, ?_⟩` and prove the remaining obligations. Conclude with `((h.1 U hU).const_smul c).congr (fun _ _ => rfl)`. Simplify using `only [Pi.smul_apply, h.2.1 F F' e x hx]`. Introduce `U g T hU hg x hx`. Simplify using `only [Pi.smul_apply]`.

Rewrite using `[h.2.2 U g T hU hg x hx, ← integral_smul]`. Conclude with `integral_congr_ae (Filter.Eventually.of_forall fun t => smul_comm _ _ _)`.
-/
theorem good_smul (c : ℂ) {L : (Mat n → V) → (Mat n → V)} (h : Good L) : Good (fun f => c • L f) := by
  refine ⟨fun U hU => ?_, fun F F' e x hx => ?_, ?_⟩
  · exact ((h.1 U hU).const_smul c).congr (fun _ _ => rfl)
  · simp only [Pi.smul_apply, h.2.1 F F' e x hx]
  · intro U g T hU hg x hx
    simp only [Pi.smul_apply]
    rw [h.2.2 U g T hU hg x hx, ← integral_smul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => smul_comm _ _ _)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using good_zero`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.sum_insert ha]`. Conclude with `good_add (h a) ih`.
-/
theorem good_sum {ι : Type} (s : Finset ι) {L : ι → (Mat n → V) → (Mat n → V)} (h : ∀ i, Good (L i)) :
    Good (fun f => ∑ i ∈ s, L i f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact good_add (h a) ih

/- English proof (translation)
Use `⟨fun U hU => sm_Rd X hU, fun F F' h x hx => ?_, fun U g T hU hg x hx => rd_avg X hU hg hx⟩` and prove the remaining obligations. Establish `he : F =ᶠ[𝓝 x] F'` using `Filter.eventuallyEq_of_mem ((isOpen_invertible_matrices n).mem_nhds hx) h`. Use `show fderiv ℝ F x (x * X) = fderiv ℝ F' x (x * X)`. Rewrite using `[he.fderiv_eq]`.
-/
theorem good_Rd [CompleteSpace V] (X : Mat n) : Good (n := n) (V := V) (Rd X) := by
  refine ⟨fun U hU => sm_Rd X hU, fun F F' h x hx => ?_, fun U g T hU hg x hx => rd_avg X hU hg hx⟩
  have he : F =ᶠ[𝓝 x] F' := Filter.eventuallyEq_of_mem ((isOpen_invertible_matrices n).mem_nhds hx) h
  show fderiv ℝ F x (x * X) = fderiv ℝ F' x (x * X)
  rw [he.fderiv_eq]

/- English proof (translation)
The claim follows from `good_smul _ (good_add (good_Rd _) (good_smul _ (good_Rd _)))`.
-/
theorem good_Eu [CompleteSpace V] (s : Bool) (a b : Fin n) : Good (n := n) (V := V) (Eu s a b) :=
  good_smul _ (good_add (good_Rd _) (good_smul _ (good_Rd _)))

/- English proof (translation)
Proceed by induction on `m generalizing a b with`. Consider the case `zero`. Distinguish the cases in `h : a = b`. Simplify `good_id` using `[Epow, h]`. Simplify `good_zero` using `[Epow, h]`.

Consider the case `succ m ih`. Conclude with `good_sum Finset.univ fun c => good_comp (good_Eu s a c) (ih c b)`.
-/
theorem good_Epow [CompleteSpace V] (s : Bool) (m : ℕ) (a b : Fin n) : Good (n := n) (V := V) (Epow s m a b) := by
  induction m generalizing a b with
  | zero =>
    by_cases h : a = b
    · simpa [Epow, h] using good_id
    · simpa [Epow, h] using good_zero
  | succ m ih =>
    exact good_sum Finset.univ fun c => good_comp (good_Eu s a c) (ih c b)

/- English proof (translation)
The claim follows from `good_sum Finset.univ fun a => good_Epow s m a a`.
-/
theorem good_gel [CompleteSpace V] (s : Bool) (m : ℕ) : Good (n := n) (V := V) (gel s m) :=
  good_sum Finset.univ fun a => good_Epow s m a a

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact good_id`. Consider the case `cons p w ih => show Good (fun f => gel p.1 p.2 (zOp w f))`. Conclude with `good_comp (good_gel p.1 p.2) ih`.
-/
theorem good_zOp [CompleteSpace V] (w : List (Bool × ℕ)) : Good (n := n) (V := V) (zOp w) := by
  induction w with
  | nil => exact good_id
  | cons p w ih =>
    show Good (fun f => gel p.1 p.2 (zOp w f))
    exact good_comp (good_gel p.1 p.2) ih

/- English proof (translation)
Introduce `_ _ _ _ _ U g T w hU hg x hx` and use `(good_zOp w).2.2 U g T hU hg x hx`.
-/
theorem zOp_avg : ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (U : ℝ → Mat n → V)
    (g : ℝ → ℝ) (T : ℝ) (w : List (Bool × ℕ)), ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n) → IsBump g T →
    ∀ x ∈ GLs n, zOp w (fun x' => ∫ t, (g t : ℂ) • U t x') x = ∫ t, (g t : ℂ) • zOp w (U t) x :=
  fun _ _ _ _ _ U g T w hU hg x hx => (good_zOp w).2.2 U g T hU hg x hx

end GlobalTheory.CompanionTheory.WaveMult.ZOpAvg
