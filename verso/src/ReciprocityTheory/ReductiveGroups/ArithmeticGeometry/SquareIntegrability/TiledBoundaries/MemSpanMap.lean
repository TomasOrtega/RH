import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.MemSpanBn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.TileIntegral

namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries

open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory MeasureTheory.Measure Complex Module Set Submodule

noncomputable section

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `h : range (b.map e) = ((e.restrictScalars ℤ : V ≃ₗ[ℤ] V) : V →ₗ[ℤ] V) '' range b`. Use extensionality with `y`. Simplify using `[Basis.map_apply]`. Rewrite using `[h, Submodule.span_image, Submodule.mem_map_equiv]`. Apply the tactic sequence `try rfl`.
-/
theorem mem_span_map {V : Type} [AddCommGroup V] [Module ℝ V] {ι : Type} (b : Basis ι ℝ V)
    (e : V ≃ₗ[ℝ] V) (x : V) : x ∈ span ℤ (range (b.map e)) ↔ e.symm x ∈ span ℤ (range b) := by
  have h : range (b.map e) = ((e.restrictScalars ℤ : V ≃ₗ[ℤ] V) : V →ₗ[ℤ] V) '' range b := by
    ext y
    simp [Basis.map_apply]
  rw [h, Submodule.span_image, Submodule.mem_map_equiv]
  try rfl

section PiR

def piR (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) : Vsp X.dim ≃ₗ[ℝ] Vsp X.dim :=
  LinearEquiv.ofBijective (π.restrictScalars ℝ) (pi_bij X hq hπ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem piR_apply (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) (v : Vsp X.dim) : piR X hq hπ v = π v := rfl

def bP (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) : Basis (Fin (2 * Fintype.card (Idx X.dim))) ℝ (Vsp X.dim) := X.b.map (piR X hq hπ).symm

/- English proof (translation)
Unfold `bP`. Conclude with `(mem_span_map _ _ _).trans Iff.rfl`.
-/
theorem mem_P (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) (x : Vsp X.dim) : x ∈ span ℤ (range (bP X hq hπ)) ↔ π x ∈ X.L := by
  unfold bP
  exact (mem_span_map _ _ _).trans Iff.rfl

/- English proof (translation)
Introduce `x hx` and use `(mem_P X hq hπ x).mpr (hπ.2.1 x hx)`.
-/
theorem L_le_P (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) : span ℤ (range X.b) ≤ span ℤ (range (bP X hq hπ)) := fun x hx => (mem_P X hq hπ x).mpr (hπ.2.1 x hx)

/- English proof (translation)
Unfold `bP`. Rewrite using `[← ZSpan.map_fundamentalDomain, LinearEquiv.image_symm_eq_preimage]`. Apply the tactic sequence `try rfl`.
-/
theorem fdP (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) : ZSpan.fundamentalDomain (bP X hq hπ) = piR X hq hπ ⁻¹' ZSpan.fundamentalDomain X.b := by
  unfold bP
  rw [← ZSpan.map_fundamentalDomain, LinearEquiv.image_symm_eq_preimage]
  try rfl

/- English proof (translation)
Establish `hn : ∀ v : Vsp X.dim, Hf v v = @inner ℂ _ _ v v` using `fun v => by`. Simplify using `only [Hf, PiLp.inner_apply, RCLike.inner_apply, mul_comm]`. Establish `h` using `hπ.2.2.1 x x`. Rewrite `h` using `[hn, hn, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]`. Establish `h2 : ‖π x‖ ^ 2 = (q : ℝ) * ‖x‖ ^ 2`.

Establish `h' : ((‖π x‖ ^ 2 : ℝ) : ℂ) = (((q : ℝ) * ‖x‖ ^ 2 : ℝ) : ℂ)` using `by push_cast; exact h`. Conclude with `Complex.ofReal_injective h'`. Rewrite using `[← Real.sqrt_sq (norm_nonneg (π x)), h2, Real.sqrt_mul (Nat.cast_nonneg q), Real.sqrt_sq (norm_nonneg x)]`.
-/
theorem norm_pi (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hπ : IsPi X q π) (x : Vsp X.dim) : ‖π x‖ = Real.sqrt q * ‖x‖ := by
  have hn : ∀ v : Vsp X.dim, Hf v v = @inner ℂ _ _ v v := fun v => by
    simp only [Hf, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have h := hπ.2.2.1 x x
  rw [hn, hn, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖π x‖ ^ 2 = (q : ℝ) * ‖x‖ ^ 2 := by
    have h' : ((‖π x‖ ^ 2 : ℝ) : ℂ) = (((q : ℝ) * ‖x‖ ^ 2 : ℝ) : ℂ) := by push_cast; exact h
    exact Complex.ofReal_injective h'
  rw [← Real.sqrt_sq (norm_nonneg (π x)), h2, Real.sqrt_mul (Nat.cast_nonneg q), Real.sqrt_sq (norm_nonneg x)]

/- English proof (translation)
The claim follows from `Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))`.
-/
theorem sqrt_q_pos {q : ℕ} (hq : 1 ≤ q) : 0 < Real.sqrt q := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))

def Ui (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) : Vsp X.dim ≃ₗᵢ[ℝ] Vsp X.dim where
  toLinearEquiv := (piR X hq hπ).trans
    (LinearEquiv.smulOfNeZero ℝ _ (Real.sqrt q)⁻¹ (inv_ne_zero (sqrt_q_pos hq).ne'))
  norm_map' x := by
    show ‖(Real.sqrt q)⁻¹ • π x‖ = ‖x‖
    rw [norm_smul, norm_pi X hπ, Real.norm_eq_abs, abs_inv, abs_of_pos (sqrt_q_pos hq), ← mul_assoc,
      inv_mul_cancel₀ (sqrt_q_pos hq).ne', one_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Ui_apply (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) (x : Vsp X.dim) : Ui X hq hπ x = (Real.sqrt q)⁻¹ • π x := rfl

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Ui_apply, piR_apply, smul_smul, mul_inv_cancel₀ (sqrt_q_pos hq).ne', one_smul]`.
-/
theorem piR_preimage (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) (S : Set (Vsp X.dim)) :
    piR X hq hπ ⁻¹' S = Ui X hq hπ ⁻¹' ((fun x => Real.sqrt q • x) ⁻¹' S) := by
  ext x
  simp only [Set.mem_preimage, Ui_apply, piR_apply, smul_smul, mul_inv_cancel₀ (sqrt_q_pos hq).ne', one_smul]

/- English proof (translation)
Rewrite using `[Module.finrank_eq_card_basis X.b, Fintype.card_fin]`.
-/
theorem finrank_V (X : PT E) : finrank ℝ (Vsp X.dim) = 2 * Fintype.card (Idx X.dim) := by
  rw [Module.finrank_eq_card_basis X.b, Fintype.card_fin]

/- English proof (translation)
Establish `hmeas : MeasurableSet ((fun x => Real.sqrt q • x) ⁻¹' ZSpan.fundamentalDomain X.b)` using `(ZSpan.fundamentalDomain_measurableSet X.b).preimage (measurable_const_smul _)`. Rewrite using `[fdP, piR_preimage, measureReal_def, ((Ui X hq hπ).measurePreserving).measure_preimage hmeas.nullMeasurableSet, Measure.addHaar_preimage_smul volume (sqrt_q_pos hq).ne', finrank_V, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), measureReal_def]`. Use `congr 1`. Rewrite using `[abs_inv, pow_mul, Real.sq_sqrt (Nat.cast_nonneg q), abs_of_pos (pow_pos (Nat.cast_pos.mpr (by omega)) _)]`.
-/
theorem vol_fdP (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) : volume.real (ZSpan.fundamentalDomain (bP X hq hπ)) =
    ((q : ℝ) ^ Fintype.card (Idx X.dim))⁻¹ * volume.real (ZSpan.fundamentalDomain X.b) := by
  have hmeas : MeasurableSet ((fun x => Real.sqrt q • x) ⁻¹' ZSpan.fundamentalDomain X.b) :=
    (ZSpan.fundamentalDomain_measurableSet X.b).preimage (measurable_const_smul _)
  rw [fdP, piR_preimage, measureReal_def,
    ((Ui X hq hπ).measurePreserving).measure_preimage hmeas.nullMeasurableSet,
    Measure.addHaar_preimage_smul volume (sqrt_q_pos hq).ne', finrank_V, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), measureReal_def]
  congr 1
  rw [abs_inv, pow_mul, Real.sq_sqrt (Nat.cast_nonneg q),
    abs_of_pos (pow_pos (Nat.cast_pos.mpr (by omega)) _)]

end PiR

/- English proof (translation)
Establish `hdet : LinearMap.det (f : Vsp X.dim →ₗ[ℝ] Vsp X.dim) ≠ 0` using `(LinearEquiv.isUnit_det' f).ne_zero`. Establish `hmap : Measure.map f volume = ENNReal.ofReal |(LinearMap.det (f : Vsp X.dim →ₗ[ℝ] Vsp X.dim))⁻¹| • (volume : Measure (Vsp X.dim))` using `Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet`. Establish `hfm : Measurable f` using `(LinearMap.continuous_of_finiteDimensional (f : Vsp X.dim →ₗ[ℝ] Vsp X.dim)).measurable`. Establish `h1 : ∫ x in f ⁻¹' S, g (f x) ∂volume = ∫ x in S, g x ∂(Measure.map f volume)` using `(setIntegral_map hS hg.aestronglyMeasurable hfm.aemeasurable).symm`. Establish `h2 : volume (f ⁻¹' S) = (Measure.map f volume) S` using `(Measure.map_apply hfm hS).symm`.

Establish `hc0 : (ENNReal.ofReal |(LinearMap.det (f : Vsp X.dim →ₗ[ℝ] Vsp X.dim))⁻¹|).toReal ≠ 0`. Rewrite using `[ENNReal.toReal_ofReal (abs_nonneg _)]`. Conclude with `abs_ne_zero.mpr (inv_ne_zero hdet)`. Rewrite using `[setAverage_eq, setAverage_eq, h1, measureReal_def, h2, hmap, Measure.restrict_smul, integral_smul_measure, Measure.smul_apply, smul_eq_mul (α := ENNReal), ENNReal.toReal_mul, ← measureReal_def]`. Simplify using `only [smul_eq_mul, mul_inv]`.

Take the linear combination `((volume.real S)⁻¹ * ∫ x in S, g x) * inv_mul_cancel₀ hc0`.
-/
private theorem setAverage_preimage_linearEquiv_comp (X : PT E) (f : Vsp X.dim ≃ₗ[ℝ] Vsp X.dim) (g : Vsp X.dim → ℝ)
    (hg : Continuous g) (S : Set (Vsp X.dim)) (hS : MeasurableSet S) :
    ⨍ x in f ⁻¹' S, g (f x) ∂(volume : Measure (Vsp X.dim)) = ⨍ x in S, g x ∂volume := by
  have hdet : LinearMap.det (f : Vsp X.dim →ₗ[ℝ] Vsp X.dim) ≠ 0 := (LinearEquiv.isUnit_det' f).ne_zero
  have hmap : Measure.map f volume = ENNReal.ofReal |(LinearMap.det (f : Vsp X.dim →ₗ[ℝ] Vsp X.dim))⁻¹| •
      (volume : Measure (Vsp X.dim)) :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet
  have hfm : Measurable f := (LinearMap.continuous_of_finiteDimensional (f : Vsp X.dim →ₗ[ℝ] Vsp X.dim)).measurable
  have h1 : ∫ x in f ⁻¹' S, g (f x) ∂volume = ∫ x in S, g x ∂(Measure.map f volume) :=
    (setIntegral_map hS hg.aestronglyMeasurable hfm.aemeasurable).symm
  have h2 : volume (f ⁻¹' S) = (Measure.map f volume) S := (Measure.map_apply hfm hS).symm
  have hc0 : (ENNReal.ofReal |(LinearMap.det (f : Vsp X.dim →ₗ[ℝ] Vsp X.dim))⁻¹|).toReal ≠ 0 := by
    rw [ENNReal.toReal_ofReal (abs_nonneg _)]
    exact abs_ne_zero.mpr (inv_ne_zero hdet)
  rw [setAverage_eq, setAverage_eq, h1, measureReal_def, h2, hmap, Measure.restrict_smul, integral_smul_measure,
    Measure.smul_apply, smul_eq_mul (α := ENNReal), ENNReal.toReal_mul, ← measureReal_def]
  simp only [smul_eq_mul, mul_inv]
  linear_combination ((volume.real S)⁻¹ * ∫ x in S, g x) * inv_mul_cancel₀ hc0

/- English proof (translation)
Introduce `E _ _ X q π hq hπ g hg hper`. Establish `hgp : Continuous fun w => g (π w)` using `hg.comp (LinearMap.continuous_of_finiteDimensional π)`. Rewrite using `[tile_average (μ := volume) X.b (bP X hq hπ) (L_le_P X hq hπ) (fun w => g (π w)) hgp ?_]`. Rewrite using `[fdP]`. Conclude with `setAverage_preimage_linearEquiv_comp X (piR X hq hπ) g hg _ (ZSpan.fundamentalDomain_measurableSet X.b)`.

Introduce `β hβ x`. Establish `h1` using `(mem_P X hq hπ β).mp hβ`. Simplify using `only [map_add]`. Conclude with `hper _ h1 _`.
-/
theorem stepP : StepP := by
  intro E _ _ X q π hq hπ g hg hper
  have hgp : Continuous fun w => g (π w) := hg.comp (LinearMap.continuous_of_finiteDimensional π)
  rw [tile_average (μ := volume) X.b (bP X hq hπ) (L_le_P X hq hπ) (fun w => g (π w)) hgp ?_]
  · rw [fdP]
    exact setAverage_preimage_linearEquiv_comp X (piR X hq hπ) g hg _ (ZSpan.fundamentalDomain_measurableSet X.b)
  · intro β hβ x
    have h1 := (mem_P X hq hπ β).mp hβ
    simp only [map_add]
    exact hper _ h1 _

section Q

/- English proof (translation)
Conclude with `Nat.cast_ne_zero.mpr (by omega)`.
-/
theorem q_ne {q : ℕ} (hq : 1 ≤ q) : (q : ℝ) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr (by omega)

def bQ (X : PT E) {q : ℕ} (hq : 1 ≤ q) : Basis (Fin (2 * Fintype.card (Idx X.dim))) ℝ (Vsp X.dim) :=
  X.b.map (LinearEquiv.smulOfNeZero ℝ _ (q : ℝ) (q_ne hq)).symm

/- English proof (translation)
Unfold `bQ`. Conclude with `(mem_span_map _ _ _).trans Iff.rfl`.
-/
theorem mem_Q (X : PT E) {q : ℕ} (hq : 1 ≤ q) (x : Vsp X.dim) : x ∈ span ℤ (range (bQ X hq)) ↔ (q : ℝ) • x ∈ X.L := by
  unfold bQ
  exact (mem_span_map _ _ _).trans Iff.rfl

/- English proof (translation)
Unfold `bQ`. Rewrite using `[← ZSpan.map_fundamentalDomain, LinearEquiv.image_symm_eq_preimage]`. Apply the tactic sequence `try rfl`.
-/
theorem fdQ (X : PT E) {q : ℕ} (hq : 1 ≤ q) : ZSpan.fundamentalDomain (bQ X hq) =
    (fun x => (q : ℝ) • x) ⁻¹' ZSpan.fundamentalDomain X.b := by
  unfold bQ
  rw [← ZSpan.map_fundamentalDomain, LinearEquiv.image_symm_eq_preimage]
  try rfl

/- English proof (translation)
Rewrite using `[fdQ, measureReal_def, Measure.addHaar_preimage_smul volume (q_ne hq), finrank_V, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), measureReal_def]`. Use `congr 1`. Rewrite using `[abs_inv, abs_of_pos (pow_pos (Nat.cast_pos.mpr (by omega)) _)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vol_fdQ (X : PT E) {q : ℕ} (hq : 1 ≤ q) : volume.real (ZSpan.fundamentalDomain (bQ X hq)) =
    (((q : ℝ) ^ Fintype.card (Idx X.dim)) ^ 2)⁻¹ * volume.real (ZSpan.fundamentalDomain X.b) := by
  rw [fdQ, measureReal_def, Measure.addHaar_preimage_smul volume (q_ne hq), finrank_V, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), measureReal_def]
  congr 1
  rw [abs_inv, abs_of_pos (pow_pos (Nat.cast_pos.mpr (by omega)) _)]
  ring

end Q

/- English proof (translation)
Introduce `x hx`. Rewrite `hx` using `[mem_P]`. Rewrite using `[mem_Q]`. Establish `hH : ∀ a c : Vsp X.dim, Hf a c = @inner ℂ _ _ c a` using `fun a c => by`. Simplify using `only [Hf, PiLp.inner_apply, RCLike.inner_apply, mul_comm]`.

Establish `hround : ∀ y : Vsp X.dim, y ∈ X.L → ((round (Hf (π x) (π y)).im : ℤ) : ℝ) = (Hf (π x) (π y)).im`. Introduce `y hy`. Take `⟨k, hk⟩` from `X.integral _ _ hx (hπ.2.1 y hy)`. Rewrite using `[hk, round_intCast]`. Establish `hadd : ∀ y1 y2 : Vsp X.dim, (Hf (π x) (π (y1 + y2))).im = (Hf (π x) (π y1)).im + (Hf (π x) (π y2)).im`.

Introduce `y1 y2`. Rewrite using `[hH, hH, hH, map_add, inner_add_left, Complex.add_im]`. Set `φ : X.L →+ ℤ` to `{ toFun := fun y => round (Hf (π x) (π y)).im map_zero' := by simp [hH] map_add' := fun y1 y2 => by`. Apply `Int.cast_injective (α := ℝ)` to reduce the goal to its premises. Simplify using `only [Submodule.coe_add, Int.cast_add]`.

Rewrite using `[hround _ (X.L.add_mem y1.2 y2.2), hround _ y1.2, hround _ y2.2]`. Conclude with `hadd _ _ }`. Take `⟨w, hwL, hw⟩` from `X.perfect φ`. Establish `hLu : ∀ y ∈ X.L, (@inner ℂ _ _ y (w - (q : ℝ) • x)).im = 0`. Introduce `y hy`.

Establish `h1` using `hw ⟨y, hy⟩`. Establish `h2` using `hπ.2.2.1 x y`. Simplify using `only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h1`. Rewrite `h1` using `[hround _ hy, h2, hH, hH]`. Rewrite using `[inner_sub_right, ← Complex.coe_smul, inner_smul_right, Complex.sub_im, ← h1]`.

Simplify using the standard rewrite rules. Set `Lf : Vsp X.dim →ₗ[ℝ] ℝ` to `Complex.imLm.comp ((innerₛₗ ℂ (w - (q : ℝ) • x)).restrictScalars ℝ)`. Establish `hLf : Lf = 0` using `X.b.ext fun i => by`. Establish `h` using `hLu _ (Submodule.subset_span (Set.mem_range_self i))`. Rewrite `h` using `[← inner_conj_symm, Complex.conj_im, neg_eq_zero]`.

Simplify `h` using `[Lf, inner_sub_left]`. Establish `hall : ∀ y, (@inner ℂ _ _ (w - (q : ℝ) • x) y).im = 0` using `fun y => by`. Conclude with `LinearMap.congr_fun hLf y`. Establish `hu0 : w - (q : ℝ) • x = 0`. Establish `h1` using `hall (Complex.I • (w - (q : ℝ) • x))`.

Rewrite `h1` using `[inner_smul_right]`. Simplify using `only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] at h1`. Establish `h2 : ‖w - (q : ℝ) • x‖ ^ 2 = 0`. Rewrite using `[← inner_self_eq_norm_sq (𝕜 := ℂ)]`. Conclude with `h1`.

Conclude with `norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)`. Rewrite using `[← sub_eq_zero.mp hu0]`. Conclude with `hwL`.
-/
theorem P_le_Q (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) :
    span ℤ (range (bP X hq hπ)) ≤ span ℤ (range (bQ X hq)) := by
  intro x hx
  rw [mem_P] at hx
  rw [mem_Q]
  have hH : ∀ a c : Vsp X.dim, Hf a c = @inner ℂ _ _ c a := fun a c => by
    simp only [Hf, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hround : ∀ y : Vsp X.dim, y ∈ X.L →
      ((round (Hf (π x) (π y)).im : ℤ) : ℝ) = (Hf (π x) (π y)).im := by
    intro y hy
    obtain ⟨k, hk⟩ := X.integral _ _ hx (hπ.2.1 y hy)
    rw [hk, round_intCast]
  have hadd : ∀ y1 y2 : Vsp X.dim,
      (Hf (π x) (π (y1 + y2))).im = (Hf (π x) (π y1)).im + (Hf (π x) (π y2)).im := by
    intro y1 y2
    rw [hH, hH, hH, map_add, inner_add_left, Complex.add_im]
  let φ : X.L →+ ℤ :=
    { toFun := fun y => round (Hf (π x) (π y)).im
      map_zero' := by simp [hH]
      map_add' := fun y1 y2 => by
        apply Int.cast_injective (α := ℝ)
        simp only [Submodule.coe_add, Int.cast_add]
        rw [hround _ (X.L.add_mem y1.2 y2.2), hround _ y1.2, hround _ y2.2]
        exact hadd _ _ }
  obtain ⟨w, hwL, hw⟩ := X.perfect φ
  have hLu : ∀ y ∈ X.L, (@inner ℂ _ _ y (w - (q : ℝ) • x)).im = 0 := by
    intro y hy
    have h1 := hw ⟨y, hy⟩
    have h2 := hπ.2.2.1 x y
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h1
    rw [hround _ hy, h2, hH, hH] at h1
    rw [inner_sub_right, ← Complex.coe_smul, inner_smul_right, Complex.sub_im, ← h1]
    simp
  let Lf : Vsp X.dim →ₗ[ℝ] ℝ := Complex.imLm.comp ((innerₛₗ ℂ (w - (q : ℝ) • x)).restrictScalars ℝ)
  have hLf : Lf = 0 := X.b.ext fun i => by
    have h := hLu _ (Submodule.subset_span (Set.mem_range_self i))
    rw [← inner_conj_symm, Complex.conj_im, neg_eq_zero] at h
    simpa [Lf, inner_sub_left] using h
  have hall : ∀ y, (@inner ℂ _ _ (w - (q : ℝ) • x) y).im = 0 := fun y => by
    exact LinearMap.congr_fun hLf y
  have hu0 : w - (q : ℝ) • x = 0 := by
    have h1 := hall (Complex.I • (w - (q : ℝ) • x))
    rw [inner_smul_right] at h1
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] at h1
    have h2 : ‖w - (q : ℝ) • x‖ ^ 2 = 0 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
      exact h1
    exact norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)
  rw [← sub_eq_zero.mp hu0]
  exact hwL

/- English proof (translation)
Introduce `E _ _ X q n π hq hπ K hK`. Establish `hq0 : (q : ℝ) ≠ 0` using `q_ne hq`. Establish `hQ : (0 : ℝ) < (q : ℝ) ^ Fintype.card (Idx X.dim)` using `pow_pos (Nat.cast_pos.mpr (by omega)) _`. Establish `hQ' : (q : ℝ) ^ Fintype.card (Idx X.dim) ≠ 0` using `hQ.ne'`. Establish `hV : 0 < volume.real (ZSpan.fundamentalDomain X.b)`.

Rewrite using `[measureReal_def]`. Conclude with `ENNReal.toReal_pos (ZSpan.measure_fundamentalDomain_ne_zero X.b) (ZSpan.fundamentalDomain_isBounded X.b).measure_lt_top.ne`. Establish `ht` using `tile_measure (μ := volume) (bP X hq hπ) (bQ X hq) (P_le_Q X hq hπ)`. Rewrite `ht` using `[vol_fdP, vol_fdQ]`. Establish `hcR : ((reps (bP X hq hπ) (bQ X hq)).card : ℝ) = (q : ℝ) ^ Fintype.card (Idx X.dim)`.

Establish `h3 : ((reps (bP X hq hπ) (bQ X hq)).card : ℝ) * ((((q : ℝ) ^ Fintype.card (Idx X.dim)) ^ 2)⁻¹ * volume.real (ZSpan.fundamentalDomain X.b)) = ((q : ℝ) ^ Fintype.card (Idx X.dim)) * ((((q : ℝ) ^ Fintype.card (Idx X.dim)) ^ 2)⁻¹ * volume.real (ZSpan.fundamentalDomain X.b))`. Rewrite using `[← ht]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Conclude with `mul_right_cancel₀ (mul_pos (inv_pos.mpr (pow_pos hQ 2)) hV).ne' h3`.

Establish `hcR' : (reps (bP X hq hπ) (bQ X hq)).card = q ^ Fintype.card (Idx X.dim)` using `by exact_mod_cast hcR`. Establish `hmemQ : ∀ c ∈ reps (bP X hq hπ) (bQ X hq), (q : ℂ) • c ∈ X.L`. Introduce `c hc`. Establish `h1` using `(mem_Q X hq c).mp (mem_reps.mp hc).2`. Rewrite `h1` using `[Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℂ]`. Then use the resulting hypothesis.

Set `T` to `Fintype.piFinset (fun _ : Fin n => reps (bP X hq hπ) (bQ X hq))`. Establish `hT : ∀ c ∈ T, ∀ k, (q : ℂ) • c k ∈ X.L` using `fun c hc k => hmemQ _ (Fintype.mem_piFinset.mp hc k)`. Set `f : (Fin n → Vsp X.dim) → (Fin n → Vsp X.dim)` to `fun c => if h : ∀ k, (q : ℂ) • c k ∈ X.L then Classical.choose (hK.2 c h).exists else 0`. Establish `hf : ∀ c ∈ T, f c ∈ K ∧ ∀ k, π (c k - f c k) ∈ X.L`. Introduce `c hc`.

Establish `h` using `hT c hc`. Simplify using `only [f, dif_pos h]`. Conclude with `Classical.choose_spec (hK.2 c h).exists`. Establish `hcard : T.card ≤ K.card`. Apply `Finset.card_le_card_of_injOn f` to reduce the goal to its premises.

Introduce `c hc`. Apply the tactic sequence `have hc' : c ∈ T := by first | exact hc | exact Finset.mem_coe.mp hc`. Conclude with `(hf c hc').1`. Introduce `c1 hc1 c2 hc2 heq`. Apply the tactic sequence `have hc1' : c1 ∈ T := by first | exact hc1 | exact Finset.mem_coe.mp hc1`.

Apply the tactic sequence `have hc2' : c2 ∈ T := by first | exact hc2 | exact Finset.mem_coe.mp hc2`. Use function extensionality and compare the values at `k`. Establish `e1` using `(hf c1 hc1').2 k`. Establish `e2` using `(hf c2 hc2').2 k`. Rewrite `e1` using `[heq]`.

Establish `e3 : π (c1 k - c2 k) ∈ X.L`. Establish `h4` using `X.L.sub_mem e1 e2`. Rewrite `h4` using `[← map_sub, sub_sub_sub_cancel_right]`. Then use the resulting hypothesis. Establish `hP` using `(mem_P X hq hπ _).mpr e3`. Establish `hc1k` using `(mem_reps.mp (Fintype.mem_piFinset.mp hc1' k)).1`.

Establish `hc2k` using `(mem_reps.mp (Fintype.mem_piFinset.mp hc2' k)).1`. Establish `h5` using `fd_uniq (bP X hq hπ) (x := c2 k) hP (Submodule.zero_mem _) (by rw [sub_add_cancel]; exact hc1k) (by rw [zero_add]; exact hc2k)`. Conclude with `sub_eq_zero.mp h5`. Establish `hTc : T.card = q ^ (Fintype.card (Idx X.dim) * n)`. Simplify using `only [T, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hcR', pow_mul]`.

Rewrite using `[← hTc]`. Conclude with `hcard`.
-/
theorem stepK : StepK := by
  intro E _ _ X q n π hq hπ K hK
  have hq0 : (q : ℝ) ≠ 0 := q_ne hq
  have hQ : (0 : ℝ) < (q : ℝ) ^ Fintype.card (Idx X.dim) := pow_pos (Nat.cast_pos.mpr (by omega)) _
  have hQ' : (q : ℝ) ^ Fintype.card (Idx X.dim) ≠ 0 := hQ.ne'
  have hV : 0 < volume.real (ZSpan.fundamentalDomain X.b) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (ZSpan.measure_fundamentalDomain_ne_zero X.b)
      (ZSpan.fundamentalDomain_isBounded X.b).measure_lt_top.ne
  have ht := tile_measure (μ := volume) (bP X hq hπ) (bQ X hq) (P_le_Q X hq hπ)
  rw [vol_fdP, vol_fdQ] at ht
  have hcR : ((reps (bP X hq hπ) (bQ X hq)).card : ℝ) = (q : ℝ) ^ Fintype.card (Idx X.dim) := by
    have h3 : ((reps (bP X hq hπ) (bQ X hq)).card : ℝ) *
        ((((q : ℝ) ^ Fintype.card (Idx X.dim)) ^ 2)⁻¹ * volume.real (ZSpan.fundamentalDomain X.b)) =
        ((q : ℝ) ^ Fintype.card (Idx X.dim)) *
        ((((q : ℝ) ^ Fintype.card (Idx X.dim)) ^ 2)⁻¹ * volume.real (ZSpan.fundamentalDomain X.b)) := by
      rw [← ht]
      field_simp
      try ring
    exact mul_right_cancel₀ (mul_pos (inv_pos.mpr (pow_pos hQ 2)) hV).ne' h3
  have hcR' : (reps (bP X hq hπ) (bQ X hq)).card = q ^ Fintype.card (Idx X.dim) := by exact_mod_cast hcR
  have hmemQ : ∀ c ∈ reps (bP X hq hπ) (bQ X hq), (q : ℂ) • c ∈ X.L := by
    intro c hc
    have h1 := (mem_Q X hq c).mp (mem_reps.mp hc).2
    rwa [Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℂ] at h1
  classical
  let T := Fintype.piFinset (fun _ : Fin n => reps (bP X hq hπ) (bQ X hq))
  have hT : ∀ c ∈ T, ∀ k, (q : ℂ) • c k ∈ X.L := fun c hc k =>
    hmemQ _ (Fintype.mem_piFinset.mp hc k)
  let f : (Fin n → Vsp X.dim) → (Fin n → Vsp X.dim) := fun c =>
    if h : ∀ k, (q : ℂ) • c k ∈ X.L then Classical.choose (hK.2 c h).exists else 0
  have hf : ∀ c ∈ T, f c ∈ K ∧ ∀ k, π (c k - f c k) ∈ X.L := by
    intro c hc
    have h := hT c hc
    simp only [f, dif_pos h]
    exact Classical.choose_spec (hK.2 c h).exists
  have hcard : T.card ≤ K.card := by
    apply Finset.card_le_card_of_injOn f
    · intro c hc
      have hc' : c ∈ T := by first | exact hc | exact Finset.mem_coe.mp hc
      exact (hf c hc').1
    · intro c1 hc1 c2 hc2 heq
      have hc1' : c1 ∈ T := by first | exact hc1 | exact Finset.mem_coe.mp hc1
      have hc2' : c2 ∈ T := by first | exact hc2 | exact Finset.mem_coe.mp hc2
      funext k
      have e1 := (hf c1 hc1').2 k
      have e2 := (hf c2 hc2').2 k
      rw [heq] at e1
      have e3 : π (c1 k - c2 k) ∈ X.L := by
        have h4 := X.L.sub_mem e1 e2
        rwa [← map_sub, sub_sub_sub_cancel_right] at h4
      have hP := (mem_P X hq hπ _).mpr e3
      have hc1k := (mem_reps.mp (Fintype.mem_piFinset.mp hc1' k)).1
      have hc2k := (mem_reps.mp (Fintype.mem_piFinset.mp hc2' k)).1
      have h5 := fd_uniq (bP X hq hπ) (x := c2 k) hP (Submodule.zero_mem _)
        (by rw [sub_add_cancel]; exact hc1k) (by rw [zero_add]; exact hc2k)
      exact sub_eq_zero.mp h5
  have hTc : T.card = q ^ (Fintype.card (Idx X.dim) * n) := by
    simp only [T, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hcR', pow_mul]
  rw [← hTc]
  exact hcard

end

end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
