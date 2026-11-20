import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralFundSetInterLe

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal Matrix

namespace GlobalTheory.CovolConj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Use `FundSetPf.countable_GL (E := E) (r := r)` as an intermediate fact. Establish `hM : MeasInvStatement (E` using `E) := measInv_holds`. Establish `hle` using `GlobalTheory.Unfold.lintegral_fundSet_inter_le hM r X x0 x1 h0 h1 F0 hF0 (fun _ => 1) measurable_const (fun _ _ _ _ _ _ => rfl) F1 hF1.1 hF1.2.1`. Simplify using `only [setLIntegral_one] at hle`. Use `le_trans (le_of_eq ?_) hle` and prove the remaining obligations.

Set `S : Set (Frame X.Ψ r)` to `⋃ γ : X.Γ, (fun x => lact (γ.1)⁻¹ x) ⁻¹' GlobalTheory.Unfold.satFrames X x1 F1`. Establish `hS : MeasurableSet S` using `MeasurableSet.iUnion fun γ => (GlobalTheory.Unfold.continuous_lact X _).measurable (GlobalTheory.Unfold.measurableSet_satFrames X h1 hF1.1 hF1.2.1)`. Establish `hSiff : ∀ x, x ∈ S ↔ ∃ y ∈ F1, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (cpt X x1 y) b)`. Introduce `x`. Simplify using `only [S, Set.mem_iUnion, Set.mem_preimage]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ, y, hy, b, hb, h⟩`. Use `⟨y, hy, γ.1, γ.2, b, hb, ?_⟩` and prove the remaining obligations. Rewrite using `[← h, ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one]`. Introduce and unpack `⟨y, hy, γ, hγ, b, hb, h⟩`.

Conclude with `⟨⟨γ, hγ⟩, y, hy, b, hb, by rw [h, FundSetPf.lact_inv]⟩`. Establish `hSB : ∀ x, ∀ b ∈ Bor X.Ψ r, rmul x b ∈ S ↔ x ∈ S`. Introduce `x b hb`. Simplify using `only [S, Set.mem_iUnion, Set.mem_preimage, FundSetPf.lact_rmul, GlobalTheory.Unfold.rmul_mem_satFrames_iff X x1 F1 _ hb]`. Establish `hI` using `hM r X x0 x1 h0 h1 (Sᶜ.indicator fun _ => 1) (measurable_const.indicator hS.compl) (fun x _ b hb => by simp only [Set.indicator, Set.mem_compl_iff, hSB x b hb])`.

Establish `hc : ∀ x : Frame X.Ψ r, ∫⁻ z, (Sᶜ.indicator fun _ => (1 : ℝ≥0∞)) (cpt X x z) ∂muF X x = muF X x (cpt X x ⁻¹' Sᶜ)`. Introduce `x`. Rewrite using `[← lintegral_indicator_one ((FundSetPf.cont_cpt X x).measurable hS.compl)]`. Both sides reduce to the same expression. Rewrite `hI` using `[hc, hc]`.

Establish `hz1 : muF X x1 (cpt X x1 ⁻¹' Sᶜ) = 0`. Establish `: ∀ᵐ z ∂muF X x1, cpt X x1 z ∈ S` using `by filter_upwards [hF1.2.2.2] with z hz using (hSiff _).2 hz`. Conclude with `this`. Establish `hz0 : ∀ᵐ z ∂muF X x0, cpt X x0 z ∈ S` using `hI.trans hz1`. Use `measure_congr ?_` and prove the remaining obligations.

Use `filter_upwards [hz0] with z hz`. Conclude with `propext ⟨fun h => ⟨h, (hSiff _).1 hz⟩, fun h => h.1⟩`.
-/
theorem mass_le (X : Data E r) {x0 x1 : Frame X.Ψ r} (h0 : IsOrth X x0) (h1 : IsOrth X x1)
    {F0 F1 : Set (V (nd X))} (hF0 : IsFundSet X x0 F0) (hF1 : IsFundSet X x1 F1) :
    muF X x0 F0 ≤ muF X x1 F1 := by
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hM : MeasInvStatement (E := E) := measInv_holds
  have hle := GlobalTheory.Unfold.lintegral_fundSet_inter_le hM r X x0 x1 h0 h1 F0 hF0 (fun _ => 1)
    measurable_const (fun _ _ _ _ _ _ => rfl) F1 hF1.1 hF1.2.1
  simp only [setLIntegral_one] at hle
  refine le_trans (le_of_eq ?_) hle
  let S : Set (Frame X.Ψ r) :=
    ⋃ γ : X.Γ, (fun x => lact (γ.1)⁻¹ x) ⁻¹' GlobalTheory.Unfold.satFrames X x1 F1
  have hS : MeasurableSet S := MeasurableSet.iUnion fun γ =>
    (GlobalTheory.Unfold.continuous_lact X _).measurable (GlobalTheory.Unfold.measurableSet_satFrames X h1 hF1.1 hF1.2.1)
  have hSiff : ∀ x, x ∈ S ↔ ∃ y ∈ F1, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
      x = lact γ (rmul (cpt X x1 y) b) := by
    intro x
    simp only [S, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨γ, y, hy, b, hb, h⟩
      refine ⟨y, hy, γ.1, γ.2, b, hb, ?_⟩
      rw [← h, ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one]
    · rintro ⟨y, hy, γ, hγ, b, hb, h⟩
      exact ⟨⟨γ, hγ⟩, y, hy, b, hb, by rw [h, FundSetPf.lact_inv]⟩
  have hSB : ∀ x, ∀ b ∈ Bor X.Ψ r, rmul x b ∈ S ↔ x ∈ S := by
    intro x b hb
    simp only [S, Set.mem_iUnion, Set.mem_preimage, FundSetPf.lact_rmul,
      GlobalTheory.Unfold.rmul_mem_satFrames_iff X x1 F1 _ hb]
  have hI := hM r X x0 x1 h0 h1 (Sᶜ.indicator fun _ => 1) (measurable_const.indicator hS.compl)
    (fun x _ b hb => by simp only [Set.indicator, Set.mem_compl_iff, hSB x b hb])
  have hc : ∀ x : Frame X.Ψ r, ∫⁻ z, (Sᶜ.indicator fun _ => (1 : ℝ≥0∞)) (cpt X x z) ∂muF X x =
      muF X x (cpt X x ⁻¹' Sᶜ) := by
    intro x
    rw [← lintegral_indicator_one ((FundSetPf.cont_cpt X x).measurable hS.compl)]
    rfl
  rw [hc, hc] at hI
  have hz1 : muF X x1 (cpt X x1 ⁻¹' Sᶜ) = 0 := by
    have : ∀ᵐ z ∂muF X x1, cpt X x1 z ∈ S := by
      filter_upwards [hF1.2.2.2] with z hz using (hSiff _).2 hz
    exact this
  have hz0 : ∀ᵐ z ∂muF X x0, cpt X x0 z ∈ S := hI.trans hz1
  refine measure_congr ?_
  filter_upwards [hz0] with z hz
  exact propext ⟨fun h => ⟨h, (hSiff _).1 hz⟩, fun h => h.1⟩

/- English proof (translation)
The claim follows from `le_antisymm (mass_le X h0 h1 hF0 hF1) (mass_le X h1 h0 hF1 hF0)`.
-/
theorem mass_eq (X : Data E r) {x0 x1 : Frame X.Ψ r} (h0 : IsOrth X x0) (h1 : IsOrth X x1)
    {F0 F1 : Set (V (nd X))} (hF0 : IsFundSet X x0 F0) (hF1 : IsFundSet X x1 F1) :
    muF X x0 F0 = muF X x1 F1 :=
  le_antisymm (mass_le X h0 h1 hF0 hF1) (mass_le X h1 h0 hF1 hF0)

omit [IsCMField E] [NumberField E] in
/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [IsCMField E] [NumberField E] in
/- English proof (translation)
Rewrite `hu` using `[gram_eq]`. Rewrite using `[gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]`. Use `conv_rhs => rw [← hu]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem gram_mul {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} {u : Matrix (Fin r) (Fin r) ℂ}
    (hu : gram τ G u = G.map τ) (x : Matrix (Fin r) (Fin r) ℂ) : gram τ G (u * x) = gram τ G x := by
  rw [gram_eq] at hu
  rw [gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_assoc]

omit [IsCMField E] [NumberField E] in
/- English proof (translation)
Introduce `h`. Rewrite `hu` using `[gram_eq]`. Establish `h2` using `congrArg Matrix.det hu`. Rewrite `h2` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, zero_mul]`. Establish `h3 : τ G.det = (G.map τ).det` using `RingHom.map_det τ G`.

Conclude with `hG ((map_eq_zero τ).1 (h3.trans h2.symm))`.
-/
theorem det_ne {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} (hG : G.det ≠ 0)
    {u : Matrix (Fin r) (Fin r) ℂ} (hu : gram τ G u = G.map τ) : u.det ≠ 0 := by
  intro h
  rw [gram_eq] at hu
  have h2 := congrArg Matrix.det hu
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, zero_mul] at h2
  have h3 : τ G.det = (G.map τ).det := RingHom.map_det τ G
  exact hG ((map_eq_zero τ).1 (h3.trans h2.symm))

noncomputable def umul {Ψ : Finset (E →+* ℂ)} (u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (x : Frame Ψ r) : Frame Ψ r :=
  fun τ => (u τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ)

section

variable (X : Data E r) {u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}

omit [IsCMField E] [NumberField E] in
/- English proof (translation)
Use function extensionality and compare the values at `τ`. Conclude with `(Matrix.mul_assoc (u τ.1) (mat x τ) (mat b τ)).symm`.
-/
theorem umul_rmul {Ψ : Finset (E →+* ℂ)} (x b : Frame Ψ r) :
    umul u (rmul x b) = rmul (umul u x) b := by
  funext τ
  exact (Matrix.mul_assoc (u τ.1) (mat x τ) (mat b τ)).symm

/- English proof (translation)
The claim follows from `(umul_rmul _ _).symm`.
-/
theorem cpt_umul (x0 : Frame X.Ψ r) (z : V (nd X)) :
    cpt X (umul u x0) z = umul u (cpt X x0 z) := (umul_rmul _ _).symm

/- English proof (translation)
The claim follows from `gram_mul (hu τ.1 τ.2) _`.
-/
theorem gram_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (umul u x) τ) = gram τ.1 X.Gm (mat x τ) :=
  gram_mul (hu τ.1 τ.2) _

/- English proof (translation)
Use `forall_congr' fun τ => and_congr ?_ ?_` and prove the remaining obligations. Establish `: mat (umul u x) τ = u τ.1 * mat x τ` using `rfl`. Rewrite using `[this, Matrix.det_mul]`. Conclude with `⟨right_ne_zero_of_mul, mul_ne_zero (det_ne X.Gm_det (hu τ.1 τ.2))⟩`. Simplify using `only [dmin, gram_umul X hu]`.
-/
theorem umul_mem_dom (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) (x : Frame X.Ψ r) :
    umul u x ∈ X.dom ↔ x ∈ X.dom := by
  refine forall_congr' fun τ => and_congr ?_ ?_
  · have : mat (umul u x) τ = u τ.1 * mat x τ := rfl
    rw [this, Matrix.det_mul]
    exact ⟨right_ne_zero_of_mul, mul_ne_zero (det_ne X.Gm_det (hu τ.1 τ.2))⟩
  · simp only [dmin, gram_umul X hu]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Establish `h1 : u τ.1 * mat x τ = u τ.1 * mat y τ` using `congrFun h τ`. Establish `hd : IsUnit (u τ.1).det` using `isUnit_iff_ne_zero.mpr (det_ne X.Gm_det (hu τ.1 τ.2))`. Use `congrArg (fun M => (u τ.1)⁻¹ * M) h1` as an intermediate fact. Simplify using `only [Matrix.nonsing_inv_mul_cancel_left _ _ hd] at this`.

Conclude with `this`.
-/
theorem umul_inj (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) {x y : Frame X.Ψ r}
    (h : umul u x = umul u y) : x = y := by
  funext τ
  have h1 : u τ.1 * mat x τ = u τ.1 * mat y τ := congrFun h τ
  have hd : IsUnit (u τ.1).det := isUnit_iff_ne_zero.mpr (det_ne X.Gm_det (hu τ.1 τ.2))
  have := congrArg (fun M => (u τ.1)⁻¹ * M) h1
  simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hd] at this
  exact this

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show u τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) = (γ' : Matrix (Fin r) (Fin r) E).map τ.1 * (u τ.1 * mat x τ)`. Rewrite using `[← Matrix.mul_assoc, h τ.1 τ.2, Matrix.mul_assoc]`.
-/
theorem umul_lact {γ γ' : GL (Fin r) E}
    (h : ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ =
      (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) (x : Frame X.Ψ r) :
    umul u (lact γ x) = lact γ' (umul u x) := by
  funext τ
  show u τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    (γ' : Matrix (Fin r) (Fin r) E).map τ.1 * (u τ.1 * mat x τ)
  rw [← Matrix.mul_assoc, h τ.1 τ.2, Matrix.mul_assoc]

/- English proof (translation)
Introduce `τ` and use `by rw [gram_umul X hu]; exact ho τ`.
-/
theorem isOrth_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) {x0 : Frame X.Ψ r}
    (ho : IsOrth X x0) : IsOrth X (umul u x0) := fun τ => by
  rw [gram_umul X hu]; exact ho τ

/- English proof (translation)
Use extensionality with `z`. Use `show cpt X (umul u x0) z ∈ X.dom ↔ cpt X x0 z ∈ X.dom`. Rewrite using `[cpt_umul, umul_mem_dom X hu]`.
-/
theorem OmF_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) (x0 : Frame X.Ψ r) :
    OmF X (umul u x0) = OmF X x0 := by
  ext z
  show cpt X (umul u x0) z ∈ X.dom ↔ cpt X x0 z ∈ X.dom
  rw [cpt_umul, umul_mem_dom X hu]

/- English proof (translation)
Establish `h2 : densF X (umul u x0) = densF X x0`. Use function extensionality and compare the values at `z`. Simplify using `only [densF, dmin, cpt_umul, gram_umul X hu]`. Simplify using `only [muF, OmF_umul X hu, h2]`.
-/
theorem muF_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) (x0 : Frame X.Ψ r) :
    muF X (umul u x0) = muF X x0 := by
  have h2 : densF X (umul u x0) = densF X x0 := by
    funext z
    simp only [densF, dmin, cpt_umul, gram_umul X hu]
  simp only [muF, OmF_umul X hu, h2]

/- English proof (translation)
Use `⟨hF.1, by rw [OmF_umul X hu]; exact hF.2.1, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz z' hz' γ' hγ' b hb h`. Take `⟨γ, hγ, hc⟩` from `h2 γ' hγ'`. Rewrite `h` using `[cpt_umul, cpt_umul, ← umul_rmul, ← umul_lact X hc]`. Conclude with `hF.2.2.1 z hz z' hz' γ hγ b hb (umul_inj X hu h)`.

Rewrite using `[muF_umul X hu] filter_upwards [hF.2.2.2] with z hz`. Take `⟨z', hz', γ, hγ, b, hb, h⟩` from `hz`. Take `⟨γ', hγ', hc⟩` from `h1 γ hγ`. Use `⟨z', hz', γ', hγ', b, hb, ?_⟩` and prove the remaining obligations. Rewrite using `[cpt_umul, cpt_umul, ← umul_rmul, ← umul_lact X hc, h]`.
-/
theorem fundSet_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ)
    (Γ' : Subgroup (GL (Fin r) E))
    (h1 : ∀ γ ∈ X.Γ, ∃ γ' ∈ Γ', ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ =
      (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ)
    (h2 : ∀ γ' ∈ Γ', ∃ γ ∈ X.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ =
      (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ)
    {x0 : Frame X.Ψ r} {FF : Set (V (nd X))} (hF : IsFundSet X x0 FF) :
    MeasurableSet FF ∧ FF ⊆ OmF X (umul u x0) ∧
    (∀ z ∈ FF, ∀ z' ∈ FF, ∀ γ ∈ Γ', ∀ b ∈ Bor X.Ψ r,
      cpt X (umul u x0) z' = lact γ (rmul (cpt X (umul u x0) z) b) → z = z') ∧
    ∀ᵐ z ∂muF X (umul u x0), ∃ z' ∈ FF, ∃ γ ∈ Γ', ∃ b ∈ Bor X.Ψ r,
      cpt X (umul u x0) z = lact γ (rmul (cpt X (umul u x0) z') b) := by
  refine ⟨hF.1, by rw [OmF_umul X hu]; exact hF.2.1, ?_, ?_⟩
  · intro z hz z' hz' γ' hγ' b hb h
    obtain ⟨γ, hγ, hc⟩ := h2 γ' hγ'
    rw [cpt_umul, cpt_umul, ← umul_rmul, ← umul_lact X hc] at h
    exact hF.2.2.1 z hz z' hz' γ hγ b hb (umul_inj X hu h)
  · rw [muF_umul X hu]
    filter_upwards [hF.2.2.2] with z hz
    obtain ⟨z', hz', γ, hγ, b, hb, h⟩ := hz
    obtain ⟨γ', hγ', hc⟩ := h1 γ hγ
    refine ⟨z', hz', γ', hγ', b, hb, ?_⟩
    rw [cpt_umul, cpt_umul, ← umul_rmul, ← umul_lact X hc, h]

end

/- English proof (translation)
Introduce `E _ _ _ r X X' hΨ u x0 x0' FF FF' hG hp hu h1 h2 ho ho' hF hF'`. Establish `k1` using `isOrth_umul X hu ho`. Establish `k2` using `fundSet_umul X hu X'.Γ h1 h2 hF`. Rewrite using `[← muF_umul X hu x0]`. Establish `k3` using `fun (y : Frame X'.Ψ r) (F : Set (V (nd X'))) (hy : IsOrth X' y) (hF0 : IsFundSet X' y F) => mass_eq X' hy ho' hF0 hF'`.

Consider the cases of `X`. Consider the cases of `X'`. Simplify using `only at hΨ hG hp`. Substitute `hΨ hG hp` using the available equality. Conclude with `k3 (umul u x0) FF k1 k2`.
-/
theorem muF_eq_of_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (hΨ : X'.Ψ = X.Ψ) (u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (x0 : Frame X.Ψ r) (x0' : Frame X'.Ψ r) (FF : Set (V (nd X))) (FF' : Set (V (nd X'))), X'.Gm = X.Gm → X'.p0 = X.p0 → (∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) → (∀ γ ∈ X.Γ, ∃ γ' ∈ X'.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ = (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) → (∀ γ' ∈ X'.Γ, ∃ γ ∈ X.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ = (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) → IsOrth X x0 → IsOrth X' x0' → IsFundSet X x0 FF → IsFundSet X' x0' FF' → muF X x0 FF = muF X' x0' FF' := by
  intro E _ _ _ r X X' hΨ u x0 x0' FF FF' hG hp hu h1 h2 ho ho' hF hF'
  have k1 := isOrth_umul X hu ho
  have k2 := fundSet_umul X hu X'.Γ h1 h2 hF
  rw [← muF_umul X hu x0]
  have k3 := fun (y : Frame X'.Ψ r) (F : Set (V (nd X'))) (hy : IsOrth X' y) (hF0 : IsFundSet X' y F) =>
    mass_eq X' hy ho' hF0 hF'
  cases X
  cases X'
  dsimp only at hΨ hG hp
  subst hΨ hG hp
  exact k3 (umul u x0) FF k1 k2

end GlobalTheory.CovolConj
