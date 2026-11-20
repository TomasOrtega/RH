import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieMeasureFrameBoxGeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieHaarLeTwoMulTangentNormalizedHaarStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.LowBall

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Use `set W := (realLie Ψ G).comap (fromFrame x)`. Set `Φ : W →ₗ[ℝ] realLie Ψ G` to `((fromFrame x).comp W.subtype).codRestrict (realLie Ψ G) (fun v => v.2)`. Establish `key2 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ), mat x τ * ((mat x τ)⁻¹ * A * mat x τ) * (mat x τ)⁻¹ = A` using `fun τ A => by`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit, Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]`. Establish `hsurj : Function.Surjective Φ`.

Introduce `X`. Set `Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)` to `WithLp.toLp 2 (fun p : Ψ × Fin r × Fin r => ((mat x p.1)⁻¹ * Matrix.of (X.1 p.1) * mat x p.1) p.2.1 p.2.2)`. Establish `hY : fromFrame x Y = X.1`. Use function extensionality and compare the values at `τ`. Establish `e : Matrix.of (fun a b => Y (τ, a, b)) = (mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ`.

Use extensionality with `a b`. Simplify using `[Y]`. Express the relevant statement in the definitionally equal form `(mat x τ * Matrix.of _ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = X.1 τ`. Rewrite using `[e, key2]`. Both sides reduce to the same expression.

Conclude with `⟨⟨Y, show fromFrame x Y ∈ realLie Ψ G by rw [hY]; exact X.2⟩, Subtype.ext hY⟩`. Establish `key1 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ), (mat x τ)⁻¹ * (mat x τ * A * (mat x τ)⁻¹) * mat x τ = A` using `fun τ A => by`. Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit, Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]`. Establish `hinj : Function.Injective Φ`. Introduce `Y Z h`.

Establish `h' : fromFrame x Y.1 = fromFrame x Z.1` using `congrArg Subtype.val h`. Establish `hτ : ∀ τ, Matrix.of (fun a b => Y.1 (τ, a, b)) = Matrix.of (fun a b => Z.1 (τ, a, b))`. Introduce `τ`. Establish `h1 : mat x τ * Matrix.of (fun a b => Y.1 (τ, a, b)) * (mat x τ)⁻¹ = mat x τ * Matrix.of (fun a b => Z.1 (τ, a, b)) * (mat x τ)⁻¹` using `congrFun h' τ`. Rewrite using `[← key1 τ (Matrix.of (fun a b => Y.1 (τ, a, b))), h1, key1]`.

Use `Subtype.ext (PiLp.ext fun p => ?_)` and prove the remaining obligations. Take `⟨τ, a, b⟩` from `p`. Conclude with `congrFun (congrFun (hτ τ) a) b`. Set `φ : W ≃L[ℝ] realLie Ψ G` to `(LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).toContinuousLinearEquiv`. Use `⟨(stdOrthonormalBasis ℝ W).toBasis.addHaar.map φ, φ.isAddHaarMeasure_map _, ?_⟩` and prove the remaining obligations.

Rewrite using `[Measure.map_map measurable_subtype_coe φ.continuous.measurable]`. Both sides reduce to the same expression.
-/
theorem exists_lam (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r)
    (hx : ∀ τ, (mat x τ).det ≠ 0) :
    ∃ lam : Measure (realLie Ψ G), lam.IsAddHaarMeasure ∧ lam.map Subtype.val = riemLie Ψ G x := by
  set W := (realLie Ψ G).comap (fromFrame x)
  let Φ : W →ₗ[ℝ] realLie Ψ G :=
    ((fromFrame x).comp W.subtype).codRestrict (realLie Ψ G) (fun v => v.2)
  have key2 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      mat x τ * ((mat x τ)⁻¹ * A * mat x τ) * (mat x τ)⁻¹ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hsurj : Function.Surjective Φ := by
    intro X
    let Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r) := WithLp.toLp 2 (fun p : Ψ × Fin r × Fin r =>
      ((mat x p.1)⁻¹ * Matrix.of (X.1 p.1) * mat x p.1) p.2.1 p.2.2)
    have hY : fromFrame x Y = X.1 := by
      funext τ
      have e : Matrix.of (fun a b => Y (τ, a, b)) = (mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ := by
        ext a b; simp [Y]
      change (mat x τ * Matrix.of _ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = X.1 τ
      rw [e, key2]; rfl
    exact ⟨⟨Y, show fromFrame x Y ∈ realLie Ψ G by rw [hY]; exact X.2⟩, Subtype.ext hY⟩
  have key1 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * A * (mat x τ)⁻¹) * mat x τ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]
  have hinj : Function.Injective Φ := by
    intro Y Z h
    have h' : fromFrame x Y.1 = fromFrame x Z.1 := congrArg Subtype.val h
    have hτ : ∀ τ, Matrix.of (fun a b => Y.1 (τ, a, b)) = Matrix.of (fun a b => Z.1 (τ, a, b)) := by
      intro τ
      have h1 : mat x τ * Matrix.of (fun a b => Y.1 (τ, a, b)) * (mat x τ)⁻¹ =
          mat x τ * Matrix.of (fun a b => Z.1 (τ, a, b)) * (mat x τ)⁻¹ := congrFun h' τ
      rw [← key1 τ (Matrix.of (fun a b => Y.1 (τ, a, b))), h1, key1]
    refine Subtype.ext (PiLp.ext fun p => ?_)
    obtain ⟨τ, a, b⟩ := p
    exact congrFun (congrFun (hτ τ) a) b
  let φ : W ≃L[ℝ] realLie Ψ G := (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  refine ⟨(stdOrthonormalBasis ℝ W).toBasis.addHaar.map φ, φ.isAddHaarMeasure_map _, ?_⟩
  rw [Measure.map_map measurable_subtype_coe φ.continuous.measurable]
  rfl

/- English proof (translation)
Set `L : (Ψ → Fin r → Fin r → ℂ) →ₗ[ℝ] (Ψ → Fin r → Fin r → ℂ)` to `{ toFun := fun Y τ => (mat x τ * Matrix.of (Y τ) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) map_add' := fun Y Z => by`. Use function extensionality and compare the values at `τ`. Express the relevant statement in the definitionally equal form `mat x τ * (Matrix.of (Y τ) + Matrix.of (Z τ)) * (mat x τ)⁻¹ = _`. Rewrite using `[Matrix.mul_add, Matrix.add_mul]`. Both sides reduce to the same expression.

Use the proof step `map_smul' := fun c Y => by`. Use function extensionality and compare the values at `τ`. Express the relevant statement in the definitionally equal form `mat x τ * ((c : ℂ) • Matrix.of (Y τ)) * (mat x τ)⁻¹ = _`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`. Use `rfl }`.

Set `Lc` to `LinearMap.toContinuousLinearMap L`. Use `⟨‖Lc‖ + 1, by positivity, fun t X ht hX => ?_⟩` and prove the remaining obligations. Set `Y : Ψ → Fin r → Fin r → ℂ` to `fun τ => ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ : Matrix (Fin r) (Fin r) ℂ)`. Establish `hLY : Lc Y = X`. Use function extensionality and compare the values at `τ`.

Express the relevant statement in the definitionally equal form `mat x τ * ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) * (mat x τ)⁻¹ = Matrix.of (X τ)`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit, Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]`. Establish `hY : ‖Y‖ ≤ t`. Use `(pi_norm_le_iff_of_nonneg ht).2 fun τ => (pi_norm_le_iff_of_nonneg ht).2 fun a => (pi_norm_le_iff_of_nonneg ht).2 fun b => hX τ a b` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_conj_bound (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r) (hx : ∀ τ, (mat x τ).det ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (X : Ψ → Fin r → Fin r → ℂ), 0 ≤ t →
      (∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ ≤ t) → ‖X‖ ≤ C * t := by
  let L : (Ψ → Fin r → Fin r → ℂ) →ₗ[ℝ] (Ψ → Fin r → Fin r → ℂ) :=
    { toFun := fun Y τ => (mat x τ * Matrix.of (Y τ) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
      map_add' := fun Y Z => by
        funext τ
        change mat x τ * (Matrix.of (Y τ) + Matrix.of (Z τ)) * (mat x τ)⁻¹ = _
        rw [Matrix.mul_add, Matrix.add_mul]; rfl
      map_smul' := fun c Y => by
        funext τ
        change mat x τ * ((c : ℂ) • Matrix.of (Y τ)) * (mat x τ)⁻¹ = _
        rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  let Lc := LinearMap.toContinuousLinearMap L
  refine ⟨‖Lc‖ + 1, by positivity, fun t X ht hX => ?_⟩
  let Y : Ψ → Fin r → Fin r → ℂ := fun τ => ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ : Matrix (Fin r) (Fin r) ℂ)
  have hLY : Lc Y = X := by
    funext τ
    change mat x τ * ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) * (mat x τ)⁻¹ = Matrix.of (X τ)
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hY : ‖Y‖ ≤ t := by
    refine (pi_norm_le_iff_of_nonneg ht).2 fun τ => (pi_norm_le_iff_of_nonneg ht).2 fun a =>
      (pi_norm_le_iff_of_nonneg ht).2 fun b => hX τ a b
  calc ‖X‖ = ‖Lc Y‖ := by rw [hLY]
    _ ≤ ‖Lc‖ * ‖Y‖ := Lc.le_opNorm Y
    _ ≤ ‖Lc‖ * t := by gcongr
    _ ≤ (‖Lc‖ + 1) * t := by nlinarith

section Exp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `h` using `(hasFDerivAt_iff_isLittleO_nhds_zero.1 (GlobalTheory.CompactDualExists.exp_strict (n := n)).hasFDerivAt).def (zero_lt_one' ℝ)`. Take `⟨δ, hδ, hh⟩` from `Metric.eventually_nhds_iff.1 h`. Use `⟨δ, hδ, fun Y hY => ?_⟩` and prove the remaining obligations. Use `hh (y := Y) (by rwa [dist_zero_right])` as an intermediate fact. Simplify using `only [zero_add, NormedSpace.exp_zero, one_mul] at this`.

Establish `this : ‖NormedSpace.exp Y - 1 - Y‖ ≤ ‖Y‖` using `this`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_exp_bound (n : Type) [Fintype n] [DecidableEq n] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y : Matrix n n ℂ, ‖Y‖ < δ → ‖NormedSpace.exp Y - 1‖ ≤ 2 * ‖Y‖ := by
  have h := (hasFDerivAt_iff_isLittleO_nhds_zero.1
    (GlobalTheory.CompactDualExists.exp_strict (n := n)).hasFDerivAt).def (zero_lt_one' ℝ)
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun Y hY => ?_⟩
  have := hh (y := Y) (by rwa [dist_zero_right])
  simp only [zero_add, NormedSpace.exp_zero, one_mul] at this
  have this : ‖NormedSpace.exp Y - 1 - Y‖ ≤ ‖Y‖ := this
  calc ‖NormedSpace.exp Y - 1‖ = ‖Y + (NormedSpace.exp Y - 1 - Y)‖ := by congr 1; abel
    _ ≤ ‖Y‖ + ‖NormedSpace.exp Y - 1 - Y‖ := norm_add_le _ _
    _ ≤ 2 * ‖Y‖ := by linarith

/- English proof (translation)
Take `⟨δ, hδ, h⟩` from `exists_exp_bound n`. Use `⟨δ, hδ, fun ε Y hε hεδ hY a b => ?_⟩` and prove the remaining obligations. Establish `hYn : ‖Y‖ < ε / 2` using `(Matrix.norm_lt_iff (by positivity)).2 hY`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_exp_entry (n : Type) [Fintype n] [DecidableEq n] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : ℝ) (Y : Matrix n n ℂ), 0 < ε → ε < δ → (∀ a b, ‖Y a b‖ < ε / 2) →
      ∀ a b, ‖(NormedSpace.exp Y - 1) a b‖ < ε := by
  obtain ⟨δ, hδ, h⟩ := exists_exp_bound n
  refine ⟨δ, hδ, fun ε Y hε hεδ hY a b => ?_⟩
  have hYn : ‖Y‖ < ε / 2 := (Matrix.norm_lt_iff (by positivity)).2 hY
  calc ‖(NormedSpace.exp Y - 1) a b‖ ≤ ‖NormedSpace.exp Y - 1‖ := Matrix.norm_entry_le_entrywise_sup_norm _
    _ ≤ 2 * ‖Y‖ := h Y (by linarith)
    _ < ε := by linarith

end Exp

/- English proof (translation)
Introduce `E _ _ _ r Ψ G x hr hG hx`. Take `⟨lam, hlam, hmap⟩` from `exists_lam Ψ G x hx`. Take `⟨δ, hδ, hlow⟩` from `GlobalTheory.T.lieHaar_le_two_mul_tangentNormalizedHaar E r Ψ G hG lam`. Take `⟨C, hC, hconj⟩` from `exists_conj_bound Ψ x hx`. Apply the tactic sequence `obtain ⟨δ', hδ', hexp⟩ := exists_exp_entry (Fin r)`.

Use `⟨min 2 (min δ' (δ / C)), lt_min two_pos (lt_min hδ' (div_pos hδ hC)), fun ε hε hε₀ => ?_⟩` and prove the remaining obligations. Establish `hε2 : ε < 2` using `lt_of_lt_of_le hε₀ (min_le_left _ _)`. Establish `hεδ' : ε < δ'` using `lt_of_lt_of_le hε₀ ((min_le_right _ _).trans (min_le_left _ _))`. Establish `hεC : ε < δ / C` using `lt_of_lt_of_le hε₀ ((min_le_right _ _).trans (min_le_right _ _))`. Use `set S : Set (Ψ → Fin r → Fin r → ℂ) := {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < ε / 2} with hS`.

Establish `hcont : ∀ τ a b, Continuous (fun X : Ψ → Fin r → Fin r → ℂ => ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b)`. Introduce `τ a b`. Conclude with `((continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const).matrix_elem a b`. Establish `hSm : MeasurableSet S`. Simplify using `only [hS, Set.setOf_forall]`.

Conclude with `MeasurableSet.iInter fun τ => MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => measurableSet_lt (hcont τ a b).norm.measurable measurable_const`. Use `set s : Set (realLie Ψ G) := Subtype.val ⁻¹' S with hs`. Establish `hsm : MeasurableSet s` using `measurable_subtype_coe hSm`. Establish `h1 : ENNReal.ofReal ((ε / 2 / ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) ^ (Ψ.card * (r ^ 2 - 1))) ≤ lam s`. Use `GlobalTheory.T.riemannianLieMeasure_frameBox_ge E r Ψ G x hr hG hx (ε / 2) (by positivity) (by linarith)` as an intermediate fact.

Rewrite `this` using `[← hmap, Measure.map_apply measurable_subtype_coe hSm]`. Conclude with `this`. Establish `hball : s ⊆ Metric.ball 0 δ`. Introduce `X hX`. Rewrite using `[mem_ball_zero_iff]`.

Establish `h` using `hconj (ε / 2) X.1 (by positivity) fun τ a b => (hX τ a b).le`. Establish `hCε : C * ε < δ` using `by rw [lt_div_iff₀ hC] at hεC; linarith`. Combine the equalities or inequalities in the displayed calculation. Establish `himg : GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s ⊆ frBall Ψ G x ε`. Introduce and unpack `_ ⟨X, hX, rfl⟩ τ a b`.

Express the relevant statement in the definitionally equal form `‖((mat x τ)⁻¹ * NormedSpace.exp (Matrix.of (X.1 τ)) * mat x τ - 1) a b‖ < ε`. Rewrite using `[← Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det _).2 (hx τ).isUnit)]`. Conclude with `hexp ε _ hε hεδ' (hX τ) a b`. Establish `h2` using `hlow s hsm hball`. Establish `h3 : tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) ≤ riemHaar Ψ G x (frBall Ψ G x ε)`.

Rewrite using `[hmap]`. Conclude with `measure_mono himg`. Establish `e : ε / (2 * ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) = ε / 2 / ((Ψ.card : ℝ) * (r : ℝ) ^ 2)` using `by rw [div_div]`. Rewrite using `[e, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]`. Use `ENNReal.div_le_of_le_mul ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem riemHaar_frBall_ge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ))
    (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → G.det ≠ 0 → (∀ τ, (mat x τ).det ≠ 0) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ENNReal.ofReal ((ε / (2 * ((Ψ.card : ℝ) * (r : ℝ) ^ 2))) ^ (Ψ.card * (r ^ 2 - 1)) / 2) ≤
        riemHaar Ψ G x (frBall Ψ G x ε) := by
  intro E _ _ _ r Ψ G x hr hG hx
  obtain ⟨lam, hlam, hmap⟩ := exists_lam Ψ G x hx
  obtain ⟨δ, hδ, hlow⟩ := GlobalTheory.T.lieHaar_le_two_mul_tangentNormalizedHaar E r Ψ G hG lam
  obtain ⟨C, hC, hconj⟩ := exists_conj_bound Ψ x hx
  obtain ⟨δ', hδ', hexp⟩ := exists_exp_entry (Fin r)
  refine ⟨min 2 (min δ' (δ / C)), lt_min two_pos (lt_min hδ' (div_pos hδ hC)), fun ε hε hε₀ => ?_⟩
  have hε2 : ε < 2 := lt_of_lt_of_le hε₀ (min_le_left _ _)
  have hεδ' : ε < δ' := lt_of_lt_of_le hε₀ ((min_le_right _ _).trans (min_le_left _ _))
  have hεC : ε < δ / C := lt_of_lt_of_le hε₀ ((min_le_right _ _).trans (min_le_right _ _))
  set S : Set (Ψ → Fin r → Fin r → ℂ) :=
    {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < ε / 2} with hS
  have hcont : ∀ τ a b, Continuous (fun X : Ψ → Fin r → Fin r → ℂ =>
      ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b) := by
    intro τ a b
    exact ((continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const).matrix_elem a b
  have hSm : MeasurableSet S := by
    simp only [hS, Set.setOf_forall]
    exact MeasurableSet.iInter fun τ => MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      measurableSet_lt (hcont τ a b).norm.measurable measurable_const
  set s : Set (realLie Ψ G) := Subtype.val ⁻¹' S with hs
  have hsm : MeasurableSet s := measurable_subtype_coe hSm
  have h1 : ENNReal.ofReal ((ε / 2 / ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) ^ (Ψ.card * (r ^ 2 - 1))) ≤ lam s := by
    have := GlobalTheory.T.riemannianLieMeasure_frameBox_ge E r Ψ G x hr hG hx (ε / 2) (by positivity) (by linarith)
    rw [← hmap, Measure.map_apply measurable_subtype_coe hSm] at this
    exact this
  have hball : s ⊆ Metric.ball 0 δ := by
    intro X hX
    rw [mem_ball_zero_iff]
    have h := hconj (ε / 2) X.1 (by positivity) fun τ a b => (hX τ a b).le
    have hCε : C * ε < δ := by rw [lt_div_iff₀ hC] at hεC; linarith
    calc ‖X‖ = ‖X.1‖ := rfl
      _ ≤ C * (ε / 2) := h
      _ < δ := by nlinarith
  have himg : GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s ⊆ frBall Ψ G x ε := by
    rintro _ ⟨X, hX, rfl⟩ τ a b
    change ‖((mat x τ)⁻¹ * NormedSpace.exp (Matrix.of (X.1 τ)) * mat x τ - 1) a b‖ < ε
    rw [← Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det _).2 (hx τ).isUnit)]
    exact hexp ε _ hε hεδ' (hX τ) a b
  have h2 := hlow s hsm hball
  have h3 : tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) ≤
      riemHaar Ψ G x (frBall Ψ G x ε) := by
    rw [hmap]; exact measure_mono himg
  have e : ε / (2 * ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) = ε / 2 / ((Ψ.card : ℝ) * (r : ℝ) ^ 2) := by rw [div_div]
  rw [e, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
  refine ENNReal.div_le_of_le_mul ?_
  calc _ ≤ lam s := h1
    _ ≤ 2 * tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) := h2
    _ ≤ 2 * riemHaar Ψ G x (frBall Ψ G x ε) := by gcongr
    _ = riemHaar Ψ G x (frBall Ψ G x ε) * 2 := mul_comm _ _

end GlobalTheory.CovTop.VolUp.LowBall
