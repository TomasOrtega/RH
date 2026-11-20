import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.KernInvariantSymmPos
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPlaceKernelHolomorphicWeightRowHighest
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExtendByZeroAntitoneOffBreak
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MeasurePreservingMulLeft
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegrableOnMinorFinStatement

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.KernInt

/- English proof (translation)
Consider the cases of `k with`. Consider the case `ofNat k`. Simplify using `only [Int.ofNat_eq_natCast, zpow_natCast, Int.natAbs_natCast, norm_pow]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) h1 _`. Consider the case `negSucc k`.

Rewrite using `[zpow_negSucc, ← inv_pow, norm_pow, Int.natAbs_negSucc]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) h2 _`.
-/
theorem norm_zpow_le {z : ℂ} {C : ℝ} (h1 : ‖z‖ ≤ C) (h2 : ‖z⁻¹‖ ≤ C) (k : ℤ) :
    ‖z ^ k‖ ≤ C ^ k.natAbs := by
  cases k with
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast, Int.natAbs_natCast, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 _
  | negSucc k =>
    rw [zpow_negSucc, ← inv_pow, norm_pow, Int.natAbs_negSucc]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 _

/- English proof (translation)
Set `L'` to `L.toContinuousLinearEquiv`. Establish `_ : (μ.map L').IsAddHaarMeasure` using `L'.isAddHaarMeasure_map μ`. Establish `e` using `Measure.isAddLeftInvariant_eq_smul (μ.map L') ν`. Establish `h2 : IntegrableOn g S (μ.map L')`. Rewrite using `[e, IntegrableOn, Measure.restrict_smul]`.

Conclude with `h.smul_measure_nnreal`. Conclude with `(L'.toHomeomorph.measurableEmbedding.integrableOn_map_iff).1 h2`.
-/
theorem integrableOn_comp_linearEquiv {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
    (μ : Measure V) (ν : Measure W) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] (L : V ≃ₗ[ℂ] W)
    {g : W → ℝ} {S : Set W} (h : IntegrableOn g S ν) : IntegrableOn (g ∘ L) (L ⁻¹' S) μ := by
  let L' := L.toContinuousLinearEquiv
  have _ : (μ.map L').IsAddHaarMeasure := L'.isAddHaarMeasure_map μ
  have e := Measure.isAddLeftInvariant_eq_smul (μ.map L') ν
  have h2 : IntegrableOn g S (μ.map L') := by
    rw [e, IntegrableOn, Measure.restrict_smul]
    exact h.smul_measure_nnreal
  exact (L'.toHomeomorph.measurableEmbedding.integrableOn_map_iff).1 h2

/- English proof (translation)
Substitute `hr` using the available equality. Take `⟨δ₀, h0, h⟩` from `GlobalTheory.T.integrableOn_inv_norm_det_pow_near_indefinite_gram p q n hn`. Use `⟨δ₀, h0, fun A hA => ?_⟩` and prove the remaining obligations. Set `e : Fin p ⊕ Fin q ≃ Fin (p + q)` to `finSumFinEquiv`. Set `L : (Fin (p + q) → Fin (p + q) → ℂ) ≃ₗ[ℂ] ((Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → ℂ)` to `{ toFun := fun x => (A * Matrix.of x).submatrix e e invFun := fun y => (A⁻¹ * (Matrix.of y).submatrix e.symm e.symm : Matrix _ _ ℂ) map_add' := fun x y => by`.

Express the relevant statement in the definitionally equal form `(A * (Matrix.of x + Matrix.of y)).submatrix e e = _`. Rewrite using `[Matrix.mul_add]`. Both sides reduce to the same expression. Use the proof step `map_smul' := fun c x => by`. Express the relevant statement in the definitionally equal form `(A * (c • Matrix.of x)).submatrix e e = _`.

Rewrite using `[Matrix.mul_smul]`. Both sides reduce to the same expression. Use `left_inv := fun x => by`. Express the relevant statement in the definitionally equal form `A⁻¹ * ((A * Matrix.of x).submatrix e e).submatrix e.symm e.symm = Matrix.of x`. Rewrite using `[Matrix.submatrix_submatrix, e.self_comp_symm, Matrix.submatrix_id_id, Matrix.nonsing_inv_mul_cancel_left _ _ hA]`.

Use `right_inv := fun y => by`. Express the relevant statement in the definitionally equal form `(A * (A⁻¹ * (Matrix.of y).submatrix e.symm e.symm)).submatrix e e = Matrix.of y`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_left _ _ hA, Matrix.submatrix_submatrix, e.symm_comp_self, Matrix.submatrix_id_id] }`. Establish `_ : (volume : Measure (Fin (p + q) → ℂ)).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`. Establish `_ : (volume : Measure (Fin (p + q) → Fin (p + q) → ℂ)).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`.

Establish `_ : (volume : Measure (Fin p ⊕ Fin q → ℂ)).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`. Establish `_ : (volume : Measure ((Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → ℂ)).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`. Establish `hS : Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1 : Matrix (Fin q) (Fin q) ℂ) = (Matrix.diagonal fun a : Fin (p + q) => ((sgn p (a : ℕ) : ℝ) : ℂ)).submatrix e e`. Rewrite using `[Matrix.submatrix_diagonal_equiv]`. Apply the tactic sequence `ext (a | a) (b | b) <;> simp [Matrix.diagonal_apply, Matrix.one_apply, sgn, e]`.

Apply the tactic sequence `split_ifs <;> simp`. Use `(integrableOn_comp_linearEquiv volume volume L h).mono_set fun x hx a b => ?_` and prove the remaining obligations. Establish `e1 : Matrix.of (L x) = (A * Matrix.of x).submatrix e e` using `rfl`. Rewrite using `[e1, hS, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv]`. Conclude with `hx _ _`.
-/
theorem integrableOn_place {r p q n : ℕ} (hr : p + q = r) (hp : p ≤ r) (hn : 2 * r ≤ n) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ A : Matrix (Fin r) (Fin r) ℂ, IsUnit A.det →
      IntegrableOn (fun x : Fin r → Fin r → ℂ =>
        (‖lminor (A * Matrix.of x) ⟨p, Nat.lt_succ_of_le hp⟩‖ ^ n)⁻¹)
      {x | ∀ a b, ‖((A * Matrix.of x)ᵀ * (Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) *
        (A * Matrix.of x).map conj) a b -
        (Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) a b‖ < δ₀} volume := by
  subst hr
  obtain ⟨δ₀, h0, h⟩ := GlobalTheory.T.integrableOn_inv_norm_det_pow_near_indefinite_gram p q n hn
  refine ⟨δ₀, h0, fun A hA => ?_⟩
  let e : Fin p ⊕ Fin q ≃ Fin (p + q) := finSumFinEquiv
  let L : (Fin (p + q) → Fin (p + q) → ℂ) ≃ₗ[ℂ] ((Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → ℂ) :=
    { toFun := fun x => (A * Matrix.of x).submatrix e e
      invFun := fun y => (A⁻¹ * (Matrix.of y).submatrix e.symm e.symm : Matrix _ _ ℂ)
      map_add' := fun x y => by
        change (A * (Matrix.of x + Matrix.of y)).submatrix e e = _
        rw [Matrix.mul_add]; rfl
      map_smul' := fun c x => by
        change (A * (c • Matrix.of x)).submatrix e e = _
        rw [Matrix.mul_smul]; rfl
      left_inv := fun x => by
        change A⁻¹ * ((A * Matrix.of x).submatrix e e).submatrix e.symm e.symm = Matrix.of x
        rw [Matrix.submatrix_submatrix, e.self_comp_symm, Matrix.submatrix_id_id,
          Matrix.nonsing_inv_mul_cancel_left _ _ hA]
      right_inv := fun y => by
        change (A * (A⁻¹ * (Matrix.of y).submatrix e.symm e.symm)).submatrix e e = Matrix.of y
        rw [Matrix.mul_nonsing_inv_cancel_left _ _ hA,
          Matrix.submatrix_submatrix, e.symm_comp_self, Matrix.submatrix_id_id] }
  have _ : (volume : Measure (Fin (p + q) → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have _ : (volume : Measure (Fin (p + q) → Fin (p + q) → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have _ : (volume : Measure (Fin p ⊕ Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have _ : (volume : Measure ((Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have hS : Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1 : Matrix (Fin q) (Fin q) ℂ) =
      (Matrix.diagonal fun a : Fin (p + q) => ((sgn p (a : ℕ) : ℝ) : ℂ)).submatrix e e := by
    rw [Matrix.submatrix_diagonal_equiv]
    ext (a | a) (b | b) <;> simp [Matrix.diagonal_apply, Matrix.one_apply, sgn, e]
    split_ifs <;> simp
  refine (integrableOn_comp_linearEquiv volume volume L h).mono_set fun x hx a b => ?_
  have e1 : Matrix.of (L x) = (A * Matrix.of x).submatrix e e := rfl
  rw [e1, hS, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.submatrix_map,
    Matrix.submatrix_mul_equiv]
  exact hx _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

/- English proof (translation)
Establish `e` using `FrameDegreeData.gram_mul τ.1 X.Gm (mat x₀ τ) ((mat x₀ τ)⁻¹ * y)`. Rewrite `e` using `[Matrix.mul_nonsing_inv_cancel_left _ _ hu, hx₀ τ]`. Conclude with `e.symm`.
-/
theorem gram_inv_mul {x₀ : Frame X.Ψ r} (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) = sgnM X)
    (τ : X.Ψ) (hu : IsUnit (mat x₀ τ).det) (y : Matrix (Fin r) (Fin r) ℂ) :
    ((mat x₀ τ)⁻¹ * y)ᵀ * sgnM X * ((mat x₀ τ)⁻¹ * y).map conj = gram τ.1 X.Gm y := by
  have e := FrameDegreeData.gram_mul τ.1 X.Gm (mat x₀ τ) ((mat x₀ τ)⁻¹ * y)
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu, hx₀ τ] at e
  exact e.symm

/- English proof (translation)
Establish `e : ∀ v w : Fin r → ℂ, ∀ M : Matrix (Fin r) (Fin r) ℂ, ∑ a, ∑ b, v a * M a b * conj (w b) = v ⬝ᵥ M *ᵥ star w` using `fun v w M => by`. Simplify using `[dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`. Rewrite using `[e, FrameDegreeData.gram_eq]`. Use `(e _ _ (X.Gm.map τ)).trans ?_` and prove the remaining obligations. Rewrite using `[Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v, Matrix.vecMul_transpose, ← Matrix.mulVec_transpose]`.

Both sides reduce to the same expression.
-/
theorem hermC_eq_gram (τ : E →+* ℂ) (A : Matrix (Fin r) (Fin r) ℂ) (v w : Fin r → ℂ) :
    hermC τ X.Gm (A *ᵥ v) (A *ᵥ w) = ∑ a, ∑ b, v a * gram τ X.Gm A a b * conj (w b) := by
  have e : ∀ v w : Fin r → ℂ, ∀ M : Matrix (Fin r) (Fin r) ℂ,
      ∑ a, ∑ b, v a * M a b * conj (w b) = v ⬝ᵥ M *ᵥ star w := fun v w M => by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [e, FrameDegreeData.gram_eq]
  refine (e _ _ (X.Gm.map τ)).trans ?_
  rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec v, Matrix.vecMul_transpose, ← Matrix.mulVec_transpose]
  rfl

/- English proof (translation)
Establish `e : gram τ.1 X.Gm (mat x₀ τ * Matrix.diagonal t * (mat x₀ τ)⁻¹) = gram τ.1 X.Gm 1`. Establish `e1 : gram τ.1 X.Gm (mat x₀ τ * Matrix.diagonal t) = gram τ.1 X.Gm (mat x₀ τ)`. Rewrite using `[FrameDegreeData.gram_mul, hx₀ τ, sgnM, Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Rewrite using `[mul_right_comm, Complex.mul_conj', ht]`. Simplify using the standard rewrite rules. Rewrite using `[FrameDegreeData.gram_mul, e1, ← FrameDegreeData.gram_mul, Matrix.mul_nonsing_inv _ hu]`. Rewrite using `[hermC_eq_gram, e, ← hermC_eq_gram, Matrix.one_mulVec, Matrix.one_mulVec]`.
-/
theorem torus_unitary {x₀ : Frame X.Ψ r} (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) = sgnM X)
    (τ : X.Ψ) (hu : IsUnit (mat x₀ τ).det) (t : Fin r → ℂ) (ht : ∀ i, ‖t i‖ = 1) (v w : Fin r → ℂ) :
    hermC τ.1 X.Gm ((mat x₀ τ * Matrix.diagonal t * (mat x₀ τ)⁻¹) *ᵥ v)
      ((mat x₀ τ * Matrix.diagonal t * (mat x₀ τ)⁻¹) *ᵥ w) = hermC τ.1 X.Gm v w := by
  have e : gram τ.1 X.Gm (mat x₀ τ * Matrix.diagonal t * (mat x₀ τ)⁻¹) = gram τ.1 X.Gm 1 := by
    have e1 : gram τ.1 X.Gm (mat x₀ τ * Matrix.diagonal t) = gram τ.1 X.Gm (mat x₀ τ) := by
      rw [FrameDegreeData.gram_mul, hx₀ τ, sgnM, Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _),
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      rw [mul_right_comm, Complex.mul_conj', ht]
      simp
    rw [FrameDegreeData.gram_mul, e1, ← FrameDegreeData.gram_mul, Matrix.mul_nonsing_inv _ hu]
  rw [hermC_eq_gram, e, ← hermC_eq_gram, Matrix.one_mulVec, Matrix.one_mulVec]

end GlobalTheory.SW.KernInt

/- English proof (translation)
Introduce `E _ _ _ r X g q0 hr idx n c c' m P hn hP h2`. Take `⟨δa, ha, hA⟩` from `thin_slab E r X`. Take `⟨δb, hb, hB⟩` from `KernInt.integrableOn_place hr X.p0_le h2`. Use `⟨min δa δb, lt_min ha hb, fun δ hδ hδ1 x₁ hx₁ => ?_⟩` and prove the remaining obligations. Take `⟨hopen, hsub, horth, -, hun, ⟨C, hC⟩, hdec⟩` from `hA δ hδ (hδ1.trans (min_le_left _ _))`.

Take `⟨x₀, hx₀, b₁, hb₁, rfl⟩` from `hdec x₁ hx₁`. Take `⟨hinv, hsym, -⟩` from `kern_invariant_symm_pos E r X g q0 hr idx n c c' m P hn hP`. Establish `hhol` using `KernHol.kern_hol_weight E r X g q0 hr idx n c c' m P hn hP`. Establish `h₀ : x₀ ∈ X.dom` using `hsub (horth x₀ hx₀)`. Establish `hu : ∀ τ, IsUnit (mat x₀ τ).det` using `fun τ => isUnit_iff_ne_zero.2 (h₀ τ).1`.

Use `set la := wtOf X hr c c' n with hla`. Use `set f : Frame X.Ψ r → ℂ := fun x => kern X hr idx P x x₀ with hf`. Establish `hbd` using `lowest_weight_function_bound E r X q0 hr n c c' x₀ hn hx₀ f (hhol x₀ h₀).1 (hhol x₀ h₀).2 (fun t ht x hx => by`. Establish `ht0 : ∀ τ i, t τ i ≠ 0` using `fun τ i => norm_ne_zero_iff.1 (by rw [ht τ i]; exact one_ne_zero)`. Establish `hU` using `fun τ => KernInt.torus_unitary X hx₀ τ (hu τ) (t τ) (ht τ)`.

Set `s : Frame X.Ψ r` to `fun τ => Matrix.diagonal fun i => (t τ i)⁻¹`. Establish `hs : s ∈ Bor X.Ψ r` using `fun τ => by`. Use `⟨?_, fun a c hca => Matrix.diagonal_apply_ne _ hca.ne'⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Matrix.diagonal fun i => (t τ i)⁻¹).det ≠ 0`. Rewrite using `[Matrix.det_diagonal]`.

Conclude with `Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (ht0 τ i)`. Establish `e : X.lmulC (fun τ => mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹) (rmul x₀ s) = x₀`. Use function extensionality and compare the values at `τ`. Express the relevant statement in the definitionally equal form `mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹ * (mat x₀ τ * Matrix.diagonal fun i => (t τ i)⁻¹) = mat x₀ τ`. Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hu τ), Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]`.

Simplify using `[ht0]`. Establish `hxs : rmul x₀ s ∈ X.dom` using `((hun _ hU).2.2 _).1 (by rw [e]; exact h₀)`. Establish `e2` using `hinv _ hU x hx _ hxs`. Rewrite `e2` using `[e]`. Simplify using `only [hf]`.

Rewrite using `[e2, hsym _ hxs _ hx, (hhol x hx).2 x₀ h₀ s hs, map_mul, ← hsym _ h₀ _ hx]`. Use `congr 1`. Rewrite using `[bchar, map_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_prod]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `e3 : s τ i i = conj (t τ i)` using `(Matrix.diagonal_apply_eq _ _).trans (Complex.inv_eq_conj (ht τ i))`. Rewrite using `[map_zpow₀, e3, Complex.conj_conj])`. Use `set D : Frame X.Ψ r → X.Ψ → ℝ := fun x τ => ‖lminor ((mat x₀ τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ with hD`. Use `set K : ℝ := ‖bchar la b₁‖ * ∏ τ, ∏ i, C ^ (la τ i).natAbs with hK`.

Establish `key : ∀ x ∈ slab X δ, ‖kern X hr idx P (rmul x₀ b₁) x‖ ≤ K * ‖f x₀‖ ∧ ‖kern X hr idx P (rmul x₀ b₁) x‖ ≤ (K * ‖f x₀‖ * ∏ _τ : X.Ψ, (C ^ X.p0) ^ n) * ∏ τ, (D x τ ^ n)⁻¹`. Introduce `x hx`. Establish `hxd` using `hsub hx`. Take `⟨x', hx', b, hb, rfl, hbC⟩` from `hC x hx`. Establish `hx'd` using `hsub (horth x' hx')`.

Establish `h1 : ∀ τ, 1 ≤ D x' τ` using `fun τ => by`. Use `FramePotential.one_le_norm_lminor_sq X.p0_le ((mat x₀ τ)⁻¹ * mat x' τ) ((KernInt.gram_inv_mul X hx₀ τ (hu τ) _).trans (hx' τ))` as an intermediate fact. Conclude with `(one_le_sq_iff_one_le_abs _).1 this |>.trans_eq (abs_norm _)`. Establish `h3 : ‖bchar la b‖ ≤ ∏ τ, ∏ i, C ^ (la τ i).natAbs`. Rewrite using `[bchar, norm_prod]`.

Use `Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[norm_prod]`. Conclude with `Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => KernInt.norm_zpow_le (hbC τ i i).1 (hbC τ i i).2 _`. Establish `h4 : ‖kern X hr idx P (rmul x₀ b₁) (rmul x' b)‖ ≤ K * ‖f x'‖`. Rewrite using `[(hhol _ hxd).2 x₀ h₀ b₁ hb₁, hsym _ hxd _ h₀, (hhol _ h₀).2 x' hx'd b hb, norm_mul, Complex.norm_conj, norm_mul, hK, mul_assoc]`.

Use `gcongr`. Establish `hK0 : 0 ≤ K` using `mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans h3)`. Establish `h5 : ‖f x'‖ * ∏ τ, D x' τ ^ n ≤ ‖f x₀‖` using `hbd x' hx'`. Establish `h6 : 1 ≤ ∏ τ, D x' τ ^ n`. Use `le_of_eq_of_le ?_ (Finset.prod_le_prod (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) fun τ _ => one_le_pow₀ (h1 τ))` and prove the remaining obligations.

Simplify using the standard rewrite rules. Establish `h7 : ∀ τ, D (rmul x' b) τ = D x' τ * ∏ j : Fin X.p0, ‖b τ (Fin.castLE X.p0_le j) (Fin.castLE X.p0_le j)‖` using `fun τ => by`. Express the relevant statement in the definitionally equal form `‖lminor ((mat x₀ τ)⁻¹ * (mat x' τ * mat b τ)) _‖ = _`. Rewrite using `[← Matrix.mul_assoc, FramePotential.lminor_mul_upper _ (FrameDegreeData.upper_of_bor X hb τ), norm_mul, norm_prod]`. Both sides reduce to the same expression.

Establish `h8 : ∀ τ, 0 < D (rmul x' b) τ` using `fun τ => by`. Rewrite using `[h7]`. Conclude with `mul_pos (one_pos.trans_le (h1 τ)) (Finset.prod_pos fun j _ => norm_pos_iff.2 (FrameDegreeData.bdiag_ne X hb τ _))`. Establish `h9 : ∀ τ, D (rmul x' b) τ ≤ D x' τ * C ^ X.p0` using `fun τ => by`. Rewrite using `[h7]`.

Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Use `(Finset.prod_le_prod (fun _ _ => norm_nonneg _) (g := fun _ => C) fun j _ => (hbC τ _ _).1).trans_eq ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `h10 : ∏ τ, D (rmul x' b) τ ^ n ≤ (∏ τ, D x' τ ^ n) * ∏ _τ : X.Ψ, (C ^ X.p0) ^ n`. Rewrite using `[← Finset.prod_mul_distrib]`.

Use `Finset.prod_le_prod (fun τ _ => (pow_pos (h8 τ) n).le) fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ (h8 τ).le (h9 τ) n`. Establish `h11 : 0 < ∏ τ, D (rmul x' b) τ ^ n` using `Finset.prod_pos fun τ _ => pow_pos (h8 τ) n`. Establish `h12 : 0 ≤ ∏ _τ : X.Ψ, (C ^ X.p0) ^ n` using `nonneg_of_mul_nonneg_right (h11.trans_le h10).le (one_pos.trans_le h6)`.

Use `⟨h4.trans (mul_le_mul_of_nonneg_left ((le_mul_of_one_le_right (norm_nonneg _) h6).trans h5) hK0), h4.trans ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ h11, mul_assoc K, mul_assoc K]`. Use `mul_le_mul_of_nonneg_left ?_ hK0` and prove the remaining obligations. Use `(mul_le_mul_of_nonneg_left h10 (norm_nonneg _)).trans ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc]`.

Conclude with `mul_le_mul_of_nonneg_right h5 h12`. Use `⟨?_, _, fun x hx => (key x hx).1⟩` and prove the remaining obligations. Establish `hI : IntegrableOn (fun x : Frame X.Ψ r => ∏ τ, (D x τ ^ n)⁻¹) (slab X δ) volume`. Establish `hτ` using `fun τ : X.Ψ => hB (mat x₀ τ)⁻¹ (Matrix.isUnit_nonsing_inv_det _ (hu τ))`. Simplify using `only [IntegrableOn] at hτ`.

Establish `_ : ∀ S : Set (Fin r → Fin r → ℂ), SigmaFinite (volume.restrict S)` using `fun S => inferInstance`. Establish `h` using `Integrable.fintype_prod_dep hτ`. Rewrite `h` using `[← Measure.restrict_pi_pi]`. Use `IntegrableOn.mono_set h fun x hx τ _ a b => ?_` and prove the remaining obligations. Use `KernInt.gram_inv_mul X hx₀ τ (hu τ) (mat x τ)` as an intermediate fact.

Use `lt_of_eq_of_lt ?_ ((hx τ a b).trans_le (hδ1.trans (min_le_right _ _)))` and prove the remaining obligations. Rewrite using `[← this]`. Both sides reduce to the same expression. Use `Integrable.mono' (hI.const_mul _) ?_ ((ae_restrict_iff' hopen.measurableSet).2 (Filter.Eventually.of_forall fun x hx => (key x hx).2))` and prove the remaining obligations. Use `ContinuousOn.aestronglyMeasurable ?_ hopen.measurableSet` and prove the remaining obligations.

Use `ContinuousOn.congr (f := fun x => bchar la b₁ * conj (f x)) ?_ fun x hx => ?_` and prove the remaining obligations. Conclude with `continuousOn_const.mul (Complex.continuous_conj.comp_continuousOn ((hhol x₀ h₀).1.continuousOn.mono hsub))`. Express the relevant statement in the definitionally equal form `kern X hr idx P (rmul x₀ b₁) x = _`. Rewrite using `[(hhol _ (hsub hx)).2 x₀ h₀ b₁ hb₁, hsym _ (hsub hx) _ h₀]`.
-/
theorem GlobalTheory.SW.kern_integrableOn_slab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ) (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (m : ℕ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), Even n → (∀ j, P j ∈ Harm.rowHighest ℂ c c') → 2 * r ≤ n → ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → ∀ x₁ ∈ X.dom, IntegrableOn (fun x₂ => kern X hr idx P x₁ x₂) (slab X δ) volume ∧ ∃ C : ℝ, ∀ x₂ ∈ slab X δ, ‖kern X hr idx P x₁ x₂‖ ≤ C := by
  intro E _ _ _ r X g q0 hr idx n c c' m P hn hP h2
  obtain ⟨δa, ha, hA⟩ := thin_slab E r X
  obtain ⟨δb, hb, hB⟩ := KernInt.integrableOn_place hr X.p0_le h2
  refine ⟨min δa δb, lt_min ha hb, fun δ hδ hδ1 x₁ hx₁ => ?_⟩
  obtain ⟨hopen, hsub, horth, -, hun, ⟨C, hC⟩, hdec⟩ := hA δ hδ (hδ1.trans (min_le_left _ _))
  obtain ⟨x₀, hx₀, b₁, hb₁, rfl⟩ := hdec x₁ hx₁
  obtain ⟨hinv, hsym, -⟩ := kern_invariant_symm_pos E r X g q0 hr idx n c c' m P hn hP
  have hhol := KernHol.kern_hol_weight E r X g q0 hr idx n c c' m P hn hP
  have h₀ : x₀ ∈ X.dom := hsub (horth x₀ hx₀)
  have hu : ∀ τ, IsUnit (mat x₀ τ).det := fun τ => isUnit_iff_ne_zero.2 (h₀ τ).1
  set la := wtOf X hr c c' n with hla
  set f : Frame X.Ψ r → ℂ := fun x => kern X hr idx P x x₀ with hf
  have hbd := lowest_weight_function_bound E r X q0 hr n c c' x₀ hn hx₀ f (hhol x₀ h₀).1
    (hhol x₀ h₀).2 (fun t ht x hx => by
      have ht0 : ∀ τ i, t τ i ≠ 0 := fun τ i => norm_ne_zero_iff.1 (by rw [ht τ i]; exact one_ne_zero)
      have hU := fun τ => KernInt.torus_unitary X hx₀ τ (hu τ) (t τ) (ht τ)
      let s : Frame X.Ψ r := fun τ => Matrix.diagonal fun i => (t τ i)⁻¹
      have hs : s ∈ Bor X.Ψ r := fun τ => by
        refine ⟨?_, fun a c hca => Matrix.diagonal_apply_ne _ hca.ne'⟩
        change (Matrix.diagonal fun i => (t τ i)⁻¹).det ≠ 0
        rw [Matrix.det_diagonal]
        exact Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (ht0 τ i)
      have e : X.lmulC (fun τ => mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹) (rmul x₀ s) = x₀ := by
        funext τ
        change mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹ *
          (mat x₀ τ * Matrix.diagonal fun i => (t τ i)⁻¹) = mat x₀ τ
        rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hu τ), Matrix.mul_assoc,
          Matrix.diagonal_mul_diagonal]
        simp [ht0]
      have hxs : rmul x₀ s ∈ X.dom := ((hun _ hU).2.2 _).1 (by rw [e]; exact h₀)
      have e2 := hinv _ hU x hx _ hxs
      rw [e] at e2
      simp only [hf]
      rw [e2, hsym _ hxs _ hx, (hhol x hx).2 x₀ h₀ s hs, map_mul, ← hsym _ h₀ _ hx]
      congr 1
      rw [bchar, map_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      have e3 : s τ i i = conj (t τ i) :=
        (Matrix.diagonal_apply_eq _ _).trans (Complex.inv_eq_conj (ht τ i))
      rw [map_zpow₀, e3, Complex.conj_conj])
  set D : Frame X.Ψ r → X.Ψ → ℝ := fun x τ =>
    ‖lminor ((mat x₀ τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ with hD
  set K : ℝ := ‖bchar la b₁‖ * ∏ τ, ∏ i, C ^ (la τ i).natAbs with hK
  have key : ∀ x ∈ slab X δ, ‖kern X hr idx P (rmul x₀ b₁) x‖ ≤ K * ‖f x₀‖ ∧
      ‖kern X hr idx P (rmul x₀ b₁) x‖ ≤
        (K * ‖f x₀‖ * ∏ _τ : X.Ψ, (C ^ X.p0) ^ n) * ∏ τ, (D x τ ^ n)⁻¹ := by
    intro x hx
    have hxd := hsub hx
    obtain ⟨x', hx', b, hb, rfl, hbC⟩ := hC x hx
    have hx'd := hsub (horth x' hx')
    have h1 : ∀ τ, 1 ≤ D x' τ := fun τ => by
      have := FramePotential.one_le_norm_lminor_sq X.p0_le ((mat x₀ τ)⁻¹ * mat x' τ)
        ((KernInt.gram_inv_mul X hx₀ τ (hu τ) _).trans (hx' τ))
      exact (one_le_sq_iff_one_le_abs _).1 this |>.trans_eq (abs_norm _)
    have h3 : ‖bchar la b‖ ≤ ∏ τ, ∏ i, C ^ (la τ i).natAbs := by
      rw [bchar, norm_prod]
      refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => ?_
      rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ =>
        KernInt.norm_zpow_le (hbC τ i i).1 (hbC τ i i).2 _
    have h4 : ‖kern X hr idx P (rmul x₀ b₁) (rmul x' b)‖ ≤ K * ‖f x'‖ := by
      rw [(hhol _ hxd).2 x₀ h₀ b₁ hb₁, hsym _ hxd _ h₀, (hhol _ h₀).2 x' hx'd b hb, norm_mul,
        Complex.norm_conj, norm_mul, hK, mul_assoc]
      gcongr
    have hK0 : 0 ≤ K := mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans h3)
    have h5 : ‖f x'‖ * ∏ τ, D x' τ ^ n ≤ ‖f x₀‖ := hbd x' hx'
    have h6 : 1 ≤ ∏ τ, D x' τ ^ n := by
      refine le_of_eq_of_le ?_ (Finset.prod_le_prod (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
        fun τ _ => one_le_pow₀ (h1 τ))
      simp
    have h7 : ∀ τ, D (rmul x' b) τ = D x' τ * ∏ j : Fin X.p0,
        ‖b τ (Fin.castLE X.p0_le j) (Fin.castLE X.p0_le j)‖ := fun τ => by
      change ‖lminor ((mat x₀ τ)⁻¹ * (mat x' τ * mat b τ)) _‖ = _
      rw [← Matrix.mul_assoc, FramePotential.lminor_mul_upper _ (FrameDegreeData.upper_of_bor X hb τ),
        norm_mul, norm_prod]
      rfl
    have h8 : ∀ τ, 0 < D (rmul x' b) τ := fun τ => by
      rw [h7]
      exact mul_pos (one_pos.trans_le (h1 τ))
        (Finset.prod_pos fun j _ => norm_pos_iff.2 (FrameDegreeData.bdiag_ne X hb τ _))
    have h9 : ∀ τ, D (rmul x' b) τ ≤ D x' τ * C ^ X.p0 := fun τ => by
      rw [h7]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        (g := fun _ => C) fun j _ => (hbC τ _ _).1).trans_eq ?_
      simp
    have h10 : ∏ τ, D (rmul x' b) τ ^ n ≤ (∏ τ, D x' τ ^ n) * ∏ _τ : X.Ψ, (C ^ X.p0) ^ n := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun τ _ => (pow_pos (h8 τ) n).le) fun τ _ => ?_
      rw [← mul_pow]
      exact pow_le_pow_left₀ (h8 τ).le (h9 τ) n
    have h11 : 0 < ∏ τ, D (rmul x' b) τ ^ n := Finset.prod_pos fun τ _ => pow_pos (h8 τ) n
    have h12 : 0 ≤ ∏ _τ : X.Ψ, (C ^ X.p0) ^ n :=
      nonneg_of_mul_nonneg_right (h11.trans_le h10).le (one_pos.trans_le h6)
    refine ⟨h4.trans (mul_le_mul_of_nonneg_left ((le_mul_of_one_le_right (norm_nonneg _) h6).trans h5)
      hK0), h4.trans ?_⟩
    rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ h11, mul_assoc K, mul_assoc K]
    refine mul_le_mul_of_nonneg_left ?_ hK0
    refine (mul_le_mul_of_nonneg_left h10 (norm_nonneg _)).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right h5 h12
  refine ⟨?_, _, fun x hx => (key x hx).1⟩
  have hI : IntegrableOn (fun x : Frame X.Ψ r => ∏ τ, (D x τ ^ n)⁻¹) (slab X δ) volume := by
    have hτ := fun τ : X.Ψ => hB (mat x₀ τ)⁻¹ (Matrix.isUnit_nonsing_inv_det _ (hu τ))
    simp only [IntegrableOn] at hτ
    have _ : ∀ S : Set (Fin r → Fin r → ℂ), SigmaFinite (volume.restrict S) := fun S => inferInstance
    have h := Integrable.fintype_prod_dep hτ
    rw [← Measure.restrict_pi_pi] at h
    refine IntegrableOn.mono_set h fun x hx τ _ a b => ?_
    have := KernInt.gram_inv_mul X hx₀ τ (hu τ) (mat x τ)
    refine lt_of_eq_of_lt ?_ ((hx τ a b).trans_le (hδ1.trans (min_le_right _ _)))
    rw [← this]
    rfl
  refine Integrable.mono' (hI.const_mul _) ?_
    ((ae_restrict_iff' hopen.measurableSet).2 (Filter.Eventually.of_forall fun x hx => (key x hx).2))
  refine ContinuousOn.aestronglyMeasurable ?_ hopen.measurableSet
  refine ContinuousOn.congr (f := fun x => bchar la b₁ * conj (f x)) ?_ fun x hx => ?_
  · exact continuousOn_const.mul
      (Complex.continuous_conj.comp_continuousOn ((hhol x₀ h₀).1.continuousOn.mono hsub))
  · change kern X hr idx P (rmul x₀ b₁) x = _
    rw [(hhol _ (hsub hx)).2 x₀ h₀ b₁ hb₁, hsym _ (hsub hx) _ h₀]
