import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

noncomputable section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed.Ori

variable {E : Type} [Field E] [NumberField E]

def ev1 (σ : E →+* ℂ) : ℝ ⊗[ℚ] E →ₐ[ℝ] ℂ :=
  Algebra.TensorProduct.lift (Algebra.ofId ℝ ℂ) σ.toRatAlgHom (fun _ _ => Commute.all _ _)

def evM {n : ℕ} (σ : E →+* ℂ) : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E →ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  Algebra.TensorProduct.lift (Algebra.ofId ℝ _) (σ.mapMatrix).toRatAlgHom
    (fun x _ => Algebra.commute_algebraMap_left x _)

/- English proof (translation)
Simplify using `[ev1, Algebra.ofId_apply, Algebra.smul_def]`.
-/
theorem realTensorEvalAlgHom_tmul (σ : E →+* ℂ) (r : ℝ) (x : E) : ev1 σ (r ⊗ₜ x) = r • σ x := by
  simp [ev1, Algebra.ofId_apply, Algebra.smul_def]

/- English proof (translation)
Unfold `evM`. Use `(Algebra.TensorProduct.lift_tmul _ _ _ r x).trans ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem evM_tmul {n : ℕ} (σ : E →+* ℂ) (r : ℝ) (x : Matrix (Fin n) (Fin n) E) :
    evM σ (r ⊗ₜ x) = r • x.map σ := by
  unfold evM
  refine (Algebra.TensorProduct.lift_tmul _ _ _ r x).trans ?_
  rw [Algebra.smul_def]
  rfl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r x`. Rewrite using `[evM_tmul, evM_tmul]`. Use extensionality with `i j`.

Simplify using `[ComplexEmbedding.conjugate_coe_eq]`. Consider the case `add a b ha hb => rw [map_add, ha, hb, map_add, Matrix.map_add _ (map_add _)]`.
-/
theorem evM_conj {n : ℕ} (σ : E →+* ℂ) (z : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) :
    evM (ComplexEmbedding.conjugate σ) z = (evM σ z).map (starRingEnd ℂ) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [evM_tmul, evM_tmul]
    ext i j
    simp [ComplexEmbedding.conjugate_coe_eq]
  | add a b ha hb => rw [map_add, ha, hb, map_add, Matrix.map_add _ (map_add _)]

def Th {K : Type} (f : K → (E →+* ℂ)) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℚ V] (β : V →ₗ[ℚ] (Fin n → E)) :
    ℝ ⊗[ℚ] V →ₗ[ℝ] (K × Fin n → ℂ) :=
  LinearMap.liftBaseChange ℝ
    { toFun := fun w k => f k.1 (β w k.2)
      map_add' := fun a b => by ext k; simp
      map_smul' := fun q a => by ext k; simp [map_rat_smul] }

/- English proof (translation)
Simplify using `[Th]`.
-/
theorem Th_tmul {K : Type} (f : K → (E →+* ℂ)) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℚ V]
    (β : V →ₗ[ℚ] (Fin n → E)) (r : ℝ) (w : V) (k : K × Fin n) :
    Th f β (r ⊗ₜ w) k = r • f k.1 (β w k.2) := by
  simp [Th]

/- English proof (translation)
Establish `hl : actOn rep ℝ (r ⊗ₜ m) = algebraMap ℝ _ r * (Module.End.baseChangeHom ℚ ℝ V) (rep m)`. Unfold `actOn`. Conclude with `Algebra.TensorProduct.lift_tmul _ _ _ r m`. Establish `ha : actOn rep ℝ (r ⊗ₜ m) (s ⊗ₜ w) = (r * s) ⊗ₜ rep m w`. Rewrite using `[hl, Module.End.mul_apply, Module.algebraMap_end_apply]`.

Use `show r • LinearMap.baseChange ℝ (rep m) (s ⊗ₜ w) = _`. Rewrite using `[LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]`. Rewrite using `[ha, Th_tmul, evM_tmul, hβ]`. Simplify using `only [Th_tmul]`. Rewrite using `[RingHom.map_mulVec]`.

Simplify using `[Matrix.mulVec, dotProduct, Finset.smul_sum, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]`.
-/
private theorem th_actOn_tmul_eq_evM_mulVec {K : Type} (f : K → (E →+* ℂ)) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℚ V]
    (β : V →ₗ[ℚ] (Fin n → E)) (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ V)
    (hβ : ∀ x z, β (rep x z) = x *ᵥ β z) (r s : ℝ) (m : Matrix (Fin n) (Fin n) E) (w : V) (τ : K) (i : Fin n) :
    Th f β (actOn rep ℝ (r ⊗ₜ m) (s ⊗ₜ w)) (τ, i) = (evM (f τ) (r ⊗ₜ m) *ᵥ fun j => Th f β (s ⊗ₜ w) (τ, j)) i := by
  have hl : actOn rep ℝ (r ⊗ₜ m) = algebraMap ℝ _ r * (Module.End.baseChangeHom ℚ ℝ V) (rep m) := by
    unfold actOn
    exact Algebra.TensorProduct.lift_tmul _ _ _ r m
  have ha : actOn rep ℝ (r ⊗ₜ m) (s ⊗ₜ w) = (r * s) ⊗ₜ rep m w := by
    rw [hl, Module.End.mul_apply, Module.algebraMap_end_apply]
    show r • LinearMap.baseChange ℝ (rep m) (s ⊗ₜ w) = _
    rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  rw [ha, Th_tmul, evM_tmul, hβ]
  simp only [Th_tmul]
  rw [RingHom.map_mulVec]
  simp [Matrix.mulVec, dotProduct, Finset.smul_sum, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r m`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero`.

Simplify using the standard rewrite rules. Conclude with `(congrFun (Matrix.mulVec_zero _) i).symm`. Consider the case `tmul s w => exact th_actOn_tmul_eq_evM_mulVec f β rep hβ r s m w τ i`. Consider the case `add a b ha hb`. Rewrite using `[map_add, map_add, Pi.add_apply, ha, hb]`.

Establish `: (fun j => Th f β (a + b) (τ, j)) = (fun j => Th f β a (τ, j)) + (fun j => Th f β b (τ, j))`. Use extensionality with `j`. Simplify using the standard rewrite rules. Rewrite using `[this, Matrix.mulVec_add, Pi.add_apply]`. Consider the case `add c d hc hd`.

Rewrite using `[map_add, LinearMap.add_apply, map_add, Pi.add_apply, hc, hd, map_add, Matrix.add_mulVec, Pi.add_apply]`.
-/
theorem Th_act {K : Type} (f : K → (E →+* ℂ)) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℚ V]
    (β : V →ₗ[ℚ] (Fin n → E)) (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ V)
    (hβ : ∀ x z, β (rep x z) = x *ᵥ β z) (y : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) (x : ℝ ⊗[ℚ] V) (τ : K) (i : Fin n) :
    Th f β (actOn rep ℝ y x) (τ, i) = (evM (f τ) y *ᵥ fun j => Th f β x (τ, j)) i := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
    induction x using TensorProduct.induction_on with
    | zero =>
      simp
      exact (congrFun (Matrix.mulVec_zero _) i).symm
    | tmul s w => exact th_actOn_tmul_eq_evM_mulVec f β rep hβ r s m w τ i
    | add a b ha hb =>
      rw [map_add, map_add, Pi.add_apply, ha, hb]
      have : (fun j => Th f β (a + b) (τ, j)) = (fun j => Th f β a (τ, j)) + (fun j => Th f β b (τ, j)) := by
        ext j
        simp
      rw [this, Matrix.mulVec_add, Pi.add_apply]
  | add c d hc hd =>
    rw [map_add, LinearMap.add_apply, map_add, Pi.add_apply, hc, hd, map_add, Matrix.add_mulVec, Pi.add_apply]

variable [IsCMField E]

/- English proof (translation)
Establish `hc : ∀ M : Matrix (Fin n) (Fin n) E, (M.map (IsCMField.complexConj E : E →+* E)).map σ = (M.map σ).map (starRingEnd ℂ)`. Introduce `M`. Use extensionality with `i j`. Simplify using `[IsCMField.complexEmbedding_complexConj]`. Establish `hHc : (H.map (IsCMField.complexConj E : E →+* E)).map σ = gramAt H σ`.

Establish `h1` using `congrArg Matrix.transpose hH`. Rewrite `h1` using `[Matrix.transpose_transpose]`. Rewrite using `[h1, gramAt, Matrix.transpose_map]`. Establish `hu : IsUnit (H.map (IsCMField.complexConj E : E →+* E)).det`. Rewrite using `[show (H.map (IsCMField.complexConj E : E →+* E)).det = (IsCMField.complexConj E : E →+* E) H.det from (RingHom.map_det _ H).symm]`.

Conclude with `((map_ne_zero _).mpr hdet).isUnit`. Establish `hG : IsUnit (gramAt H σ).det`. Rewrite using `[gramAt, Matrix.det_transpose, show (H.map σ).det = σ H.det from (RingHom.map_det σ H).symm]`. Conclude with `((map_ne_zero _).mpr hdet).isUnit`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul r x`. Rewrite using `[starT_tmul, hermStar_apply, evM_tmul, evM_tmul, Matrix.map_mul, Matrix.map_mul, map_nonsingInv σ hu, hHc, Matrix.transpose_map, hc x, Matrix.conjTranspose_smul]`. Establish `hx : ((x.map σ).map (starRingEnd ℂ))ᵀ = (x.map σ)ᴴ`. Use extensionality with `i j`.

Simplify using `[Matrix.conjTranspose_apply]`. Rewrite using `[hx, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.one_mul, star_trivial, Matrix.smul_mul]`. Consider the case `add a b ha hb`. Rewrite using `[map_add, MulOpposite.unop_add, map_add, map_add, Matrix.mul_add, ha, hb, Matrix.conjTranspose_add, Matrix.add_mul]`.
-/
theorem evM_star {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (hH : (H.map (IsCMField.complexConj E : E →+* E))ᵀ = H)
    (hdet : H.det ≠ 0) (σ : E →+* ℂ) (z : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) :
    gramAt H σ * evM σ (starT (hermStar H hdet) ℝ z).unop = (evM σ z)ᴴ * gramAt H σ := by
  have hc : ∀ M : Matrix (Fin n) (Fin n) E,
      (M.map (IsCMField.complexConj E : E →+* E)).map σ = (M.map σ).map (starRingEnd ℂ) := by
    intro M
    ext i j
    simp [IsCMField.complexEmbedding_complexConj]
  have hHc : (H.map (IsCMField.complexConj E : E →+* E)).map σ = gramAt H σ := by
    have h1 := congrArg Matrix.transpose hH
    rw [Matrix.transpose_transpose] at h1
    rw [h1, gramAt, Matrix.transpose_map]
  have hu : IsUnit (H.map (IsCMField.complexConj E : E →+* E)).det := by
    rw [show (H.map (IsCMField.complexConj E : E →+* E)).det = (IsCMField.complexConj E : E →+* E) H.det from
      (RingHom.map_det _ H).symm]
    exact ((map_ne_zero _).mpr hdet).isUnit
  have hG : IsUnit (gramAt H σ).det := by
    rw [gramAt, Matrix.det_transpose, show (H.map σ).det = σ H.det from (RingHom.map_det σ H).symm]
    exact ((map_ne_zero _).mpr hdet).isUnit
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [starT_tmul, hermStar_apply, evM_tmul, evM_tmul, Matrix.map_mul, Matrix.map_mul,
      map_nonsingInv σ hu, hHc, Matrix.transpose_map, hc x, Matrix.conjTranspose_smul]
    have hx : ((x.map σ).map (starRingEnd ℂ))ᵀ = (x.map σ)ᴴ := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    rw [hx, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG,
      Matrix.one_mul, star_trivial, Matrix.smul_mul]
  | add a b ha hb =>
    rw [map_add, MulOpposite.unop_add, map_add, map_add, Matrix.mul_add, ha, hb,
      Matrix.conjTranspose_add, Matrix.add_mul]

/- English proof (translation)
Establish `hz : z * (starRingEnd ℂ) z = (Complex.normSq z : ℂ)` using `Complex.mul_conj z`. Establish `e : D * h * ((if 0 < h.re then Complex.I else -Complex.I) * z) * (starRingEnd ℂ) z = D * h * (if 0 < h.re then Complex.I else -Complex.I) * (Complex.normSq z : ℂ)`. Rewrite using `[← hz]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Establish `hc : (D * h * (if 0 < h.re then Complex.I else -Complex.I)).re = |D.im| * |h.re|` using `by split_ifs with hp`. Simplify using `[Complex.mul_re, Complex.mul_im, hD, hi]`. Rewrite using `[abs_of_neg hD', abs_of_pos hp]`. Expand and normalize the polynomial expressions, which then agree. Establish `hn : h.re < 0` using `lt_of_le_of_ne (not_lt.mp hp) hr`.

Simplify using `[Complex.mul_re, Complex.mul_im, hD, hi]`. Rewrite using `[abs_of_neg hD', abs_of_neg hn]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : 0 < |D.im| * |h.re|` using `mul_pos (abs_pos.mpr hD'.ne) (abs_pos.mpr hr)`. Rewrite using `[Complex.re_mul_ofReal, hc]`.

Use `⟨mul_nonneg hpos.le (Complex.normSq_nonneg z), fun hz0 => ?_⟩` and prove the remaining obligations. Conclude with `mul_pos hpos (Complex.normSq_pos.mpr hz0)`.
-/
theorem term_pos (D h z : ℂ) (hD : D.re = 0) (hD' : D.im < 0) (hi : h.im = 0) (hr : h.re ≠ 0) :
    0 ≤ (D * h * ((if 0 < h.re then Complex.I else -Complex.I) * z) * (starRingEnd ℂ) z).re ∧
    (z ≠ 0 → 0 < (D * h * ((if 0 < h.re then Complex.I else -Complex.I) * z) * (starRingEnd ℂ) z).re) := by
  have hz : z * (starRingEnd ℂ) z = (Complex.normSq z : ℂ) := Complex.mul_conj z
  have e : D * h * ((if 0 < h.re then Complex.I else -Complex.I) * z) * (starRingEnd ℂ) z =
      D * h * (if 0 < h.re then Complex.I else -Complex.I) * (Complex.normSq z : ℂ) := by
    rw [← hz]
    ring
  rw [e]
  have hc : (D * h * (if 0 < h.re then Complex.I else -Complex.I)).re = |D.im| * |h.re| := by
    split_ifs with hp
    · simp [Complex.mul_re, Complex.mul_im, hD, hi]
      rw [abs_of_neg hD', abs_of_pos hp]
      ring
    · have hn : h.re < 0 := lt_of_le_of_ne (not_lt.mp hp) hr
      simp [Complex.mul_re, Complex.mul_im, hD, hi]
      rw [abs_of_neg hD', abs_of_neg hn]
      ring
  have hpos : 0 < |D.im| * |h.re| := mul_pos (abs_pos.mpr hD'.ne) (abs_pos.mpr hr)
  rw [Complex.re_mul_ofReal, hc]
  refine ⟨mul_nonneg hpos.le (Complex.normSq_nonneg z), fun hz0 => ?_⟩
  exact mul_pos hpos (Complex.normSq_pos.mpr hz0)

end UpperTheory.Gal.W2.Seed.Ori
