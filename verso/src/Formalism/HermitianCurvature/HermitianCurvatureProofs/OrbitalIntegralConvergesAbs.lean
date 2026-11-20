import Formalism.HermitianCurvature.StatementG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhaseFunctionCriticalPoints
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AffineChangeOfVariables

open Matrix MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.G7

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2

instance sigmaFinite_mu (β : ℂ) : SigmaFinite (mu β) := by unfold mu; infer_instance

instance sigmaFinite_muPi (β : ℂ) (ι : Type) [Fintype ι] : SigmaFinite (muPi β ι) := by
  unfold muPi; infer_instance

/- English proof (translation)
Unfold `muPi`. Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Simplify using `only [mu, Measure.smul_apply, volume_pi_pi, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]`.
-/
theorem muPi_eq (β : ℂ) (ι : Type) [Fintype ι] :
    muPi β ι = (Real.toNNReal (‖β‖ / (2 * Real.pi))) ^ Fintype.card ι • (volume : Measure (ι → ℂ)) := by
  unfold muPi
  refine Measure.pi_eq fun s hs => ?_
  simp only [mu, Measure.smul_apply, volume_pi_pi, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

/- English proof (translation)
Establish `hdet : LinearMap.det ((Matrix.toLin' M).restrictScalars ℝ) = 1`. Rewrite using `[LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, h, one_pow]`. Establish `h2` using `Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ)) (f := (Matrix.toLin' M).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)`. Rewrite `h2` using `[hdet]`. Establish `h3 : Measure.map (fun x : ι → ℂ => M *ᵥ x) volume = ENNReal.ofReal |(1 : ℝ)⁻¹| • volume` using `h2`.

Simplify using `using h3`.
-/
theorem map_mulVec_volume {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (h : ‖M.det‖ = 1) :
    Measure.map (fun x : ι → ℂ => M *ᵥ x) volume = volume := by
  have hdet : LinearMap.det ((Matrix.toLin' M).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, h, one_pow]
  have h2 := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ))
    (f := (Matrix.toLin' M).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at h2
  have h3 : Measure.map (fun x : ι → ℂ => M *ᵥ x) volume = ENNReal.ofReal |(1 : ℝ)⁻¹| • volume := h2
  simpa using h3

/- English proof (translation)
Establish `hm : Measurable (fun x : ι → ℂ => M *ᵥ x)` using `(Continuous.matrix_mulVec continuous_const continuous_id).measurable`. Use `⟨hm, ?_⟩` and prove the remaining obligations. Rewrite using `[muPi_eq, Measure.map_smul, map_mulVec_volume M h]`.
-/
theorem mp_mulVec (β : ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (h : ‖M.det‖ = 1) :
    MeasurePreserving (fun x : ι → ℂ => M *ᵥ x) (muPi β ι) (muPi β ι) := by
  have hm : Measurable (fun x : ι → ℂ => M *ᵥ x) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  refine ⟨hm, ?_⟩
  rw [muPi_eq, Measure.map_smul, map_mulVec_volume M h]

/- English proof (translation)
Use `mp_mulVec β Mᵀ (by rwa [Matrix.det_transpose])` as an intermediate fact. Simplify `this` using `only [Matrix.mulVec_transpose]`.
-/
theorem mp_vecMul (β : ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (h : ‖M.det‖ = 1) :
    MeasurePreserving (fun x : ι → ℂ => x ᵥ* M) (muPi β ι) (muPi β ι) := by
  have := mp_mulVec β Mᵀ (by rwa [Matrix.det_transpose])
  simpa only [Matrix.mulVec_transpose] using this

/- English proof (translation)
Establish `h` using `congrArg Matrix.det (G3.wMat_mul_self n)`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_one]`. Establish `h2 : ‖(wMat n).det‖ * ‖(wMat n).det‖ = 1` using `by rw [← norm_mul, h, norm_one]`. Use polynomial arithmetic with `[norm_nonneg (wMat n).det]`.
-/
theorem norm_det_wMat (n : ℕ) : ‖(wMat n).det‖ = 1 := by
  have h := congrArg Matrix.det (G3.wMat_mul_self n)
  rw [Matrix.det_mul, Matrix.det_one] at h
  have h2 : ‖(wMat n).det‖ * ‖(wMat n).det‖ = 1 := by rw [← norm_mul, h, norm_one]
  nlinarith [norm_nonneg (wMat n).det]

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Distinguish the cases in `h : i < j`. Simplify using `only [strictUpper, Matrix.of_apply, h, dif_pos]`. Conclude with `continuous_apply _`. Simplify using `only [strictUpper, Matrix.of_apply, h, dif_neg, not_false_iff]`.

Conclude with `continuous_const`.
-/
theorem continuous_strictUpper (d : ℕ) : Continuous (strictUpper : (UT d → ℂ) → Matrix (Fin d) (Fin d) ℂ) := by
  refine continuous_matrix fun i j => ?_
  by_cases h : i < j
  · simp only [strictUpper, Matrix.of_apply, h, dif_pos]
    exact continuous_apply _
  · simp only [strictUpper, Matrix.of_apply, h, dif_neg, not_false_iff]
    exact continuous_const

/- English proof (translation)
The claim follows from `continuous_const.add (continuous_strictUpper d)`.
-/
theorem continuous_upper (d : ℕ) : Continuous (upper : (UT d → ℂ) → Matrix (Fin d) (Fin d) ℂ) :=
  continuous_const.add (continuous_strictUpper d)

/- English proof (translation)
Establish `h1 : MeasurePreserving (fun q : ((UT n → ℂ) × (Fin n → ℂ)) × (Fin n → ℂ) => (q.1, q.2 ᵥ* (wMat n * upper q.1.1))) (((muPi β (UT n)).prod (muPi β (Fin n))).prod (muPi β (Fin n))) (((muPi β (UT n)).prod (muPi β (Fin n))).prod (muPi β (Fin n)))`. Use `(MeasurePreserving.id _).skew_product (g := fun (q : (UT n → ℂ) × (Fin n → ℂ)) (a : Fin n → ℂ) => a ᵥ* (wMat n * upper q.1)) ?_ ?_` and prove the remaining obligations. Use `Continuous.measurable ?_` and prove the remaining obligations. Conclude with `Continuous.matrix_vecMul continuous_snd (continuous_const.matrix_mul ((continuous_upper n).comp (continuous_fst.comp continuous_fst)))`. Conclude with `Filter.Eventually.of_forall fun q => (mp_vecMul β _ (by rw [Matrix.det_mul, det_upper, mul_one, norm_det_wMat])).map_eq`.

Conclude with `Measure.measurePreserving_swap.comp (h1.comp Measure.measurePreserving_swap)`.
-/
theorem mp_shear (β : ℂ) (n : ℕ) :
    MeasurePreserving (fun p : BlockCoord n => ((p.1 ᵥ* (wMat n * upper p.2.1), p.2) : BlockCoord n))
      (muBlock β n) (muBlock β n) := by
  have h1 : MeasurePreserving
      (fun q : ((UT n → ℂ) × (Fin n → ℂ)) × (Fin n → ℂ) => (q.1, q.2 ᵥ* (wMat n * upper q.1.1)))
      (((muPi β (UT n)).prod (muPi β (Fin n))).prod (muPi β (Fin n)))
      (((muPi β (UT n)).prod (muPi β (Fin n))).prod (muPi β (Fin n))) := by
    refine (MeasurePreserving.id _).skew_product
      (g := fun (q : (UT n → ℂ) × (Fin n → ℂ)) (a : Fin n → ℂ) => a ᵥ* (wMat n * upper q.1)) ?_ ?_
    · refine Continuous.measurable ?_
      exact Continuous.matrix_vecMul continuous_snd
        (continuous_const.matrix_mul ((continuous_upper n).comp (continuous_fst.comp continuous_fst)))
    · exact Filter.Eventually.of_forall fun q =>
        (mp_vecMul β _ (by rw [Matrix.det_mul, det_upper, mul_one, norm_det_wMat])).map_eq
  exact Measure.measurePreserving_swap.comp (h1.comp Measure.measurePreserving_swap)

/- English proof (translation)
Establish `hm : ∀ ι : Type, ∀ [Fintype ι], Measurable (fun v : ι → ℂ => t • v)` using `fun ι _ => measurable_const_smul t`. Establish `e : (fun p : BlockCoord n => ((t • p.1, t • p.2.1, t • p.2.2) : BlockCoord n)) = Prod.map (fun v => t • v) (Prod.map (fun v => t • v) (fun v => t • v))` using `rfl`. Unfold `muBlock`. Rewrite using `[e, ← Measure.map_prod_map _ _ (hm _) ((hm _).prodMap (hm _)), ← Measure.map_prod_map _ _ (hm _) (hm _), scale_product_measure β t _ ht, scale_product_measure β t _ ht]`. Simplify using `only [ENNReal.smul_def, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]`.

Use `congr 1`. Establish `hc : 2 * Fintype.card (UT n) = n * (n - 1)` using `(dimension_count n).1`. Rewrite using `[hc, Fintype.card_fin, ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← Real.toNNReal_mul (by positivity), ← Real.toNNReal_mul (by positivity), ← mul_inv, ← mul_inv, ← pow_add, ← pow_add]`. Use `congr 4`. Consider the cases of `n with`.

Consider the case `zero => rfl`. Consider the case `succ k => simp only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_scale (β t : ℂ) (n : ℕ) (ht : t ≠ 0) :
    Measure.map (fun p : BlockCoord n => ((t • p.1, t • p.2.1, t • p.2.2) : BlockCoord n)) (muBlock β n) =
      Real.toNNReal ((‖t‖ ^ (n * (n + 3)))⁻¹) • muBlock β n := by
  have hm : ∀ ι : Type, ∀ [Fintype ι], Measurable (fun v : ι → ℂ => t • v) := fun ι _ => measurable_const_smul t
  have e : (fun p : BlockCoord n => ((t • p.1, t • p.2.1, t • p.2.2) : BlockCoord n)) =
      Prod.map (fun v => t • v) (Prod.map (fun v => t • v) (fun v => t • v)) := rfl
  unfold muBlock
  rw [e, ← Measure.map_prod_map _ _ (hm _) ((hm _).prodMap (hm _)), ← Measure.map_prod_map _ _ (hm _) (hm _),
    scale_product_measure β t _ ht, scale_product_measure β t _ ht]
  simp only [ENNReal.smul_def, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  congr 1
  have hc : 2 * Fintype.card (UT n) = n * (n - 1) := (dimension_count n).1
  rw [hc, Fintype.card_fin, ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← Real.toNNReal_mul (by positivity),
    ← Real.toNNReal_mul (by positivity), ← mul_inv, ← mul_inv, ← pow_add, ← pow_add]
  congr 4
  cases n with
  | zero => rfl
  | succ k => simp only [Nat.add_sub_cancel]; ring

/- English proof (translation)
Establish `e : coordMap n t = (fun p : BlockCoord n => ((t • p.1, t • p.2.1, t • p.2.2) : BlockCoord n)) ∘ (fun p : BlockCoord n => ((p.1 ᵥ* (wMat n * upper p.2.1), p.2) : BlockCoord n))` using `rfl`. Establish `hm : Measurable (fun p : BlockCoord n => ((t • p.1, t • p.2.1, t • p.2.2) : BlockCoord n))` using `by fun_prop`. Rewrite using `[e, ← Measure.map_map hm (mp_shear β n).measurable, (mp_shear β n).map_eq, map_scale β t n ht]`.
-/
theorem jacobian (n : ℕ) (β t : ℂ) (ht : t ≠ 0) :
    Measure.map (coordMap n t) (muBlock β n) = Real.toNNReal ((‖t‖ ^ (n * (n + 3)))⁻¹) • muBlock β n := by
  have e : coordMap n t = (fun p : BlockCoord n => ((t • p.1, t • p.2.1, t • p.2.2) : BlockCoord n)) ∘
      (fun p : BlockCoord n => ((p.1 ᵥ* (wMat n * upper p.2.1), p.2) : BlockCoord n)) := rfl
  have hm : Measurable (fun p : BlockCoord n => ((t • p.1, t • p.2.1, t • p.2.2) : BlockCoord n)) := by
    fun_prop
  rw [e, ← Measure.map_map hm (mp_shear β n).measurable, (mp_shear β n).map_eq, map_scale β t n ht]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i < j <;> simp [strictUpper, h]`.
-/
theorem strictUpper_smul {d : ℕ} (a : ℂ) (y : UT d → ℂ) : strictUpper (a • y) = a • strictUpper y := by
  ext i j
  by_cases h : i < j <;> simp [strictUpper, h]

/- English proof (translation)
Introduce `i j hij`. Simplify using `[strictUpper, not_lt.2 hij]`.
-/
theorem isStrictUpper_strictUpper {d : ℕ} (v : UT d → ℂ) : IsStrictUpper (strictUpper v) := by
  intro i j hij
  simp [strictUpper, not_lt.2 hij]

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `i k h`. Establish `: i ≠ k`.

Introduce and unpack `rfl`. Simplify using `at h`. Simplify using `[this]`. Consider the case `succ j ih`. Introduce `i k h`.

Rewrite using `[pow_succ, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : (l : ℕ) < i + j`. Rewrite using `[ih i l hl, zero_mul]`. Rewrite using `[hX l k (by rw [Fin.le_def]; omega), mul_zero]`.
-/
theorem pow_apply_strict {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X) :
    ∀ (j : ℕ) (i k : Fin n), (k : ℕ) < i + j → (X ^ j) i k = 0 := by
  intro j
  induction j with
  | zero =>
    intro i k h
    have : i ≠ k := by
      rintro rfl
      simp at h
    simp [this]
  | succ j ih =>
    intro i k h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : (l : ℕ) < i + j
    · rw [ih i l hl, zero_mul]
    · rw [hX l k (by rw [Fin.le_def]; omega), mul_zero]

/- English proof (translation)
Use extensionality with `i k`. Conclude with `pow_apply_strict X hX n i k (by have := k.2; omega)`.
-/
theorem pow_card_strict {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X) : X ^ n = 0 := by
  ext i k
  exact pow_apply_strict X hX n i k (by have := k.2; omega)

/- English proof (translation)
Introduce `n t c a b v`. Establish `hXs : IsStrictUpper (Xof t v)`. Rewrite using `[Xof, ← strictUpper_smul]`. Conclude with `isStrictUpper_strictUpper _`. Use `set X := Xof t v with hX`.

Use `set B := t • b with hB`. Use `set S : Matrix (Fin n) (Fin n) ℂ := ∑ j ∈ Finset.range n, (-X) ^ j * (t • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (n - 1 - j) with hS`. Establish `hgeom : (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) * S = t ^ n • (1 : Matrix (Fin n) (Fin n) ℂ)`. Establish `hc : Commute (-X) (t • (1 : Matrix (Fin n) (Fin n) ℂ))` using `(Commute.one_right _).smul_right t`. Establish `h1` using `hc.mul_geom_sum₂ n`.

Rewrite `h1` using `[neg_pow, pow_card_strict X hXs, mul_zero, zero_sub, smul_pow, one_pow]`. Establish `h2 : (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) * S = -((-X - t • (1 : Matrix (Fin n) (Fin n) ℂ)) * S)`. Rewrite using `[← neg_mul]`. Use `congr 1`. Normalize the expressions using the abelian group laws.

Rewrite using `[h2, h1, neg_neg]`. Establish `hρ : rhoOf t a v = a ᵥ* (wMat n * (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X))`. Simplify using `only [rhoOf, hX, Xof, G.upper]`. Rewrite using `[← Matrix.vecMul_smul, ← Matrix.mul_smul, smul_add]`. Establish `hsum : ∑ j ∈ Finset.range n, (rhoOf t a v ⬝ᵥ ((-X) ^ j *ᵥ B)) * t ^ (n - 1 - j) = rhoOf t a v ⬝ᵥ (S *ᵥ B)`.

Rewrite using `[hS, Matrix.sum_mulVec, dotProduct_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_pow, one_pow, Matrix.mul_smul, mul_one, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, mul_comm]`. Establish `hfin : (a ᵥ* (wMat n * (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X))) ⬝ᵥ (S *ᵥ B) = t ^ n * (a ⬝ᵥ (wMat n *ᵥ B))`. Rewrite using `[Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, mul_assoc, hgeom, Matrix.mul_smul, mul_one, Matrix.vecMul_smul, smul_dotProduct, ← Matrix.dotProduct_mulVec, smul_eq_mul]`.

Rewrite using `[hsum, hρ, hfin]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cornerRelation : CornerRelation := by
  intro n t c a b v
  have hXs : IsStrictUpper (Xof t v) := by
    rw [Xof, ← strictUpper_smul]; exact isStrictUpper_strictUpper _
  set X := Xof t v with hX
  set B := t • b with hB
  set S : Matrix (Fin n) (Fin n) ℂ :=
    ∑ j ∈ Finset.range n, (-X) ^ j * (t • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (n - 1 - j) with hS
  have hgeom : (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) * S = t ^ n • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have hc : Commute (-X) (t • (1 : Matrix (Fin n) (Fin n) ℂ)) := (Commute.one_right _).smul_right t
    have h1 := hc.mul_geom_sum₂ n
    rw [neg_pow, pow_card_strict X hXs, mul_zero, zero_sub, smul_pow, one_pow] at h1
    have h2 : (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) * S =
        -((-X - t • (1 : Matrix (Fin n) (Fin n) ℂ)) * S) := by
      rw [← neg_mul]; congr 1; abel
    rw [h2, h1, neg_neg]
  have hρ : rhoOf t a v = a ᵥ* (wMat n * (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X)) := by
    simp only [rhoOf, hX, Xof, G.upper]
    rw [← Matrix.vecMul_smul, ← Matrix.mul_smul, smul_add]
  have hsum : ∑ j ∈ Finset.range n, (rhoOf t a v ⬝ᵥ ((-X) ^ j *ᵥ B)) * t ^ (n - 1 - j) =
      rhoOf t a v ⬝ᵥ (S *ᵥ B) := by
    rw [hS, Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_pow, one_pow, Matrix.mul_smul, mul_one, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      mul_comm]
  have hfin : (a ᵥ* (wMat n * (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X))) ⬝ᵥ (S *ᵥ B) =
      t ^ n * (a ⬝ᵥ (wMat n *ᵥ B)) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, mul_assoc, hgeom, Matrix.mul_smul, mul_one,
      Matrix.vecMul_smul, smul_dotProduct, ← Matrix.dotProduct_mulVec, smul_eq_mul]
  rw [hsum, hρ, hfin]
  ring

/- English proof (translation)
Introduce `m X B ρ₁ ρ' t`. Unfold `Cof R0`. Rewrite using `[Finset.sum_mul, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Nat.add_sub_cancel]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cornerSplit : CornerSplit := by
  intro m X B ρ₁ ρ' t
  unfold Cof R0
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Nat.add_sub_cancel]
  ring

noncomputable def sig {m : ℕ} (D t : ℂ) (ρ : Fin (m + 1) → ℂ) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (B : Fin (m + 1) → ℂ) : ℂ :=
  (D + ∑ j ∈ Finset.range (m + 1), (ρ ⬝ᵥ ((-X) ^ j *ᵥ B)) * t ^ (m + 1 - 1 - j)) / t ^ (m + 1)

noncomputable def Fint {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ)
    (Φ : Mat (m + 1 + 1) → V) (t c : ℂ) (p : BlockCoord (m + 1)) : V :=
  psi β ((p.1 0 + ∑ k, xOf (strictUpper p.2.1) p.2.2 k) / t) •
    Φ (Mcoord t (strictUpper p.2.1) p.2.2 p.1 (sig (c * t ^ (m + 1)) t p.1 (strictUpper p.2.1) p.2.2))

/- English proof (translation)
Establish `hσ : c + p.1 ⬝ᵥ (wMat (m + 1) *ᵥ (t • p.2.2)) = sig (c * t ^ (m + 1)) t (rhoOf t p.1 p.2.1) (strictUpper (t • p.2.1)) (t • p.2.2)`. Unfold `sig`. Rewrite using `[eq_div_iff (pow_ne_zero _ ht), mul_comm, cornerRelation (m + 1) t c p.1 p.2.2 p.2.1, Xof, strictUpper_smul]`. Unfold `blockIntegrand Fint coordMap`. Rewrite using `[← (additive_character_psi β _ _).1, phase_formula m t ht p, matrix_entries, hσ, Xof, strictUpper_smul]`.
-/
theorem blockIntegrand_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ)
    (Φ : Mat (m + 1 + 1) → V) (t c : ℂ) (ht : t ≠ 0) (p : BlockCoord (m + 1)) :
    blockIntegrand β (m + 1) Φ t c p = Fint β m Φ t c (coordMap (m + 1) t p) := by
  have hσ : c + p.1 ⬝ᵥ (wMat (m + 1) *ᵥ (t • p.2.2)) =
      sig (c * t ^ (m + 1)) t (rhoOf t p.1 p.2.1) (strictUpper (t • p.2.1)) (t • p.2.2) := by
    unfold sig
    rw [eq_div_iff (pow_ne_zero _ ht), mul_comm, cornerRelation (m + 1) t c p.1 p.2.2 p.2.1, Xof,
      strictUpper_smul]
  unfold blockIntegrand Fint coordMap
  rw [← (additive_character_psi β _ _).1, phase_formula m t ht p, matrix_entries, hσ, Xof,
    strictUpper_smul]

/- English proof (translation)
Unfold `sig`. Rewrite using `[cornerSplit m X B _ ρ' t, rho1, mul_div_cancel₀ _ hC, div_eq_iff (pow_ne_zero _ ht)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem signature_first_coordinate {m : ℕ} (D t σ : ℂ) (ht : t ≠ 0) (ρ' : Fin m → ℂ) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (B : Fin (m + 1) → ℂ) (hC : Cof X B t ≠ 0) :
    sig D t (Fin.cons (rho1 D σ ρ' X B t) ρ') X B = σ := by
  unfold sig
  rw [cornerSplit m X B _ ρ' t, rho1, mul_div_cancel₀ _ hC, div_eq_iff (pow_ne_zero _ ht)]
  ring

/- English proof (translation)
Establish `hT : Measurable (fun p : ℂ × Y => (α p.2 * p.1 + γ p.2, p.2))` using `by fun_prop`. Establish `hd : Measurable (fun p : ℂ × Y => ((‖α p.2‖₊ ^ 2 : NNReal) : ENNReal))` using `by fun_prop`. Use `Measure.ext_of_lintegral _ fun f hf => ?_` and prove the remaining obligations. Establish `hfT : Measurable (fun p : ℂ × Y => f (α p.2 * p.1 + γ p.2, p.2))` using `hf.comp hT`. Rewrite using `[lintegral_map hf hT, lintegral_withDensity_eq_lintegral_mul _ hd hfT, lintegral_prod_symm _ (hd.mul hfT).aemeasurable, lintegral_prod_symm _ hf.aemeasurable]`.

Use `lintegral_congr_ae (h0.mono fun y hy => ?_)` and prove the remaining obligations. Establish `hfy : Measurable (fun x : ℂ => f (x, y))` using `hf.comp (by fun_prop)`. Establish `hA` using `affine_change_of_variables β (α y) (γ y) hy`. Establish `h1 : ∫⁻ x, f (α y * x + γ y, y) ∂(mu β) = ((Real.toNNReal ((‖α y‖ ^ 2)⁻¹) : NNReal) : ENNReal) * ∫⁻ x, f (x, y) ∂(mu β)`. Rewrite using `[← lintegral_map hfy (by fun_prop : Measurable fun x : ℂ => α y * x + γ y), hA, ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul]`.

Establish `hfy2 : Measurable (fun x : ℂ => f (α y * x + γ y, y))` using `hfy.comp (by fun_prop : Measurable fun x : ℂ => α y * x + γ y)`. Simplify using `only [Pi.mul_apply]`. Rewrite using `[lintegral_const_mul _ hfy2, h1, ← mul_assoc, ← ENNReal.coe_mul]`. Establish `h2 : ‖α y‖₊ ^ 2 * Real.toNNReal ((‖α y‖ ^ 2)⁻¹) = 1`. Establish `hpos : (0 : ℝ) < ‖α y‖ ^ 2` using `by positivity`.

Apply `NNReal.eq` to reduce the goal to its premises. Rewrite using `[NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]`. Simplify using `only [NNReal.coe_pow, coe_nnnorm, NNReal.coe_one]`. Conclude with `mul_inv_cancel₀ hpos.ne'`. Rewrite using `[h2, ENNReal.coe_one, one_mul]`.
-/
theorem affine_fibre {Y : Type} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (β : ℂ)
    (α γ : Y → ℂ) (hα : Measurable α) (hγ : Measurable γ) (h0 : ∀ᵐ y ∂ν, α y ≠ 0) :
    Measure.map (fun p : ℂ × Y => (α p.2 * p.1 + γ p.2, p.2))
      (((mu β).prod ν).withDensity (fun p => ((‖α p.2‖₊ ^ 2 : NNReal) : ENNReal))) = (mu β).prod ν := by
  have hT : Measurable (fun p : ℂ × Y => (α p.2 * p.1 + γ p.2, p.2)) := by fun_prop
  have hd : Measurable (fun p : ℂ × Y => ((‖α p.2‖₊ ^ 2 : NNReal) : ENNReal)) := by fun_prop
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hfT : Measurable (fun p : ℂ × Y => f (α p.2 * p.1 + γ p.2, p.2)) := hf.comp hT
  rw [lintegral_map hf hT, lintegral_withDensity_eq_lintegral_mul _ hd hfT,
    lintegral_prod_symm _ (hd.mul hfT).aemeasurable, lintegral_prod_symm _ hf.aemeasurable]
  refine lintegral_congr_ae (h0.mono fun y hy => ?_)
  have hfy : Measurable (fun x : ℂ => f (x, y)) := hf.comp (by fun_prop)
  have hA := affine_change_of_variables β (α y) (γ y) hy
  have h1 : ∫⁻ x, f (α y * x + γ y, y) ∂(mu β) =
      ((Real.toNNReal ((‖α y‖ ^ 2)⁻¹) : NNReal) : ENNReal) * ∫⁻ x, f (x, y) ∂(mu β) := by
    rw [← lintegral_map hfy (by fun_prop : Measurable fun x : ℂ => α y * x + γ y), hA, ENNReal.smul_def,
      lintegral_smul_measure, smul_eq_mul]
  have hfy2 : Measurable (fun x : ℂ => f (α y * x + γ y, y)) :=
    hfy.comp (by fun_prop : Measurable fun x : ℂ => α y * x + γ y)
  simp only [Pi.mul_apply]
  rw [lintegral_const_mul _ hfy2, h1, ← mul_assoc,
    ← ENNReal.coe_mul]
  have h2 : ‖α y‖₊ ^ 2 * Real.toNNReal ((‖α y‖ ^ 2)⁻¹) = 1 := by
    have hpos : (0 : ℝ) < ‖α y‖ ^ 2 := by positivity
    apply NNReal.eq
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
    simp only [NNReal.coe_pow, coe_nnnorm, NNReal.coe_one]
    exact mul_inv_cancel₀ hpos.ne'
  rw [h2, ENNReal.coe_one, one_mul]

/- English proof (translation)
Establish `hT : Measurable (fun p : ℂ × Y => (α p.2 * p.1 + γ p.2, p.2))` using `by fun_prop`. Establish `hd : Measurable (fun p : ℂ × Y => (‖α p.2‖₊ ^ 2 : NNReal))` using `by fun_prop`. Establish `hm` using `affine_fibre ν β α γ hα hγ h0`. Use `conv_lhs => rw [← hm]`. Rewrite using `[integral_map hT.aemeasurable (by rw [hm]; exact hG), integral_withDensity_eq_integral_smul hd]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Simplify using `only [NNReal.smul_def, NNReal.coe_pow, coe_nnnorm]`. Rewrite using `[← Complex.coe_smul]`.
-/
theorem integral_affine_fibre {Y : Type} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (β : ℂ)
    (α γ : Y → ℂ) (hα : Measurable α) (hγ : Measurable γ) (h0 : ∀ᵐ y ∂ν, α y ≠ 0)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (G : ℂ × Y → V)
    (hG : AEStronglyMeasurable G ((mu β).prod ν)) :
    ∫ p, G p ∂((mu β).prod ν) =
      ∫ p, ((‖α p.2‖ ^ 2 : ℝ) : ℂ) • G (α p.2 * p.1 + γ p.2, p.2) ∂((mu β).prod ν) := by
  have hT : Measurable (fun p : ℂ × Y => (α p.2 * p.1 + γ p.2, p.2)) := by fun_prop
  have hd : Measurable (fun p : ℂ × Y => (‖α p.2‖₊ ^ 2 : NNReal)) := by fun_prop
  have hm := affine_fibre ν β α γ hα hγ h0
  conv_lhs => rw [← hm]
  rw [integral_map hT.aemeasurable (by rw [hm]; exact hG), integral_withDensity_eq_integral_smul hd]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [NNReal.smul_def, NNReal.coe_pow, coe_nnnorm]
  rw [← Complex.coe_smul]

def consMap (m : ℕ) (q : RedCoord m) : BlockCoord (m + 1) := (Fin.cons q.1 q.2.1, q.2.2)

/- English proof (translation)
Establish `h1` using `(measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => mu β) 0).symm`. Establish `h2` using `(measurePreserving_prodAssoc (mu β) (muPi β (Fin m)) ((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1))))).symm`. Establish `h3` using `(h1.prod (MeasurePreserving.id ((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1)))))).comp h2`. Establish `e : consMap m = (Prod.map (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) 0).symm) id) ∘ ⇑(MeasurableEquiv.prodAssoc : ((ℂ × (Fin m → ℂ)) × ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ))) ≃ᵐ _).symm`. Use function extensionality and compare the values at `q`.

Simplify using `only [consMap, Function.comp, Prod.map]`. Use `Prod.ext ?_ rfl` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) i <;> simp [MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodAssoc]`. Rewrite using `[e]`.

Conclude with `h3`.
-/
theorem mp_consMap (β : ℂ) (m : ℕ) : MeasurePreserving (consMap m) (muRed β m) (muBlock β (m + 1)) := by
  have h1 := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => mu β) 0).symm
  have h2 := (measurePreserving_prodAssoc (mu β) (muPi β (Fin m))
    ((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1))))).symm
  have h3 := (h1.prod (MeasurePreserving.id ((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1)))))).comp h2
  have e : consMap m = (Prod.map (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) 0).symm) id) ∘
      ⇑(MeasurableEquiv.prodAssoc : ((ℂ × (Fin m → ℂ)) × ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ))) ≃ᵐ _).symm := by
    funext q
    simp only [consMap, Function.comp, Prod.map]
    refine Prod.ext ?_ rfl
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodAssoc]
  rw [e]
  exact h3

/- English proof (translation)
Establish `hX' : IsStrictUpper (-X)` using `fun i j h => by simp [hX i j h]`. Unfold `Cof`. Rewrite using `[Finset.sum_eq_single 0]`. Simplify using the standard rewrite rules. Introduce `j _ hj`.

Rewrite using `[Matrix.mulVec_single_one, Matrix.col_apply, pow_apply_strict (-X) hX' j 0 0 (by simpa using Nat.pos_of_ne_zero hj), zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem cof_single {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hX : IsStrictUpper X) (t : ℂ) :
    Cof X (Pi.single 0 1) t = t ^ m := by
  have hX' : IsStrictUpper (-X) := fun i j h => by simp [hX i j h]
  unfold Cof
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    rw [Matrix.mulVec_single_one, Matrix.col_apply,
      pow_apply_strict (-X) hX' j 0 0 (by simpa using Nat.pos_of_ne_zero hj), zero_mul]
  · simp

noncomputable def cofLin {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (t : ℂ) :
    (Fin (m + 1) → ℂ) →ₗ[ℝ] ℂ where
  toFun B := Cof X B t
  map_add' B B' := by simp [Cof, Matrix.mulVec_add, add_mul, Finset.sum_add_distrib]
  map_smul' r B := by
    simp only [Cof, Matrix.mulVec_smul, Pi.smul_apply, smul_mul_assoc, Finset.smul_sum, RingHom.id_apply]

/- English proof (translation)
Rewrite using `[muPi_eq]`. Use `Measure.ae_smul_measure ?_ _` and prove the remaining obligations. Establish `hker : LinearMap.ker (cofLin X t) ≠ ⊤`. Introduce `h`. Establish `h1 : (Pi.single 0 1 : Fin (m + 1) → ℂ) ∈ LinearMap.ker (cofLin X t)` using `by rw [h]; trivial`.

Rewrite `h1` using `[LinearMap.mem_ker]`. Conclude with `pow_ne_zero m ht ((cof_single X hX t).symm.trans h1)`. Establish `h2` using `Measure.addHaar_submodule (volume : Measure (Fin (m + 1) → ℂ)) _ hker`. Conclude with `(measure_eq_zero_iff_ae_notMem.1 h2).mono fun B hB h => hB (LinearMap.mem_ker.2 h)`.
-/
theorem ae_cof_ne (β t : ℂ) (ht : t ≠ 0) {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hX : IsStrictUpper X) : ∀ᵐ B ∂(muPi β (Fin (m + 1))), Cof X B t ≠ 0 := by
  rw [muPi_eq]
  refine Measure.ae_smul_measure ?_ _
  have hker : LinearMap.ker (cofLin X t) ≠ ⊤ := by
    intro h
    have h1 : (Pi.single 0 1 : Fin (m + 1) → ℂ) ∈ LinearMap.ker (cofLin X t) := by rw [h]; trivial
    rw [LinearMap.mem_ker] at h1
    exact pow_ne_zero m ht ((cof_single X hX t).symm.trans h1)
  have h2 := Measure.addHaar_submodule (volume : Measure (Fin (m + 1) → ℂ)) _ hker
  exact (measure_eq_zero_iff_ae_notMem.1 h2).mono fun B hB h => hB (LinearMap.mem_ker.2 h)

/- English proof (translation)
The claim follows from `Continuous.matrix_mulVec ((((continuous_strictUpper _).comp continuous_fst).neg).pow j) continuous_snd`.
-/
theorem continuous_powMulVec (m j : ℕ) : Continuous
    (fun z : (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) => (-(strictUpper z.1)) ^ j *ᵥ z.2) :=
  Continuous.matrix_mulVec ((((continuous_strictUpper _).comp continuous_fst).neg).pow j) continuous_snd

/- English proof (translation)
Unfold `Cof`. Use `continuous_finsetSum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `((continuous_apply 0).comp (continuous_powMulVec m j)).mul continuous_const`.
-/
theorem continuous_cof (m : ℕ) (t : ℂ) :
    Continuous (fun z : (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) => Cof (strictUpper z.1) z.2 t) := by
  unfold Cof
  refine continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_apply 0).comp (continuous_powMulVec m j)).mul continuous_const

/- English proof (translation)
Unfold `R0`. Use `continuous_finsetSum _ fun j _ => ?_` and prove the remaining obligations. Use `Continuous.mul (continuous_finsetSum _ fun k _ => ?_) continuous_const` and prove the remaining obligations. Conclude with `((continuous_apply k).comp continuous_fst).mul ((continuous_apply k.succ).comp ((continuous_powMulVec m j).comp continuous_snd))`.
-/
theorem continuous_remainder (m : ℕ) (t : ℂ) :
    Continuous (fun y : (Fin m → ℂ) × (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) =>
      R0 (strictUpper y.2.1) y.2.2 y.1 t) := by
  unfold R0
  refine continuous_finsetSum _ fun j _ => ?_
  refine Continuous.mul (continuous_finsetSum _ fun k _ => ?_) continuous_const
  exact ((continuous_apply k).comp continuous_fst).mul
    ((continuous_apply k.succ).comp ((continuous_powMulVec m j).comp continuous_snd))

/- English proof (translation)
Establish `h1 : ∀ᵐ z ∂((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1)))), Cof (strictUpper z.1) z.2 t ≠ 0`. Establish `hms : MeasurableSet {z : (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) | Cof (strictUpper z.1) z.2 t ≠ 0}` using `((isClosed_singleton (x := (0 : ℂ))).preimage (continuous_cof m t)).isOpen_compl.measurableSet`. Use `(Measure.ae_prod_iff_ae_ae hms).2 ?_` and prove the remaining obligations. Use `Filter.Eventually.of_forall fun x => ?_` and prove the remaining obligations. Use `filter_upwards [ae_cof_ne β t ht (strictUpper x) (isStrictUpper_strictUpper x)] with B hB`.

Conclude with `hB`. Conclude with `Measure.quasiMeasurePreserving_snd.ae h1`.
-/
theorem ae_cof_ne' (β t : ℂ) (ht : t ≠ 0) (m : ℕ) :
    ∀ᵐ y ∂((muPi β (Fin m)).prod ((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1))))),
      Cof (strictUpper y.2.1) y.2.2 t ≠ 0 := by
  have h1 : ∀ᵐ z ∂((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1)))), Cof (strictUpper z.1) z.2 t ≠ 0 := by
    have hms : MeasurableSet {z : (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) | Cof (strictUpper z.1) z.2 t ≠ 0} :=
      ((isClosed_singleton (x := (0 : ℂ))).preimage (continuous_cof m t)).isOpen_compl.measurableSet
    refine (Measure.ae_prod_iff_ae_ae hms).2 ?_
    refine Filter.Eventually.of_forall fun x => ?_
    filter_upwards [ae_cof_ne β t ht (strictUpper x) (isStrictUpper_strictUpper x)] with B hB
    exact hB
  exact Measure.quasiMeasurePreserving_snd.ae h1

/- English proof (translation)
Unfold `coordMap rhoOf`. Use `Continuous.prodMk ?_ (by fun_prop)` and prove the remaining obligations. Conclude with `(Continuous.matrix_vecMul continuous_fst (continuous_const.matrix_mul ((continuous_upper n).comp (continuous_fst.comp continuous_snd)))).const_smul t`.
-/
theorem continuous_coordMap (n : ℕ) (t : ℂ) : Continuous (coordMap n t) := by
  unfold coordMap rhoOf
  refine Continuous.prodMk ?_ (by fun_prop)
  exact (Continuous.matrix_vecMul continuous_fst
    (continuous_const.matrix_mul ((continuous_upper n).comp (continuous_fst.comp continuous_snd)))).const_smul t

/- English proof (translation)
Introduce and unpack `⟨a, v, b⟩ ⟨a', v', b'⟩ h`. Simplify using `only [coordMap, Prod.mk.injEq] at h`. Take `⟨h1, h2, h3⟩` from `h`. Establish `hv : v = v'` using `smul_right_injective _ ht h2`. Establish `hb : b = b'` using `smul_right_injective _ ht h3`.

Substitute `hv hb` using the available equality. Establish `h4 : a ᵥ* (wMat n * G.upper v) = a' ᵥ* (wMat n * G.upper v)` using `smul_right_injective _ ht h1`. Establish `hM : IsUnit (wMat n * G.upper v).det`. Rewrite using `[Matrix.det_mul, det_upper, mul_one]`. Conclude with `(det_wMat_ne_zero n).isUnit`.

Establish `h5` using `congrArg (fun x => x ᵥ* (wMat n * G.upper v)⁻¹) h4`. Simplify using `only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hM, Matrix.vecMul_one] at h5`. Rewrite using `[h5]`.
-/
theorem injective_coordMap (n : ℕ) (t : ℂ) (ht : t ≠ 0) : Function.Injective (coordMap n t) := by
  rintro ⟨a, v, b⟩ ⟨a', v', b'⟩ h
  simp only [coordMap, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hv : v = v' := smul_right_injective _ ht h2
  have hb : b = b' := smul_right_injective _ ht h3
  subst hv hb
  have h4 : a ᵥ* (wMat n * G.upper v) = a' ᵥ* (wMat n * G.upper v) := smul_right_injective _ ht h1
  have hM : IsUnit (wMat n * G.upper v).det := by
    rw [Matrix.det_mul, det_upper, mul_one]
    exact (det_wMat_ne_zero n).isUnit
  have h5 := congrArg (fun x => x ᵥ* (wMat n * G.upper v)⁻¹) h4
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hM, Matrix.vecMul_one] at h5
  rw [h5]

/- English proof (translation)
Establish `h1 : TopologicalSpace.SeparableSpace (BlockCoord n)` using `inferInstance`. Establish `h2 : TopologicalSpace.IsCompletelyMetrizableSpace (BlockCoord n)` using `inferInstance`. Establish `h3 : PolishSpace (BlockCoord n)` using `inferInstance`. Conclude with `(continuous_coordMap n t).measurableEmbedding (injective_coordMap n t ht)`.
-/
theorem embedding_coordMap (n : ℕ) (t : ℂ) (ht : t ≠ 0) : MeasurableEmbedding (coordMap n t) := by
  have h1 : TopologicalSpace.SeparableSpace (BlockCoord n) := inferInstance
  have h2 : TopologicalSpace.IsCompletelyMetrizableSpace (BlockCoord n) := inferInstance
  have h3 : PolishSpace (BlockCoord n) := inferInstance
  exact (continuous_coordMap n t).measurableEmbedding (injective_coordMap n t ht)

/- English proof (translation)
Take `⟨σ, ρ', x, B⟩` from `q`. Simplify using `only`. Distinguish the cases in `hC : Cof (strictUpper x) B t = 0`. Simplify using `[hC]`. Establish `hr : t ^ (m + 1) / Cof (strictUpper x) B t * σ + (-(c * t ^ (m + 1)) - R0 (strictUpper x) B ρ' t) / Cof (strictUpper x) B t = rho1 (c * t ^ (m + 1)) σ ρ' (strictUpper x) B t`.

Unfold `rho1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hr]`. Simplify using `only [Fint, consMap, Fin.cons_zero]`. Rewrite using `[signature_first_coordinate _ t σ ht ρ' _ B hC, smul_smul, smul_smul]`.

Use `congr 1`. Rewrite using `[norm_div, norm_pow, div_pow, ← pow_mul, mul_comm (m + 1) 2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pointwise_red {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ)
    (Φ : Mat (m + 1 + 1) → V) (t c : ℂ) (ht : t ≠ 0) (q : RedCoord m) :
    ((‖t ^ (m + 1) / Cof (strictUpper q.2.2.1) q.2.2.2 t‖ ^ 2 : ℝ) : ℂ) •
      Fint β m Φ t c (consMap m
        (t ^ (m + 1) / Cof (strictUpper q.2.2.1) q.2.2.2 t * q.1 +
          (-(c * t ^ (m + 1)) - R0 (strictUpper q.2.2.1) q.2.2.2 q.2.1 t) / Cof (strictUpper q.2.2.1) q.2.2.2 t,
          q.2)) =
    ((‖t‖ ^ (2 * (m + 1)) : ℝ) : ℂ) •
      ((psi β ((rho1 (c * t ^ (m + 1)) q.1 q.2.1 (strictUpper q.2.2.1) q.2.2.2 t +
                ∑ k, xOf (strictUpper q.2.2.1) q.2.2.2 k) / t) *
              (((‖Cof (strictUpper q.2.2.1) q.2.2.2 t‖ ^ 2)⁻¹ : ℝ) : ℂ)) •
            Φ (Mcoord t (strictUpper q.2.2.1) q.2.2.2
              (Fin.cons (rho1 (c * t ^ (m + 1)) q.1 q.2.1 (strictUpper q.2.2.1) q.2.2.2 t) q.2.1) q.1)) := by
  obtain ⟨σ, ρ', x, B⟩ := q
  simp only
  by_cases hC : Cof (strictUpper x) B t = 0
  · simp [hC]
  · have hr : t ^ (m + 1) / Cof (strictUpper x) B t * σ +
        (-(c * t ^ (m + 1)) - R0 (strictUpper x) B ρ' t) / Cof (strictUpper x) B t =
        rho1 (c * t ^ (m + 1)) σ ρ' (strictUpper x) B t := by
      unfold rho1; ring
    rw [hr]
    simp only [Fint, consMap, Fin.cons_zero]
    rw [signature_first_coordinate _ t σ ht ρ' _ B hC, smul_smul, smul_smul]
    congr 1
    rw [norm_div, norm_pow, div_pow, ← pow_mul, mul_comm (m + 1) 2]
    push_cast
    ring

/- English proof (translation)
Introduce `m β t c ht V _ _ _ Φ hint`. Establish `hemb` using `embedding_coordMap (m + 1) t ht`. Establish `hJ` using `jacobian (m + 1) β t ht`. Establish `hfun : blockIntegrand β (m + 1) Φ t c = Fint β m Φ t c ∘ coordMap (m + 1) t`. Use function extensionality and compare the values at `(blockIntegrand_eq β m Φ t c ht)`.

Establish `hpos : (0 : ℝ) < ‖t‖` using `norm_pos_iff.2 ht`. Use `set κ : NNReal := Real.toNNReal ((‖t‖ ^ ((m + 1) * (m + 1 + 3)))⁻¹) with hκ`. Establish `hκ0 : κ ≠ 0`. Rewrite using `[hκ]`. Conclude with `(Real.toNNReal_pos.2 (by positivity)).ne'`.

Establish `hF : Integrable (Fint β m Φ t c) (muBlock β (m + 1))`. Establish `h : Integrable (Fint β m Φ t c) (Measure.map (coordMap (m + 1) t) (muBlock β (m + 1)))` using `hemb.integrable_map_iff.2 (hfun ▸ hint)`. Rewrite `h` using `[hJ, ENNReal.smul_def]`. Conclude with `(integrable_smul_measure (by simpa using hκ0) ENNReal.coe_ne_top).1 h`. Establish `h1 : OmBlock β (m + 1) Φ t c = κ • ∫ p, Fint β m Φ t c p ∂(muBlock β (m + 1))`.

Unfold `OmBlock`. Rewrite using `[hfun, ← integral_smul_nnreal_measure, ← hJ, hemb.integral_map]`. Both sides reduce to the same expression. Establish `hmp` using `mp_consMap β m`. Establish `h2 : ∫ p, Fint β m Φ t c p ∂(muBlock β (m + 1)) = ∫ q, Fint β m Φ t c (consMap m q) ∂(muRed β m)`.

Rewrite using `[← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hF.1)]`. Establish `hcC : Measurable (fun y : (Fin m → ℂ) × (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) => Cof (strictUpper y.2.1) y.2.2 t)` using `((continuous_cof m t).comp continuous_snd).measurable`. Establish `h3` using `integral_affine_fibre ((muPi β (Fin m)).prod ((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1))))) β (fun y => t ^ (m + 1) / Cof (strictUpper y.2.1) y.2.2 t) (fun y => (-(c * t ^ (m + 1)) - R0 (strictUpper y.2.1) y.2.2 y.1 t) / Cof (strictUpper y.2.1) y.2.2 t) (measurable_const.di …`. Establish `h4 : ∫ q, Fint β m Φ t c (consMap m q) ∂(muRed β m) = _` using `h3`. Simplify using `only [pointwise_red β m Φ t c ht] at h4`.

Rewrite `h4` using `[integral_smul]`. Rewrite using `[h1, h2, h4, NNReal.smul_def, ← Complex.coe_smul, smul_smul, smul_smul]`. Establish `hconst : ((‖t‖ ^ ((m + 1) * (m + 2)) : ℝ) : ℂ) * ((κ : ℝ) : ℂ) * ((‖t‖ ^ (2 * (m + 1)) : ℝ) : ℂ) = 1`. Rewrite using `[hκ, Real.coe_toNNReal _ (by positivity), ← Complex.ofReal_mul, ← Complex.ofReal_mul]`. Establish `: ‖t‖ ^ ((m + 1) * (m + 2)) * (‖t‖ ^ ((m + 1) * (m + 1 + 3)))⁻¹ * ‖t‖ ^ (2 * (m + 1)) = 1`.

Establish `e : (m + 1) * (m + 1 + 3) = (m + 1) * (m + 2) + 2 * (m + 1)` using `by ring`. Rewrite using `[e, pow_add]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this, Complex.ofReal_one]`. Rewrite using `[hconst, one_smul]`.

Both sides reduce to the same expression.
-/
theorem omReduced : OmReduced := by
  intro m β t c ht V _ _ _ Φ hint
  have hemb := embedding_coordMap (m + 1) t ht
  have hJ := jacobian (m + 1) β t ht
  have hfun : blockIntegrand β (m + 1) Φ t c = Fint β m Φ t c ∘ coordMap (m + 1) t :=
    funext (blockIntegrand_eq β m Φ t c ht)
  have hpos : (0 : ℝ) < ‖t‖ := norm_pos_iff.2 ht
  set κ : NNReal := Real.toNNReal ((‖t‖ ^ ((m + 1) * (m + 1 + 3)))⁻¹) with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact (Real.toNNReal_pos.2 (by positivity)).ne'
  have hF : Integrable (Fint β m Φ t c) (muBlock β (m + 1)) := by
    have h : Integrable (Fint β m Φ t c) (Measure.map (coordMap (m + 1) t) (muBlock β (m + 1))) :=
      hemb.integrable_map_iff.2 (hfun ▸ hint)
    rw [hJ, ENNReal.smul_def] at h
    exact (integrable_smul_measure (by simpa using hκ0) ENNReal.coe_ne_top).1 h
  have h1 : OmBlock β (m + 1) Φ t c = κ • ∫ p, Fint β m Φ t c p ∂(muBlock β (m + 1)) := by
    unfold OmBlock
    rw [hfun, ← integral_smul_nnreal_measure, ← hJ, hemb.integral_map]
    rfl
  have hmp := mp_consMap β m
  have h2 : ∫ p, Fint β m Φ t c p ∂(muBlock β (m + 1)) = ∫ q, Fint β m Φ t c (consMap m q) ∂(muRed β m) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hF.1)]
  have hcC : Measurable (fun y : (Fin m → ℂ) × (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) =>
      Cof (strictUpper y.2.1) y.2.2 t) := ((continuous_cof m t).comp continuous_snd).measurable
  have h3 := integral_affine_fibre ((muPi β (Fin m)).prod ((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1))))) β
    (fun y => t ^ (m + 1) / Cof (strictUpper y.2.1) y.2.2 t)
    (fun y => (-(c * t ^ (m + 1)) - R0 (strictUpper y.2.1) y.2.2 y.1 t) / Cof (strictUpper y.2.1) y.2.2 t)
    (measurable_const.div hcC) ((measurable_const.sub (continuous_remainder m t).measurable).div hcC)
    ((ae_cof_ne' β t ht m).mono fun y hy => div_ne_zero (pow_ne_zero _ ht) hy)
    (fun q => Fint β m Φ t c (consMap m q)) (hF.1.comp_measurePreserving hmp)
  have h4 : ∫ q, Fint β m Φ t c (consMap m q) ∂(muRed β m) = _ := h3
  simp only [pointwise_red β m Φ t c ht] at h4
  rw [integral_smul] at h4
  rw [h1, h2, h4, NNReal.smul_def, ← Complex.coe_smul, smul_smul, smul_smul]
  have hconst : ((‖t‖ ^ ((m + 1) * (m + 2)) : ℝ) : ℂ) * ((κ : ℝ) : ℂ) * ((‖t‖ ^ (2 * (m + 1)) : ℝ) : ℂ) = 1 := by
    rw [hκ, Real.coe_toNNReal _ (by positivity), ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    have : ‖t‖ ^ ((m + 1) * (m + 2)) * (‖t‖ ^ ((m + 1) * (m + 1 + 3)))⁻¹ * ‖t‖ ^ (2 * (m + 1)) = 1 := by
      have e : (m + 1) * (m + 1 + 3) = (m + 1) * (m + 2) + 2 * (m + 1) := by ring
      rw [e, pow_add]
      field_simp
    rw [this, Complex.ofReal_one]
  rw [hconst, one_smul]
  rfl

/- English proof (translation)
Establish `h1x : (0 : ℝ) < 1 + x` using `by linarith`. Establish `e : (2 : ℝ) ^ A * (1 + x) ^ (-A) = (2 / (1 + x)) ^ A`. Rewrite using `[Real.rpow_neg h1x.le, Real.div_rpow (by norm_num) h1x.le, div_eq_mul_inv]`. Rewrite using `[e]`. Break down `le_total x 1 with h | h` into its components or cases.

Use `(min_le_left _ _).trans (Real.one_le_rpow ?_ hA)` and prove the remaining obligations. Rewrite using `[le_div_iff₀ h1x]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `(min_le_right _ _).trans ?_` and prove the remaining obligations. Establish `hx0 : (0 : ℝ) < x` using `by linarith`.

Rewrite using `[Real.rpow_neg hx, ← Real.inv_rpow hx]`. Use `Real.rpow_le_rpow (by positivity) ?_ hA` and prove the remaining obligations. Rewrite using `[inv_eq_one_div, div_le_div_iff₀ hx0 h1x]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem min_le_bracket (A x : ℝ) (hA : 0 ≤ A) (hx : 0 ≤ x) :
    min 1 (x ^ (-A)) ≤ 2 ^ A * (1 + x) ^ (-A) := by
  have h1x : (0 : ℝ) < 1 + x := by linarith
  have e : (2 : ℝ) ^ A * (1 + x) ^ (-A) = (2 / (1 + x)) ^ A := by
    rw [Real.rpow_neg h1x.le, Real.div_rpow (by norm_num) h1x.le, div_eq_mul_inv]
  rw [e]
  rcases le_total x 1 with h | h
  · refine (min_le_left _ _).trans (Real.one_le_rpow ?_ hA)
    rw [le_div_iff₀ h1x]; linarith
  · refine (min_le_right _ _).trans ?_
    have hx0 : (0 : ℝ) < x := by linarith
    rw [Real.rpow_neg hx, ← Real.inv_rpow hx]
    refine Real.rpow_le_rpow (by positivity) ?_ hA
    rw [inv_eq_one_div, div_le_div_iff₀ hx0 h1x]; linarith

/- English proof (translation)
Establish `h0 : Integrable (fun q : E => (1 + ‖q‖) ^ (-A)) ν` using `integrable_one_add_norm hA`. Establish `h1 : Integrable (fun q : E => (1 + ‖q‖) ^ (-A)) μ` using `hμ ▸ h0.smul_measure_nnreal`. Establish `h2 : Integrable (fun q : E => (1 + ‖q‖) ^ (-A)) (Measure.map f μ)` using `hmap ▸ h1.smul_measure_nnreal`. Conclude with `hf.integrable_map_iff.1 h2`.
-/
theorem integrable_comp_bracket {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν μ : Measure E) [ν.IsAddHaarMeasure] (k κ : NNReal)
    (hμ : μ = k • ν) (f : E → E) (hf : MeasurableEmbedding f) (hmap : Measure.map f μ = κ • μ) (A : ℝ)
    (hA : (Module.finrank ℝ E : ℝ) < A) : Integrable (fun p => (1 + ‖f p‖) ^ (-A)) μ := by
  have h0 : Integrable (fun q : E => (1 + ‖q‖) ^ (-A)) ν := integrable_one_add_norm hA
  have h1 : Integrable (fun q : E => (1 + ‖q‖) ^ (-A)) μ := hμ ▸ h0.smul_measure_nnreal
  have h2 : Integrable (fun q : E => (1 + ‖q‖) ^ (-A)) (Measure.map f μ) := hmap ▸ h1.smul_measure_nnreal
  exact hf.integrable_map_iff.1 h2

/- English proof (translation)
Use `⟨(Real.toNNReal (‖β‖ / (2 * Real.pi))) ^ Fintype.card (Fin n) * ((Real.toNNReal (‖β‖ / (2 * Real.pi))) ^ Fintype.card (UT n) * (Real.toNNReal (‖β‖ / (2 * Real.pi))) ^ Fintype.card (Fin n)), ?_⟩` and prove the remaining obligations. Unfold `muBlock`. Rewrite using `[muPi_eq, muPi_eq]`. Simplify using `only [ENNReal.smul_def, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, ENNReal.coe_mul, mul_assoc]`. Both sides reduce to the same expression.
-/
theorem muBlock_eq (β : ℂ) (n : ℕ) : ∃ k : NNReal, muBlock β n = k • (volume : Measure (BlockCoord n)) := by
  refine ⟨(Real.toNNReal (‖β‖ / (2 * Real.pi))) ^ Fintype.card (Fin n) *
    ((Real.toNNReal (‖β‖ / (2 * Real.pi))) ^ Fintype.card (UT n) *
      (Real.toNNReal (‖β‖ / (2 * Real.pi))) ^ Fintype.card (Fin n)), ?_⟩
  unfold muBlock
  rw [muPi_eq, muPi_eq]
  simp only [ENNReal.smul_def, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ENNReal.coe_mul, mul_assoc]
  rfl

/- English proof (translation)
Unfold `blk`. Use `Continuous.matrix_reindex (Continuous.matrix_fromBlocks hA ?_ ?_ ?_) _ _` and prove the remaining obligations. Conclude with `continuous_matrix fun i _ => (continuous_apply i).comp hb`. Conclude with `continuous_matrix fun _ j => (continuous_apply j).comp ha`. Conclude with `continuous_matrix fun _ _ => he`.
-/
theorem continuous_blk {α : Type} [TopologicalSpace α] {n : ℕ} {A : α → Matrix (Fin n) (Fin n) ℂ}
    {b a : α → Fin n → ℂ} {e : α → ℂ} (hA : Continuous A) (hb : Continuous b) (ha : Continuous a)
    (he : Continuous e) : Continuous fun p => blk (A p) (b p) (a p) (e p) := by
  unfold blk
  refine Continuous.matrix_reindex (Continuous.matrix_fromBlocks hA ?_ ?_ ?_) _ _
  · exact continuous_matrix fun i _ => (continuous_apply i).comp hb
  · exact continuous_matrix fun _ j => (continuous_apply j).comp ha
  · exact continuous_matrix fun _ _ => he

/- English proof (translation)
Unfold `psi`. Use `fun_prop`.
-/
theorem continuous_psi (β : ℂ) : Continuous (psi β) := by
  unfold psi
  fun_prop

/- English proof (translation)
Unfold `superSum`. Conclude with `continuous_finsetSum _ fun i _ => continuous_id.matrix_elem _ _`.
-/
theorem continuous_superSum (n : ℕ) :
    Continuous (superSum : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → ℂ) := by
  unfold superSum
  exact continuous_finsetSum _ fun i _ => continuous_id.matrix_elem _ _

/- English proof (translation)
Unfold `subSum`. Conclude with `continuous_finsetSum _ fun i _ => continuous_id.matrix_elem _ _`.
-/
theorem continuous_subSum (n : ℕ) :
    Continuous (subSum : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → ℂ) := by
  unfold subSum
  exact continuous_finsetSum _ fun i _ => continuous_id.matrix_elem _ _

/- English proof (translation)
The claim follows from `(norm_le_pi_norm (Z i) j).trans (norm_le_pi_norm Z i)`.
-/
theorem norm_entry_le {s : ℕ} (Z : Mat s) (i j : Fin s) : ‖Z i j‖ ≤ ‖Z‖ :=
  (norm_le_pi_norm (Z i) j).trans (norm_le_pi_norm Z i)

/- English proof (translation)
Establish `hent : ∀ i j, ‖Mcoord t (strictUpper x) B ρ σ i j‖ ≤ ‖Z‖` using `fun i j => by`. Establish `he : Z i j = Mcoord t (strictUpper x) B ρ σ i j` using `by rw [hZ]`. Rewrite using `[← he]`. Conclude with `norm_entry_le Z i j`. Rewrite using `[Prod.norm_def, Prod.norm_def]`.

Use `max_le ?_ (max_le ?_ ?_)` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_` and prove the remaining obligations. Establish `h` using `hent (Fin.last n) j.castSucc`. Rewrite `h` using `[Mcoord, blk_lc]`. Then use the resulting hypothesis. Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun ⟨⟨i, j⟩, hij⟩ => ?_` and prove the remaining obligations.

Establish `h` using `hent i.rev.castSucc j.castSucc`. Establish `hij' : i < j` using `hij`. Rewrite `h` using `[Mcoord, blk_cc, wMat_mul_apply, Fin.rev_rev]`. Simplify `h` using `[strictUpper, hij', Matrix.one_apply, hij'.ne]`. Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_` and prove the remaining obligations.

Establish `h` using `hent i.rev.castSucc (Fin.last n)`. Rewrite `h` using `[Mcoord, blk_cl, wMat_mulVec_apply, Fin.rev_rev]`. Then use the resulting hypothesis.
-/
theorem norm_coord_le {n : ℕ} (t σ : ℂ) (x : UT n → ℂ) (B ρ : Fin n → ℂ) (Z : Mat (n + 1))
    (hZ : Z = Mcoord t (strictUpper x) B ρ σ) : ‖((ρ, x, B) : BlockCoord n)‖ ≤ ‖Z‖ := by
  have hent : ∀ i j, ‖Mcoord t (strictUpper x) B ρ σ i j‖ ≤ ‖Z‖ := fun i j => by
    have he : Z i j = Mcoord t (strictUpper x) B ρ σ i j := by rw [hZ]
    rw [← he]; exact norm_entry_le Z i j
  rw [Prod.norm_def, Prod.norm_def]
  refine max_le ?_ (max_le ?_ ?_)
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
    have h := hent (Fin.last n) j.castSucc
    rwa [Mcoord, blk_lc] at h
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun ⟨⟨i, j⟩, hij⟩ => ?_
    have h := hent i.rev.castSucc j.castSucc
    have hij' : i < j := hij
    rw [Mcoord, blk_cc, wMat_mul_apply, Fin.rev_rev] at h
    simpa [strictUpper, hij', Matrix.one_apply, hij'.ne] using h
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    have h := hent i.rev.castSucc (Fin.last n)
    rwa [Mcoord, blk_cl, wMat_mulVec_apply, Fin.rev_rev] at h

/- English proof (translation)
Establish `hent : ∀ i j, ‖(ptLong d z * G.upper v) i j‖ ≤ ‖Z‖` using `fun i j => by`. Establish `he : Z i j = (ptLong d z * G.upper v) i j` using `by rw [hZ]`. Rewrite using `[← he]`. Conclude with `norm_entry_le Z i j`. Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun ⟨⟨i, j⟩, hij⟩ => ?_` and prove the remaining obligations.

Establish `h` using `hent i.rev j`. Establish `hij' : i < j` using `hij`. Rewrite `h` using `[ptLong, Matrix.smul_mul, Matrix.smul_apply, wMat_mul_apply, Fin.rev_rev]`. Simplify `h` using `[G.upper, strictUpper, hij', Matrix.one_apply, hij'.ne]`.
-/
theorem norm_long_le {d : ℕ} (z : ℂ) (v : UT d → ℂ) (Z : Mat d) (hZ : Z = ptLong d z * G.upper v) :
    ‖z • v‖ ≤ ‖Z‖ := by
  have hent : ∀ i j, ‖(ptLong d z * G.upper v) i j‖ ≤ ‖Z‖ := fun i j => by
    have he : Z i j = (ptLong d z * G.upper v) i j := by rw [hZ]
    rw [← he]; exact norm_entry_le Z i j
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun ⟨⟨i, j⟩, hij⟩ => ?_
  have h := hent i.rev j
  have hij' : i < j := hij
  rw [ptLong, Matrix.smul_mul, Matrix.smul_apply, wMat_mul_apply, Fin.rev_rev] at h
  simpa [G.upper, strictUpper, hij', Matrix.one_apply, hij'.ne] using h

/- English proof (translation)
Rewrite using `[Module.finrank_pi_fintype]`. Simplify using `[Complex.finrank_real_complex, mul_comm]`.
-/
theorem finrank_pi (ι : Type) [Fintype ι] : Module.finrank ℝ (ι → ℂ) = 2 * Fintype.card ι := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

/- English proof (translation)
Rewrite using `[Module.finrank_prod, Module.finrank_prod, finrank_pi, finrank_pi, (dimension_count n).1, Fintype.card_fin]`. Consider the cases of `n with`. Consider the case `zero => rfl`. Consider the case `succ k => simp only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_block (n : ℕ) : Module.finrank ℝ (BlockCoord n) = n * (n + 3) := by
  rw [Module.finrank_prod, Module.finrank_prod, finrank_pi, finrank_pi, (dimension_count n).1, Fintype.card_fin]
  cases n with
  | zero => rfl
  | succ k => simp only [Nat.add_sub_cancel]; ring

/- English proof (translation)
Introduce `m β A K hA V _ _ _ Φ t c ht hc hΦ`. Establish `hA0 : 0 ≤ A`. Establish `: (0 : ℝ) ≤ ((m : ℝ) + 1) * ((m : ℝ) + 4)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb : ∀ Z : Mat (m + 1 + 1), detM Z = (wMat (m + 1)).det * (c * t ^ (m + 1)) → ContinuousAt Φ Z ∧ ‖Φ Z‖ ≤ |K| * (2 ^ A * (1 + ‖Z‖) ^ (-A))`.

Introduce `Z hZ`. Take `⟨h1, h2⟩` from `hΦ Z (by rw [hZ]; exact Set.mem_singleton _)`. Use `⟨h1.continuousAt, ?_⟩` and prove the remaining obligations. Establish `h3` using `h2 0 le_rfl`. Rewrite `h3` using `[norm_iteratedFDeriv_zero]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → |K| * (2 ^ A * (1 + y) ^ (-A)) ≤ |K| * (2 ^ A * (1 + x) ^ (-A))`. Introduce `x y hx hxy`. Use `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (abs_nonneg K)` and prove the remaining obligations. Conclude with `Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)`.

Prove the components needed by the constructor for the conclusion. Use `set M : BlockCoord (m + 1) → Mat (m + 1 + 1) := fun p => lowRow p.1 * ptBlock (m + 1) t c * blk (G.upper p.2.1) p.2.2 0 1 with hM`. Establish `hlow : Continuous (fun p : BlockCoord (m + 1) => lowRow p.1)` using `continuous_blk continuous_const continuous_const continuous_fst continuous_const`. Establish `hup : Continuous (fun p : BlockCoord (m + 1) => blk (G.upper p.2.1) p.2.2 0 1)` using `continuous_blk ((continuous_upper _).comp (continuous_fst.comp continuous_snd)) (continuous_snd.comp continuous_snd) continuous_const continuous_const`. Establish `hMc : Continuous M` using `(hlow.matrix_mul continuous_const).matrix_mul hup`.

Establish `hdet : ∀ p, detM (M p) = (wMat (m + 1)).det * (c * t ^ (m + 1))` using `fun p => det_orbit.1 (m + 1) t c p`. Establish `hcont : Continuous (blockIntegrand β (m + 1) Φ t c)`. Unfold `blockIntegrand`. Use `Continuous.smul ?_ ?_` and prove the remaining obligations. Conclude with `((continuous_psi β).comp ((continuous_subSum _).comp hlow)).mul ((continuous_psi β).comp ((continuous_superSum _).comp hup))`.

Conclude with `continuous_iff_continuousAt.2 fun p => ContinuousAt.comp (f := M) (hb (M p) (hdet p)).1 hMc.continuousAt`. Take `⟨k, hk⟩` from `muBlock_eq β (m + 1)`. Establish `hfr : (Module.finrank ℝ (BlockCoord (m + 1)) : ℝ) < A`. Rewrite using `[finrank_block]`. Establish `e : (((m + 1) * (m + 1 + 3) : ℕ) : ℝ) = ((m : ℝ) + 1) * ((m : ℝ) + 4)` using `by push_cast; ring`.

Rewrite using `[e]`. Conclude with `hA`. Establish `i1 : SecondCountableTopology ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ))` using `inferInstance`. Establish `i2 : BorelSpace ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ))` using `inferInstance`. Establish `i3 : BorelSpace (BlockCoord (m + 1))` using `inferInstance`.

Establish `j1 : (volume : Measure ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ))).IsAddHaarMeasure` using `Measure.prod.instIsAddHaarMeasure _ _`. Establish `j2 : (volume : Measure (BlockCoord (m + 1))).IsAddHaarMeasure` using `Measure.prod.instIsAddHaarMeasure _ _`. Establish `hI` using `integrable_comp_bracket volume (muBlock β (m + 1)) k _ hk (coordMap (m + 1) t) (embedding_coordMap _ t ht) (jacobian (m + 1) β t ht) A hfr`. Use `Integrable.mono' ((hI.const_mul (2 ^ A)).const_mul |K|) hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Establish `hn : ‖blockIntegrand β (m + 1) Φ t c p‖ = ‖Φ (M p)‖`.

Unfold `blockIntegrand`. Rewrite using `[norm_smul, norm_mul, (additive_character_psi β _ 0).2.1, (additive_character_psi β _ 0).2.1, one_mul, one_mul]`. Rewrite using `[hn]`. Use `(hb (M p) (hdet p)).2.trans (hmono _ _ (norm_nonneg _) ?_)` and prove the remaining obligations. Use `norm_coord_le t (c + p.1 ⬝ᵥ (wMat (m + 1) *ᵥ (t • p.2.2))) (t • p.2.1) (t • p.2.2) (rhoOf t p.1 p.2.1) (M p) ?_` and prove the remaining obligations.

Rewrite using `[strictUpper_smul]`. Conclude with `matrix_entries (m + 1) t c p`. Introduce `z hz`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hz` using `[zero_pow (by omega)]`. Conclude with `(mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero hc (pow_ne_zero _ ht))) hz.symm`. Use `set M : (UT (m + 1 + 1) → ℂ) → Mat (m + 1 + 1) := fun v => ptLong (m + 1 + 1) z * G.upper v with hM`. Establish `hMc : Continuous M` using `continuous_const.matrix_mul (continuous_upper _)`. Establish `hdet : ∀ v, detM (M v) = (wMat (m + 1)).det * (c * t ^ (m + 1))`.

Introduce `v`. Establish `h1 : detM (M v) = (wMat (m + 1 + 1)).det * z ^ (m + 2)` using `det_orbit.2 (m + 1 + 1) z v`. Rewrite using `[h1, (det_weyl_matrix (m + 1)).1, hz]`. Establish `h2 : (-1 : ℂ) ^ (m + 1) * (-1) ^ (m + 3) = 1`. Rewrite using `[← pow_add]; exact Even.neg_one_pow ⟨m + 2, by ring⟩`.

Take the linear combination `((wMat (m + 1)).det * (c * t ^ (m + 1))) * h2`. Establish `hcont : Continuous (fun v : UT (m + 1 + 1) → ℂ => psi β (superSum (G.upper v)) • Φ (ptLong (m + 1 + 1) z * G.upper v))`. Use `Continuous.smul ?_ ?_` and prove the remaining obligations. Conclude with `(continuous_psi β).comp ((continuous_superSum _).comp (continuous_upper _))`. Conclude with `continuous_iff_continuousAt.2 fun v => ContinuousAt.comp (f := M) (hb (M v) (hdet v)).1 hMc.continuousAt`.

Establish `hfr : (Module.finrank ℝ (UT (m + 1 + 1) → ℂ) : ℝ) < A`. Rewrite using `[finrank_pi, (dimension_count (m + 1 + 1)).1]`. Establish `e : (((m + 1 + 1) * (m + 1 + 1 - 1) : ℕ) : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1)`. Simplify using `only [Nat.add_sub_cancel]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Establish `: (0 : ℝ) ≤ (m : ℝ)` using `Nat.cast_nonneg m`. Use the polynomial consequences of the given equalities and inequalities. Establish `hI` using `integrable_comp_bracket volume (muPi β (UT (m + 1 + 1))) _ _ (muPi_eq β _) (fun v => z • v) (measurableEmbedding_const_smul₀ hz0) (scale_product_measure β z _ hz0) A hfr`.

Use `Integrable.mono' ((hI.const_mul (2 ^ A)).const_mul |K|) hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Rewrite using `[norm_smul, (additive_character_psi β _ 0).2.1, one_mul]`. Conclude with `(hb (M v) (hdet v)).2.trans (hmono _ _ (norm_nonneg _) (norm_long_le z v (M v) rfl))`.
-/
theorem omConverges : OmConverges := by
  intro m β A K hA V _ _ _ Φ t c ht hc hΦ
  have hA0 : 0 ≤ A := by
    have : (0 : ℝ) ≤ ((m : ℝ) + 1) * ((m : ℝ) + 4) := by positivity
    linarith
  have hb : ∀ Z : Mat (m + 1 + 1), detM Z = (wMat (m + 1)).det * (c * t ^ (m + 1)) →
      ContinuousAt Φ Z ∧ ‖Φ Z‖ ≤ |K| * (2 ^ A * (1 + ‖Z‖) ^ (-A)) := by
    intro Z hZ
    obtain ⟨h1, h2⟩ := hΦ Z (by rw [hZ]; exact Set.mem_singleton _)
    refine ⟨h1.continuousAt, ?_⟩
    have h3 := h2 0 le_rfl
    rw [norm_iteratedFDeriv_zero] at h3
    calc ‖Φ Z‖ ≤ K * min 1 (‖Z‖ ^ (-A)) := h3
      _ ≤ |K| * min 1 (‖Z‖ ^ (-A)) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (le_min zero_le_one (Real.rpow_nonneg (norm_nonneg _) _))
      _ ≤ _ := mul_le_mul_of_nonneg_left (min_le_bracket A _ hA0 (norm_nonneg _)) (abs_nonneg K)
  have hmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → |K| * (2 ^ A * (1 + y) ^ (-A)) ≤ |K| * (2 ^ A * (1 + x) ^ (-A)) := by
    intro x y hx hxy
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (abs_nonneg K)
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  constructor
  · set M : BlockCoord (m + 1) → Mat (m + 1 + 1) :=
      fun p => lowRow p.1 * ptBlock (m + 1) t c * blk (G.upper p.2.1) p.2.2 0 1 with hM
    have hlow : Continuous (fun p : BlockCoord (m + 1) => lowRow p.1) :=
      continuous_blk continuous_const continuous_const continuous_fst continuous_const
    have hup : Continuous (fun p : BlockCoord (m + 1) => blk (G.upper p.2.1) p.2.2 0 1) :=
      continuous_blk ((continuous_upper _).comp (continuous_fst.comp continuous_snd))
        (continuous_snd.comp continuous_snd) continuous_const continuous_const
    have hMc : Continuous M := (hlow.matrix_mul continuous_const).matrix_mul hup
    have hdet : ∀ p, detM (M p) = (wMat (m + 1)).det * (c * t ^ (m + 1)) :=
      fun p => det_orbit.1 (m + 1) t c p
    have hcont : Continuous (blockIntegrand β (m + 1) Φ t c) := by
      unfold blockIntegrand
      refine Continuous.smul ?_ ?_
      · exact ((continuous_psi β).comp ((continuous_subSum _).comp hlow)).mul
          ((continuous_psi β).comp ((continuous_superSum _).comp hup))
      · exact continuous_iff_continuousAt.2 fun p =>
          ContinuousAt.comp (f := M) (hb (M p) (hdet p)).1 hMc.continuousAt
    obtain ⟨k, hk⟩ := muBlock_eq β (m + 1)
    have hfr : (Module.finrank ℝ (BlockCoord (m + 1)) : ℝ) < A := by
      rw [finrank_block]
      have e : (((m + 1) * (m + 1 + 3) : ℕ) : ℝ) = ((m : ℝ) + 1) * ((m : ℝ) + 4) := by push_cast; ring
      rw [e]; exact hA
    have i1 : SecondCountableTopology ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ)) := inferInstance
    have i2 : BorelSpace ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ)) := inferInstance
    have i3 : BorelSpace (BlockCoord (m + 1)) := inferInstance
    have j1 : (volume : Measure ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ))).IsAddHaarMeasure :=
      Measure.prod.instIsAddHaarMeasure _ _
    have j2 : (volume : Measure (BlockCoord (m + 1))).IsAddHaarMeasure :=
      Measure.prod.instIsAddHaarMeasure _ _
    have hI := integrable_comp_bracket volume (muBlock β (m + 1)) k _ hk (coordMap (m + 1) t)
      (embedding_coordMap _ t ht) (jacobian (m + 1) β t ht) A hfr
    refine Integrable.mono' ((hI.const_mul (2 ^ A)).const_mul |K|) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    have hn : ‖blockIntegrand β (m + 1) Φ t c p‖ = ‖Φ (M p)‖ := by
      unfold blockIntegrand
      rw [norm_smul, norm_mul, (additive_character_psi β _ 0).2.1, (additive_character_psi β _ 0).2.1, one_mul, one_mul]
    rw [hn]
    refine (hb (M p) (hdet p)).2.trans (hmono _ _ (norm_nonneg _) ?_)
    refine norm_coord_le t (c + p.1 ⬝ᵥ (wMat (m + 1) *ᵥ (t • p.2.2))) (t • p.2.1) (t • p.2.2)
      (rhoOf t p.1 p.2.1) (M p) ?_
    rw [strictUpper_smul]
    exact matrix_entries (m + 1) t c p
  · intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hz
      exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero hc (pow_ne_zero _ ht))) hz.symm
    set M : (UT (m + 1 + 1) → ℂ) → Mat (m + 1 + 1) := fun v => ptLong (m + 1 + 1) z * G.upper v with hM
    have hMc : Continuous M := continuous_const.matrix_mul (continuous_upper _)
    have hdet : ∀ v, detM (M v) = (wMat (m + 1)).det * (c * t ^ (m + 1)) := by
      intro v
      have h1 : detM (M v) = (wMat (m + 1 + 1)).det * z ^ (m + 2) := det_orbit.2 (m + 1 + 1) z v
      rw [h1, (det_weyl_matrix (m + 1)).1, hz]
      have h2 : (-1 : ℂ) ^ (m + 1) * (-1) ^ (m + 3) = 1 := by
        rw [← pow_add]; exact Even.neg_one_pow ⟨m + 2, by ring⟩
      linear_combination ((wMat (m + 1)).det * (c * t ^ (m + 1))) * h2
    have hcont : Continuous (fun v : UT (m + 1 + 1) → ℂ =>
        psi β (superSum (G.upper v)) • Φ (ptLong (m + 1 + 1) z * G.upper v)) := by
      refine Continuous.smul ?_ ?_
      · exact (continuous_psi β).comp ((continuous_superSum _).comp (continuous_upper _))
      · exact continuous_iff_continuousAt.2 fun v =>
          ContinuousAt.comp (f := M) (hb (M v) (hdet v)).1 hMc.continuousAt
    have hfr : (Module.finrank ℝ (UT (m + 1 + 1) → ℂ) : ℝ) < A := by
      rw [finrank_pi, (dimension_count (m + 1 + 1)).1]
      have e : (((m + 1 + 1) * (m + 1 + 1 - 1) : ℕ) : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
        simp only [Nat.add_sub_cancel]; push_cast; ring
      rw [e]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith
    have hI := integrable_comp_bracket volume (muPi β (UT (m + 1 + 1))) _ _ (muPi_eq β _)
      (fun v => z • v) (measurableEmbedding_const_smul₀ hz0) (scale_product_measure β z _ hz0) A hfr
    refine Integrable.mono' ((hI.const_mul (2 ^ A)).const_mul |K|) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => ?_)
    rw [norm_smul, (additive_character_psi β _ 0).2.1, one_mul]
    exact (hb (M v) (hdet v)).2.trans (hmono _ _ (norm_nonneg _) (norm_long_le z v (M v) rfl))

end Formalism.FourierDecayAlt.P.G7

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `G7.omReduced`.
-/
theorem orbital_integral_reduced : Formalism.FourierDecayAlt.G.OmReduced := G7.omReduced

/- English proof (translation)
The claim follows from `G7.omConverges`.
-/
theorem orbital_integral_converges_abs : Formalism.FourierDecayAlt.G.OmConverges := G7.omConverges

end Formalism.FourierDecayAlt.P
