import Mathlib
import GroundTheory.AutomorphicForms.RealIwasawaSubgroups

namespace GroundTheory.Automorphic

open Matrix Set MeasureTheory Measure
open scoped ComplexOrder NNReal ENNReal

set_option linter.unusedSectionVars false

section Det

/- English proof (translation)
Take `⟨c, -, hc⟩` from `Polynomial.isUnit_iff.1 (isUnit_charpolyRev_of_isNilpotent hM)`. Establish `h0` using `eval_charpolyRev (M := M)`. Rewrite `h0` using `[← hc, Polynomial.eval_C]`. Establish `h1 : M.charpolyRev = 1` using `by rw [← hc, h0, Polynomial.C_1]`. Establish `h2` using `congrArg (Polynomial.eval (-1)) h1`.

Rewrite `h2` using `[charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det, map_one]`. Rewrite using `[← h2]`. Use `congr 1`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij]`.
-/
theorem det_one_add_of_isNilpotent {m K : Type*} [Fintype m] [DecidableEq m] [Field K]
    {M : Matrix m m K} (hM : IsNilpotent M) : (1 + M).det = 1 := by
  obtain ⟨c, -, hc⟩ := Polynomial.isUnit_iff.1 (isUnit_charpolyRev_of_isNilpotent hM)
  have h0 := eval_charpolyRev (M := M)
  rw [← hc, Polynomial.eval_C] at h0
  have h1 : M.charpolyRev = 1 := by rw [← hc, h0, Polynomial.C_1]
  have h2 := congrArg (Polynomial.eval (-1)) h1
  rw [charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det, map_one] at h2
  rw [← h2]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/- English proof (translation)
Set `b` to `Module.finBasis K E`. Rewrite using `[← LinearMap.det_toMatrix b, map_add, LinearMap.toMatrix_one]`. Apply `det_one_add_of_isNilpotent` to reduce the goal to its premises. Take `⟨k, hk⟩` from `hf`. Conclude with `⟨k, by rw [LinearMap.toMatrix_pow, hk, map_zero]⟩`.
-/
theorem det_one_add_linearMap_of_isNilpotent {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] {f : E →ₗ[K] E} (hf : IsNilpotent f) : LinearMap.det (1 + f) = 1 := by
  let b := Module.finBasis K E
  rw [← LinearMap.det_toMatrix b, map_add, LinearMap.toMatrix_one]
  apply det_one_add_of_isNilpotent
  obtain ⟨k, hk⟩ := hf
  exact ⟨k, by rw [LinearMap.toMatrix_pow, hk, map_zero]⟩

end Det

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]

section Translations

def unipotentLeftLinear (w : StrictUpperIndex n → 𝕜) :
    (StrictUpperIndex n → 𝕜) →ₗ[𝕜] (StrictUpperIndex n → 𝕜) where
  toFun v := strictUpperCoords (strictUpperMatrix w * strictUpperMatrix v)
  map_add' v v' := by
    rw [strictUpperMatrix_add, Matrix.mul_add, strictUpperCoords_add]
  map_smul' c v := by
    rw [strictUpperMatrix_smul, Matrix.mul_smul, strictUpperCoords_smul, RingHom.id_apply]

def unipotentRightLinear (w : StrictUpperIndex n → 𝕜) :
    (StrictUpperIndex n → 𝕜) →ₗ[𝕜] (StrictUpperIndex n → 𝕜) where
  toFun v := strictUpperCoords (strictUpperMatrix v * strictUpperMatrix w)
  map_add' v v' := by
    rw [strictUpperMatrix_add, Matrix.add_mul, strictUpperCoords_add]
  map_smul' c v := by
    rw [strictUpperMatrix_smul, Matrix.smul_mul, strictUpperCoords_smul, RingHom.id_apply]

/- English proof (translation)
The claim follows from `(isStrictUpper_strictUpperMatrix v).mul_right (isStrictUpper_strictUpperMatrix w).isUpperTriangular`.
-/
theorem isStrictUpper_mul (v w : StrictUpperIndex n → 𝕜) :
    IsStrictUpper (strictUpperMatrix v * strictUpperMatrix w) :=
  (isStrictUpper_strictUpperMatrix v).mul_right (isStrictUpper_strictUpperMatrix w).isUpperTriangular

/- English proof (translation)
Proceed by induction on `k generalizing v with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, Module.End.mul_apply, ih]`. Use `show strictUpperCoords (strictUpperMatrix w ^ k * strictUpperMatrix (strictUpperCoords (strictUpperMatrix w * strictUpperMatrix v))) = _`.

Rewrite using `[strictUpperMatrix_strictUpperCoords (isStrictUpper_mul w v), ← Matrix.mul_assoc, ← pow_succ]`.
-/
theorem unipotentLeftLinear_pow_apply (w : StrictUpperIndex n → 𝕜) (k : ℕ)
    (v : StrictUpperIndex n → 𝕜) :
    (unipotentLeftLinear w ^ k) v = strictUpperCoords (strictUpperMatrix w ^ k * strictUpperMatrix v) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    show strictUpperCoords (strictUpperMatrix w ^ k *
      strictUpperMatrix (strictUpperCoords (strictUpperMatrix w * strictUpperMatrix v))) = _
    rw [strictUpperMatrix_strictUpperCoords (isStrictUpper_mul w v), ← Matrix.mul_assoc, ← pow_succ]

/- English proof (translation)
Proceed by induction on `k generalizing v with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, Module.End.mul_apply, ih]`. Use `show strictUpperCoords ( strictUpperMatrix (strictUpperCoords (strictUpperMatrix v * strictUpperMatrix w)) * strictUpperMatrix w ^ k) = _`.

Rewrite using `[strictUpperMatrix_strictUpperCoords (isStrictUpper_mul v w), Matrix.mul_assoc, ← pow_succ']`.
-/
theorem unipotentRightLinear_pow_apply (w : StrictUpperIndex n → 𝕜) (k : ℕ)
    (v : StrictUpperIndex n → 𝕜) :
    (unipotentRightLinear w ^ k) v = strictUpperCoords (strictUpperMatrix v * strictUpperMatrix w ^ k) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    show strictUpperCoords (
      strictUpperMatrix (strictUpperCoords (strictUpperMatrix v * strictUpperMatrix w)) *
        strictUpperMatrix w ^ k) = _
    rw [strictUpperMatrix_strictUpperCoords (isStrictUpper_mul v w), Matrix.mul_assoc, ← pow_succ']

/- English proof (translation)
Proceed by induction on `k generalizing v with`. Consider the case `zero => rfl`. Consider the case `succ k ih => rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]`. Both sides reduce to the same expression.
-/
theorem restrictScalars_pow_apply (L : (StrictUpperIndex n → 𝕜) →ₗ[𝕜] (StrictUpperIndex n → 𝕜))
    (k : ℕ) (v : StrictUpperIndex n → 𝕜) : ((L.restrictScalars ℝ) ^ k) v = (L ^ k) v := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]; rfl

/- English proof (translation)
Use `⟨Fintype.card n, LinearMap.ext fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[restrictScalars_pow_apply, unipotentLeftLinear_pow_apply, (isStrictUpper_strictUpperMatrix w).pow_card_eq_zero, Matrix.zero_mul]`. Both sides reduce to the same expression.
-/
theorem isNilpotent_unipotentLeftLinear (w : StrictUpperIndex n → 𝕜) :
    IsNilpotent ((unipotentLeftLinear w).restrictScalars ℝ) := by
  refine ⟨Fintype.card n, LinearMap.ext fun v => ?_⟩
  rw [restrictScalars_pow_apply, unipotentLeftLinear_pow_apply,
    (isStrictUpper_strictUpperMatrix w).pow_card_eq_zero, Matrix.zero_mul]
  rfl

/- English proof (translation)
Use `⟨Fintype.card n, LinearMap.ext fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[restrictScalars_pow_apply, unipotentRightLinear_pow_apply, (isStrictUpper_strictUpperMatrix w).pow_card_eq_zero, Matrix.mul_zero]`. Both sides reduce to the same expression.
-/
theorem isNilpotent_unipotentRightLinear (w : StrictUpperIndex n → 𝕜) :
    IsNilpotent ((unipotentRightLinear w).restrictScalars ℝ) := by
  refine ⟨Fintype.card n, LinearMap.ext fun v => ?_⟩
  rw [restrictScalars_pow_apply, unipotentRightLinear_pow_apply, (isStrictUpper_strictUpperMatrix w).pow_card_eq_zero,
    Matrix.mul_zero]
  rfl

/- English proof (translation)
Rewrite using `[unipotentOfCoords_mul]`. Use `congr 1`. Use `show w + v + strictUpperCoords (strictUpperMatrix w * strictUpperMatrix v) = w + (v + strictUpperCoords (strictUpperMatrix w * strictUpperMatrix v))`. Rewrite using `[add_assoc]`.
-/
theorem unipotentOfCoords_mul_eq_left (w v : StrictUpperIndex n → 𝕜) :
    unipotentOfCoords w * unipotentOfCoords v =
      unipotentOfCoords (w + (1 + (unipotentLeftLinear w).restrictScalars ℝ) v) := by
  rw [unipotentOfCoords_mul]
  congr 1
  show w + v + strictUpperCoords (strictUpperMatrix w * strictUpperMatrix v) =
    w + (v + strictUpperCoords (strictUpperMatrix w * strictUpperMatrix v))
  rw [add_assoc]

/- English proof (translation)
Rewrite using `[unipotentOfCoords_mul]`. Use `congr 1`. Use `show v + w + strictUpperCoords (strictUpperMatrix v * strictUpperMatrix w) = w + (v + strictUpperCoords (strictUpperMatrix v * strictUpperMatrix w))`. Normalize the expressions using the abelian group laws.
-/
theorem unipotentOfCoords_mul_eq_right (v w : StrictUpperIndex n → 𝕜) :
    unipotentOfCoords v * unipotentOfCoords w =
      unipotentOfCoords (w + (1 + (unipotentRightLinear w).restrictScalars ℝ) v) := by
  rw [unipotentOfCoords_mul]
  congr 1
  show v + w + strictUpperCoords (strictUpperMatrix v * strictUpperMatrix w) =
    w + (v + strictUpperCoords (strictUpperMatrix v * strictUpperMatrix w))
  abel

noncomputable def diagScaleLinear (a : PosDiag n) :
    (StrictUpperIndex n → 𝕜) →ₗ[ℝ] (StrictUpperIndex n → 𝕜) :=
  LinearMap.pi fun p => ((a.1 p.1.1 / a.1 p.1.2) • LinearMap.id).comp (LinearMap.proj p)

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `[diagScaleLinear, RCLike.real_smul_eq_coe_mul]`.
-/
theorem diagScaleLinear_apply (a : PosDiag n) (v : StrictUpperIndex n → 𝕜) :
    diagScaleLinear a v = fun p => ((a.1 p.1.1 / a.1 p.1.2 : ℝ) : 𝕜) * v p := by
  funext p
  simp [diagScaleLinear, RCLike.real_smul_eq_coe_mul]

/- English proof (translation)
Rewrite using `[diagScaleLinear, LinearMap.det_pi, iwasawaDelta_diagPosOf]`. Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.det_smul, LinearMap.det_id, mul_one]`.
-/
theorem det_diagScaleLinear (a : PosDiag n) :
    LinearMap.det (diagScaleLinear (𝕜 := 𝕜) a) = (iwasawaDelta (diagPosOf a : GL n 𝕜) : ℝ) := by
  rw [diagScaleLinear, LinearMap.det_pi, iwasawaDelta_diagPosOf]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one]

end Translations

section Topology

instance : LocallyCompactSpace (upperUnipotentSubgroup n 𝕜) :=
  (unipotentCoordsHomeomorph (𝕜 := 𝕜) (n := n)).symm.isOpenEmbedding.locallyCompactSpace

instance : SecondCountableTopology (upperUnipotentSubgroup n 𝕜) :=
  (unipotentCoordsHomeomorph (𝕜 := 𝕜) (n := n)).symm.isEmbedding.secondCountableTopology

/- English proof (translation)
Rewrite using `[setOf_forall]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)`.
-/
theorem isOpen_posDiag : IsOpen {a : n → ℝ | ∀ i, 0 < a i} := by
  rw [setOf_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)

instance : LocallyCompactSpace (PosDiag n) :=
  isOpen_posDiag.locallyCompactSpace

instance : LocallyCompactSpace (diagPosSubgroup n 𝕜) :=
  (diagPosHomeomorph (𝕜 := 𝕜) (n := n)).symm.isOpenEmbedding.locallyCompactSpace

instance : SecondCountableTopology (diagPosSubgroup n 𝕜) :=
  (diagPosHomeomorph (𝕜 := 𝕜) (n := n)).symm.isEmbedding.secondCountableTopology

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

instance : LocallyCompactSpace (upperPosSubgroup n 𝕜) :=
  (diagUnipotentHomeomorph (𝕜 := 𝕜) (n := n)).symm.isOpenEmbedding.locallyCompactSpace

instance : SecondCountableTopology (upperPosSubgroup n 𝕜) :=
  (diagUnipotentHomeomorph (𝕜 := 𝕜) (n := n)).symm.isEmbedding.secondCountableTopology

end Topology

section Haar

variable [MeasurableSpace (GL n 𝕜)] [BorelSpace (GL n 𝕜)]

noncomputable def unipotentLebesgue : Measure (upperUnipotentSubgroup n 𝕜) :=
  Measure.map unipotentCoordsHomeomorph (Measure.addHaar : Measure (StrictUpperIndex n → 𝕜))

/- English proof (translation)
Establish `hLc : Continuous L` using `LinearMap.continuous_of_finiteDimensional L`. Establish `e : (fun v => w + L v) = (fun v => w + v) ∘ L` using `rfl`. Rewrite using `[e, ← Measure.map_map (measurable_const_add w) hLc.measurable, map_linearMap_addHaar_eq_smul_addHaar μ (by rw [hL]; exact one_ne_zero), hL, inv_one, abs_one, ENNReal.ofReal_one, one_smul, map_add_left_eq_self]`.
-/
theorem map_affine_addHaar_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (w : E) (L : E →ₗ[ℝ] E) (hL : LinearMap.det L = 1) :
    Measure.map (fun v => w + L v) μ = μ := by
  have hLc : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have e : (fun v => w + L v) = (fun v => w + v) ∘ L := rfl
  rw [e, ← Measure.map_map (measurable_const_add w) hLc.measurable,
    map_linearMap_addHaar_eq_smul_addHaar μ (by rw [hL]; exact one_ne_zero), hL, inv_one, abs_one,
    ENNReal.ofReal_one, one_smul, map_add_left_eq_self]

/- English proof (translation)
Use `set w := unipotentCoordsHomeomorph.symm u`. Establish `hu : u = unipotentCoordsHomeomorph w` using `(unipotentCoordsHomeomorph.apply_symm_apply u).symm`. Establish `e : (u * ·) ∘ unipotentCoordsHomeomorph = unipotentCoordsHomeomorph ∘ (fun v => w + (1 + (unipotentLeftLinear w).restrictScalars ℝ) v)`. Use function extensionality and compare the values at `v`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [Function.comp_apply, Subgroup.coe_mul, hu, coe_unipotentCoordsHomeomorph]`. Conclude with `unipotentOfCoords_mul_eq_left w v`. Establish `hT : Measurable (fun v : StrictUpperIndex n → 𝕜 => w + (1 + (unipotentLeftLinear w).restrictScalars ℝ) v)` using `(continuous_const.add (LinearMap.continuous_of_finiteDimensional _)).measurable`. Rewrite using `[unipotentLebesgue, Measure.map_map (measurable_const_mul u) unipotentCoordsHomeomorph.measurable, e, ← Measure.map_map unipotentCoordsHomeomorph.measurable hT, map_affine_addHaar_eq _ w _ (det_one_add_linearMap_of_isNilpotent (isNilpotent_unipotentLeftLinear w))]`.
-/
theorem unipotentLebesgue_map_mul_left (u : upperUnipotentSubgroup n 𝕜) :
    Measure.map (u * ·) (unipotentLebesgue (𝕜 := 𝕜) (n := n)) = unipotentLebesgue := by
  set w := unipotentCoordsHomeomorph.symm u
  have hu : u = unipotentCoordsHomeomorph w := (unipotentCoordsHomeomorph.apply_symm_apply u).symm
  have e : (u * ·) ∘ unipotentCoordsHomeomorph = unipotentCoordsHomeomorph ∘
      (fun v => w + (1 + (unipotentLeftLinear w).restrictScalars ℝ) v) := by
    funext v
    apply Subtype.ext
    simp only [Function.comp_apply, Subgroup.coe_mul, hu, coe_unipotentCoordsHomeomorph]
    exact unipotentOfCoords_mul_eq_left w v
  have hT : Measurable (fun v : StrictUpperIndex n → 𝕜 =>
      w + (1 + (unipotentLeftLinear w).restrictScalars ℝ) v) :=
    (continuous_const.add (LinearMap.continuous_of_finiteDimensional _)).measurable
  rw [unipotentLebesgue, Measure.map_map (measurable_const_mul u)
    unipotentCoordsHomeomorph.measurable, e, ← Measure.map_map unipotentCoordsHomeomorph.measurable hT,
    map_affine_addHaar_eq _ w _ (det_one_add_linearMap_of_isNilpotent
      (isNilpotent_unipotentLeftLinear w))]

/- English proof (translation)
Use `set w := unipotentCoordsHomeomorph.symm u`. Establish `hu : u = unipotentCoordsHomeomorph w` using `(unipotentCoordsHomeomorph.apply_symm_apply u).symm`. Establish `e : (· * u) ∘ unipotentCoordsHomeomorph = unipotentCoordsHomeomorph ∘ (fun v => w + (1 + (unipotentRightLinear w).restrictScalars ℝ) v)`. Use function extensionality and compare the values at `v`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [Function.comp_apply, Subgroup.coe_mul, hu, coe_unipotentCoordsHomeomorph]`. Conclude with `unipotentOfCoords_mul_eq_right v w`. Establish `hT : Measurable (fun v : StrictUpperIndex n → 𝕜 => w + (1 + (unipotentRightLinear w).restrictScalars ℝ) v)` using `(continuous_const.add (LinearMap.continuous_of_finiteDimensional _)).measurable`. Rewrite using `[unipotentLebesgue, Measure.map_map (measurable_mul_const u) unipotentCoordsHomeomorph.measurable, e, ← Measure.map_map unipotentCoordsHomeomorph.measurable hT, map_affine_addHaar_eq _ w _ (det_one_add_linearMap_of_isNilpotent (isNilpotent_unipotentRightLinear w))]`.
-/
theorem unipotentLebesgue_map_mul_right (u : upperUnipotentSubgroup n 𝕜) :
    Measure.map (· * u) (unipotentLebesgue (𝕜 := 𝕜) (n := n)) = unipotentLebesgue := by
  set w := unipotentCoordsHomeomorph.symm u
  have hu : u = unipotentCoordsHomeomorph w := (unipotentCoordsHomeomorph.apply_symm_apply u).symm
  have e : (· * u) ∘ unipotentCoordsHomeomorph = unipotentCoordsHomeomorph ∘
      (fun v => w + (1 + (unipotentRightLinear w).restrictScalars ℝ) v) := by
    funext v
    apply Subtype.ext
    simp only [Function.comp_apply, Subgroup.coe_mul, hu, coe_unipotentCoordsHomeomorph]
    exact unipotentOfCoords_mul_eq_right v w
  have hT : Measurable (fun v : StrictUpperIndex n → 𝕜 =>
      w + (1 + (unipotentRightLinear w).restrictScalars ℝ) v) :=
    (continuous_const.add (LinearMap.continuous_of_finiteDimensional _)).measurable
  rw [unipotentLebesgue, Measure.map_map (measurable_mul_const u)
    unipotentCoordsHomeomorph.measurable, e, ← Measure.map_map unipotentCoordsHomeomorph.measurable hT,
    map_affine_addHaar_eq _ w _ (det_one_add_linearMap_of_isNilpotent
      (isNilpotent_unipotentRightLinear w))]

instance isHaarMeasure_unipotentLebesgue : (unipotentLebesgue (𝕜 := 𝕜) (n := n)).IsHaarMeasure where
  map_mul_left_eq_self u := unipotentLebesgue_map_mul_left u
  lt_top_of_isCompact := by
    have := IsFiniteMeasureOnCompacts.map (Measure.addHaar : Measure (StrictUpperIndex n → 𝕜))
      (unipotentCoordsHomeomorph (𝕜 := 𝕜) (n := n))
    exact this.lt_top_of_isCompact
  open_pos U hU hne := by
    rw [unipotentLebesgue, Measure.map_apply unipotentCoordsHomeomorph.measurable hU.measurableSet]
    exact (hU.preimage unipotentCoordsHomeomorph.continuous).measure_ne_zero _
      (hne.preimage unipotentCoordsHomeomorph.surjective)

instance isMulRightInvariant_unipotentLebesgue :
    (unipotentLebesgue (𝕜 := 𝕜) (n := n)).IsMulRightInvariant :=
  ⟨unipotentLebesgue_map_mul_right⟩

/- English proof (translation)
Use `⟨haarScalarFactor μ unipotentLebesgue, ?_, isMulLeftInvariant_eq_smul μ _⟩` and prove the remaining obligations. Introduce `h0`. Establish `h` using `isMulLeftInvariant_eq_smul μ (unipotentLebesgue (𝕜 := 𝕜) (n := n))`. Rewrite `h` using `[h0, zero_smul]`. Conclude with `(IsHaarMeasure.toIsOpenPosMeasure (μ := μ)).open_pos univ isOpen_univ univ_nonempty (by rw [h]; rfl)`.
-/
theorem exists_eq_smul_unipotentLebesgue (μ : Measure (upperUnipotentSubgroup n 𝕜))
    [μ.IsHaarMeasure] : ∃ c : ℝ≥0, c ≠ 0 ∧ μ = c • unipotentLebesgue := by
  refine ⟨haarScalarFactor μ unipotentLebesgue, ?_, isMulLeftInvariant_eq_smul μ _⟩
  intro h0
  have h := isMulLeftInvariant_eq_smul μ (unipotentLebesgue (𝕜 := 𝕜) (n := n))
  rw [h0, zero_smul] at h
  exact (IsHaarMeasure.toIsOpenPosMeasure (μ := μ)).open_pos univ isOpen_univ univ_nonempty
    (by rw [h]; rfl)

instance isMulRightInvariant_upperUnipotent (μ : Measure (upperUnipotentSubgroup n 𝕜))
    [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  obtain ⟨c, -, rfl⟩ := exists_eq_smul_unipotentLebesgue μ
  infer_instance

def diagConj (a : diagPosSubgroup n 𝕜) (u : upperUnipotentSubgroup n 𝕜) :
    upperUnipotentSubgroup n 𝕜 :=
  ⟨(a : GL n 𝕜) * u * (a : GL n 𝕜)⁻¹, by
    obtain ⟨x, rfl⟩ := diagPosHomeomorph.surjective a
    obtain ⟨v, rfl⟩ := unipotentCoordsHomeomorph.surjective u
    rw [coe_diagPosHomeomorph, coe_unipotentCoordsHomeomorph, conj_unipotentOfCoords]
    exact unipotentOfCoords_mem _⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_diagConj (a : diagPosSubgroup n 𝕜) (u : upperUnipotentSubgroup n 𝕜) :
    ((diagConj a u : upperUnipotentSubgroup n 𝕜) : GL n 𝕜) = (a : GL n 𝕜) * u * (a : GL n 𝕜)⁻¹ :=
  rfl

/- English proof (translation)
The claim follows from `Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _`.
-/
theorem continuous_diagConj (a : diagPosSubgroup n 𝕜) :
    Continuous (diagConj a) :=
  Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

/- English proof (translation)
Take `⟨x, rfl⟩` from `diagPosHomeomorph.surjective a`. Establish `e : diagConj (diagPosHomeomorph x) ∘ unipotentCoordsHomeomorph = unipotentCoordsHomeomorph ∘ diagScaleLinear (𝕜` using `𝕜) x := by`. Use function extensionality and compare the values at `v`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Function.comp_apply, coe_diagConj, coe_diagPosHomeomorph, coe_unipotentCoordsHomeomorph, diagScaleLinear_apply]`.

Conclude with `conj_unipotentOfCoords x v`. Establish `hδ : (iwasawaDelta (diagPosOf x : GL n 𝕜) : ℝ) ≠ 0` using `NNReal.coe_ne_zero.2 (iwasawaDelta_ne_zero (diagPosSubgroup_le_upperPosSubgroup (diagPosOf_mem x)))`. Rewrite using `[unipotentLebesgue, Measure.map_map (continuous_diagConj _).measurable unipotentCoordsHomeomorph.measurable, e, ← Measure.map_map unipotentCoordsHomeomorph.measurable (LinearMap.continuous_of_finiteDimensional _).measurable, map_linearMap_addHaar_eq_smul_addHaar _ (by rw [det_dia …`. Use `congr 1`. Rewrite using `[abs_of_pos (inv_pos.2 (lt_of_le_of_ne (NNReal.coe_nonneg _) hδ.symm)), ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal, ENNReal.coe_inv (NNReal.coe_ne_zero.1 hδ)]`.
-/
theorem unipotentLebesgue_map_diagConj (a : diagPosSubgroup n 𝕜) :
    Measure.map (diagConj a) (unipotentLebesgue (𝕜 := 𝕜) (n := n)) =
      ((iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞))⁻¹ • unipotentLebesgue := by
  obtain ⟨x, rfl⟩ := diagPosHomeomorph.surjective a
  have e : diagConj (diagPosHomeomorph x) ∘ unipotentCoordsHomeomorph =
      unipotentCoordsHomeomorph ∘ diagScaleLinear (𝕜 := 𝕜) x := by
    funext v
    apply Subtype.ext
    simp only [Function.comp_apply, coe_diagConj, coe_diagPosHomeomorph,
      coe_unipotentCoordsHomeomorph, diagScaleLinear_apply]
    exact conj_unipotentOfCoords x v
  have hδ : (iwasawaDelta (diagPosOf x : GL n 𝕜) : ℝ) ≠ 0 :=
    NNReal.coe_ne_zero.2 (iwasawaDelta_ne_zero (diagPosSubgroup_le_upperPosSubgroup (diagPosOf_mem x)))
  rw [unipotentLebesgue, Measure.map_map (continuous_diagConj _).measurable
    unipotentCoordsHomeomorph.measurable, e, ← Measure.map_map unipotentCoordsHomeomorph.measurable
    (LinearMap.continuous_of_finiteDimensional _).measurable,
    map_linearMap_addHaar_eq_smul_addHaar _ (by rw [det_diagScaleLinear]; exact hδ),
    Measure.map_smul, det_diagScaleLinear, coe_diagPosHomeomorph]
  congr 1
  rw [abs_of_pos (inv_pos.2 (lt_of_le_of_ne (NNReal.coe_nonneg _) hδ.symm)), ← NNReal.coe_inv,
    ENNReal.ofReal_coe_nnreal, ENNReal.coe_inv (NNReal.coe_ne_zero.1 hδ)]

/- English proof (translation)
Take `⟨c, -, rfl⟩` from `exists_eq_smul_unipotentLebesgue μ`. Rewrite using `[Measure.map_smul, unipotentLebesgue_map_diagConj, smul_comm]`.
-/
theorem map_diagConj_haar (μ : Measure (upperUnipotentSubgroup n 𝕜)) [μ.IsHaarMeasure]
    (a : diagPosSubgroup n 𝕜) :
    Measure.map (diagConj a) μ = ((iwasawaDelta (a : GL n 𝕜) : ℝ≥0∞))⁻¹ • μ := by
  obtain ⟨c, -, rfl⟩ := exists_eq_smul_unipotentLebesgue μ
  rw [Measure.map_smul, unipotentLebesgue_map_diagConj, smul_comm]

end Haar

end GroundTheory.Automorphic
