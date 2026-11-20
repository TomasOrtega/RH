import Mathlib
import GroundTheory.AutomorphicForms.GLnLocal

namespace GroundTheory.Automorphic

open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise

set_option linter.unusedSectionVars false

namespace Measures

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

section Topology

/- English proof (translation)
Take `⟨g, hg⟩` from `IsCyclic.exists_generator (α := (ValueGroupWithZero F)ˣ)`. Use `Function.Surjective.countable (f := fun k : ℤ => g ^ k) fun x => ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `Subgroup.mem_zpowers_iff.1 (hg x)`. Conclude with `⟨k, hk⟩`.
-/
theorem countable_units_valueGroup : Countable (ValueGroupWithZero F)ˣ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ValueGroupWithZero F)ˣ)
  refine Function.Surjective.countable (f := fun k : ℤ => g ^ k) fun x => ?_
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
  exact ⟨k, hk⟩

/- English proof (translation)
Set `` to `IsTopologicalAddGroup.rightUniformSpace F`. Use `isUniformAddGroup_of_addCommGroup (G := F)` as an intermediate fact. Use `countable_units_valueGroup F` as an intermediate fact. Establish `: (𝓝 (0 : F)).IsCountablyGenerated` using `(IsValuativeTopology.hasBasis_nhds_zero F).isCountablyGenerated`. Establish `: (uniformity F).IsCountablyGenerated`.

Rewrite using `[uniformity_eq_comap_nhds_zero F]`. Use `infer_instance`. Conclude with `UniformSpace.metrizableSpace`.
-/
theorem metrizableSpace : TopologicalSpace.MetrizableSpace F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have := countable_units_valueGroup F
  have : (𝓝 (0 : F)).IsCountablyGenerated :=
    (IsValuativeTopology.hasBasis_nhds_zero F).isCountablyGenerated
  have : (uniformity F).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero F]
    infer_instance
  exact UniformSpace.metrizableSpace

/- English proof (translation)
Use `⟨⟨fun k : ℕ => {x | valuation F x ≤ (valuation F (GLnLocal.uniformizer F : F))⁻¹ ^ k}, fun k => IsNonarchimedeanLocalField.isCompact_closedBall F _, ?_⟩⟩` and prove the remaining obligations. Use `Set.eq_univ_of_forall fun x => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_iUnion, Set.mem_ofPred_eq]`. Distinguish the cases in `hx : x = 0`. Conclude with `⟨0, by simp [hx]⟩`.

Establish `hvx : valuation F x ≠ 0` using `(Valuation.ne_zero_iff _).mpr hx`. Take `⟨m, hm⟩` from `exists_pow_lt₀ (GLnLocal.valuation_uniformizer_lt_one F) (Units.mk0 _ hvx)⁻¹`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `hϖ` using `GLnLocal.valuation_uniformizer_ne_zero F`. Establish `h1 : valuation F (GLnLocal.uniformizer F : F) ^ m * valuation F x < 1`.

Use `mul_lt_mul_of_pos_right hm (zero_lt_iff.mpr hvx)` as an intermediate fact. Simplify `this` using `[hvx]`. Establish `hm0 : valuation F (GLnLocal.uniformizer F : F) ^ m ≠ 0` using `pow_ne_zero _ hϖ`. Rewrite using `[inv_pow, ← mul_one ((valuation F (GLnLocal.uniformizer F : F) ^ m)⁻¹), le_inv_mul_iff₀ (zero_lt_iff.mpr hm0)]`. Conclude with `h1.le`.
-/
theorem sigmaCompactSpace : SigmaCompactSpace F := by
  refine ⟨⟨fun k : ℕ => {x | valuation F x ≤ (valuation F (GLnLocal.uniformizer F : F))⁻¹ ^ k},
    fun k => IsNonarchimedeanLocalField.isCompact_closedBall F _, ?_⟩⟩
  refine Set.eq_univ_of_forall fun x => ?_
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hvx : valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨m, hm⟩ := exists_pow_lt₀ (GLnLocal.valuation_uniformizer_lt_one F) (Units.mk0 _ hvx)⁻¹
  refine ⟨m, ?_⟩
  have hϖ := GLnLocal.valuation_uniformizer_ne_zero F
  have h1 : valuation F (GLnLocal.uniformizer F : F) ^ m * valuation F x < 1 := by
    have := mul_lt_mul_of_pos_right hm (zero_lt_iff.mpr hvx)
    simpa [hvx] using this
  have hm0 : valuation F (GLnLocal.uniformizer F : F) ^ m ≠ 0 := pow_ne_zero _ hϖ
  rw [inv_pow, ← mul_one ((valuation F (GLnLocal.uniformizer F : F) ^ m)⁻¹),
    le_inv_mul_iff₀ (zero_lt_iff.mpr hm0)]
  exact h1.le

instance secondCountableTopology : SecondCountableTopology F := by
  have := metrizableSpace F
  have := sigmaCompactSpace F
  let := TopologicalSpace.metrizableSpaceMetric F
  exact EMetric.secondCountable_of_sigmaCompact F

/- English proof (translation)
The claim follows from `haveI : SecondCountableTopology Mᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology Units.isEmbedding_embedProduct.secondCountableTopology`.
-/
theorem secondCountableTopology_units {M : Type*} [Monoid M] [TopologicalSpace M]
    [SecondCountableTopology M] : SecondCountableTopology Mˣ :=
  haveI : SecondCountableTopology Mᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

instance secondCountableTopology_GL (ι : Type*) [Fintype ι] [DecidableEq ι] :
    SecondCountableTopology (GL ι F) :=
  haveI : SecondCountableTopology (Matrix ι ι F) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → F))
  secondCountableTopology_units

end Topology

section Modulus

variable {F} {ι : Type*} [Fintype ι]

instance continuousConstSMul_linearEquiv :
    ContinuousConstSMul ((ι → F) ≃ₗ[F] (ι → F)) (ι → F) :=
  ⟨fun L => (L.toLinearMap).continuous_on_pi⟩

variable (F ι) in

def box : Set (ι → F) := Set.univ.pi fun _ => (𝒪[F] : Set F)

/- English proof (translation)
Simplify using `[box]`.
-/
theorem mem_box {x : ι → F} : x ∈ box F ι ↔ ∀ i, x i ∈ 𝒪[F] := by
  simp [box]

/- English proof (translation)
The claim follows from `isOpen_set_pi Set.finite_univ fun _ _ => Valuation.isOpen_integer`.
-/
theorem isOpen_box : IsOpen (box F ι) :=
  isOpen_set_pi Set.finite_univ fun _ _ => Valuation.isOpen_integer

/- English proof (translation)
The claim follows from `isCompact_univ_pi fun _ => isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[F]))`.
-/
theorem isCompact_box : IsCompact (box F ι) :=
  isCompact_univ_pi fun _ => isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[F]))

/- English proof (translation)
Introduce `_ _` and use `(𝒪[F]).zero_mem`.
-/
theorem zero_mem_box : (0 : ι → F) ∈ box F ι := fun _ _ => (𝒪[F]).zero_mem

/- English proof (translation)
Use `borelize (ι → F)`. Set `μ : Measure (ι → F)` to `Measure.addHaar`. Use `distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := box F ι) (isOpen_box.measure_ne_zero μ ⟨0, zero_mem_box⟩) isCompact_box.measure_lt_top.ne ?_` and prove the remaining obligations. Establish `: L • box F ι = L '' box F ι` using `rfl`. Rewrite using `[this, h, ENNReal.coe_one, one_mul]`.
-/
theorem distribHaarChar_eq_one_of_image_box {L : (ι → F) ≃ₗ[F] (ι → F)}
    (h : L '' box F ι = box F ι) : distribHaarChar (ι → F) L = 1 := by
  borelize (ι → F)
  let μ : Measure (ι → F) := Measure.addHaar
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := box F ι)
    (isOpen_box.measure_ne_zero μ ⟨0, zero_mem_box⟩) isCompact_box.measure_lt_top.ne ?_
  have : L • box F ι = L '' box F ι := rfl
  rw [this, h, ENNReal.coe_one, one_mul]

/- English proof (translation)
Use `distribHaarChar_eq_one_of_image_box (Set.Subset.antisymm ?_ fun x hx => ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `h₁ x hx`. Conclude with `⟨L.symm x, h₂ x hx, L.apply_symm_apply x⟩`.
-/
theorem distribHaarChar_eq_one_of_mapsTo_box {L : (ι → F) ≃ₗ[F] (ι → F)}
    (h₁ : ∀ x ∈ box F ι, L x ∈ box F ι) (h₂ : ∀ x ∈ box F ι, L.symm x ∈ box F ι) :
    distribHaarChar (ι → F) L = 1 := by
  refine distribHaarChar_eq_one_of_image_box (Set.Subset.antisymm ?_ fun x hx => ?_)
  · rintro _ ⟨x, hx, rfl⟩
    exact h₁ x hx
  · exact ⟨L.symm x, h₂ x hx, L.apply_symm_apply x⟩

variable [DecidableEq ι]

/- English proof (translation)
The claim follows from `mem_box.2 fun i => Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (mem_box.1 hx j)`.
-/
theorem mulVec_mem_box {A : Matrix ι ι F} (hA : ∀ i j, A i j ∈ 𝒪[F]) {x : ι → F}
    (hx : x ∈ box F ι) : A.mulVec x ∈ box F ι :=
  mem_box.2 fun i => Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (mem_box.1 hx j)

noncomputable def modulus : F →*₀ ℝ≥0 where
  toFun x := by classical exact if h : x = 0 then 0 else distribHaarChar F (Units.mk0 x h)
  map_zero' := dif_pos rfl
  map_one' := by
    rw [dif_neg one_ne_zero]
    convert map_one (distribHaarChar F (G := Fˣ))
    ext
    rfl
  map_mul' x y := by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    rw [dif_neg (mul_ne_zero hx hy), dif_neg hx, dif_neg hy, ← map_mul]
    congr 1
    ext
    rfl

/- English proof (translation)
Rewrite using `[modulus, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, dif_neg u.ne_zero]`. Use `congr 1`. Use `ext`. Both sides reduce to the same expression.
-/
theorem modulus_units (u : Fˣ) : modulus (u : F) = distribHaarChar F u := by
  rw [modulus, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, dif_neg u.ne_zero]
  congr 1
  ext
  rfl

/- English proof (translation)
Rewrite using `[show x = ((Units.mk0 x hx : Fˣ) : F) from rfl, modulus_units]`. Conclude with `distribHaarChar_pos.ne'`.
-/
theorem modulus_ne_zero {x : F} (hx : x ≠ 0) : modulus x ≠ 0 := by
  rw [show x = ((Units.mk0 x hx : Fˣ) : F) from rfl, modulus_units]
  exact distribHaarChar_pos.ne'

noncomputable def glEquiv : GL ι F ≃* ((ι → F) ≃ₗ[F] (ι → F)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (ι → F))

/- English proof (translation)
Simplify using `[glEquiv, LinearMap.GeneralLinearGroup.generalLinearEquiv, Matrix.GeneralLinearGroup.toLin]`.
-/
theorem glEquiv_apply (g : GL ι F) (x : ι → F) : glEquiv g x = (g : Matrix ι ι F).mulVec x := by
  simp [glEquiv, LinearMap.GeneralLinearGroup.generalLinearEquiv, Matrix.GeneralLinearGroup.toLin]

/- English proof (translation)
Use `ext`. Rewrite using `[LinearEquiv.coe_det]`. Use `show LinearMap.det (Matrix.toLin' (g : Matrix ι ι F)) = _`. Rewrite using `[LinearMap.det_toLin']`. Both sides reduce to the same expression.
-/
theorem det_glEquiv (g : GL ι F) :
    LinearEquiv.det (glEquiv g) = Matrix.GeneralLinearGroup.det g := by
  ext
  rw [LinearEquiv.coe_det]
  show LinearMap.det (Matrix.toLin' (g : Matrix ι ι F)) = _
  rw [LinearMap.det_toLin']
  rfl

/- English proof (translation)
Use `distribHaarChar_eq_one_of_mapsTo_box (fun x hx => ?_) (fun x hx => ?_)` and prove the remaining obligations. Rewrite using `[glEquiv_apply]`. Conclude with `mulVec_mem_box h₁ hx`. Rewrite using `[show (glEquiv g).symm = glEquiv g⁻¹ from (map_inv glEquiv g).symm, glEquiv_apply]`. Conclude with `mulVec_mem_box h₂ hx`.
-/
theorem distribHaarChar_glEquiv_eq_one {g : GL ι F} (h₁ : ∀ a b, (g : Matrix ι ι F) a b ∈ 𝒪[F])
    (h₂ : ∀ a b, ((g⁻¹ : GL ι F) : Matrix ι ι F) a b ∈ 𝒪[F]) :
    distribHaarChar (ι → F) (glEquiv g) = 1 := by
  refine distribHaarChar_eq_one_of_mapsTo_box (fun x hx => ?_) (fun x hx => ?_)
  · rw [glEquiv_apply]
    exact mulVec_mem_box h₁ hx
  · rw [show (glEquiv g).symm = glEquiv g⁻¹ from (map_inv glEquiv g).symm, glEquiv_apply]
    exact mulVec_mem_box h₂ hx

/- English proof (translation)
Simplify using `only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]`. Use `Subring.add_mem _ ?_ ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `Subring.one_mem _`. Conclude with `Subring.zero_mem _`.

Use `split_ifs`. Conclude with `hc`. Conclude with `Subring.zero_mem _`.
-/
theorem transvection_mem_integer {i j : ι} {c : F} (hc : c ∈ 𝒪[F]) (a b : ι) :
    Matrix.transvection i j c a b ∈ 𝒪[F] := by
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  refine Subring.add_mem _ ?_ ?_
  · split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · split_ifs
    · exact hc
    · exact Subring.zero_mem _

/- English proof (translation)
Establish `hD : ∀ i, D i ≠ 0` using `fun i => by`. Rewrite `h` using `[Matrix.det_diagonal]`. Conclude with `Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)`. Set `u : ι → Fˣ` to `fun i => Units.mk0 (D i) (hD i)`. Establish `hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) = ∏ i, u i`.

Use `ext`. Simplify using `[u, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_diagonal]`. Rewrite using `[hdet, map_prod]`. Use `borelize F`. Set `ν : Measure F` to `Measure.addHaar`.

Set `μ : Measure (ι → F)` to `Measure.pi fun _ => ν`. Establish `himage : glEquiv (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) • box F ι = Set.univ.pi fun i => u i • (𝒪[F] : Set F)`. Use extensionality with `x`. Simplify using `only [Set.mem_pi, Set.mem_univ, true_implies]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩ i`. Use `⟨y i, mem_box.1 hy i, ?_⟩` and prove the remaining obligations. Simplify using `[LinearEquiv.smul_def, glEquiv_apply, u, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mulVec_diagonal]`. Introduce `hx choose y hy hyx using hx`. Use `⟨y, mem_box.2 hy, funext fun i => ?_⟩` and prove the remaining obligations.

Simplify `hyx i` using `[LinearEquiv.smul_def, glEquiv_apply, u, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mulVec_diagonal, Units.smul_def]`. Use `distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := box F ι) (isOpen_box.measure_ne_zero μ ⟨0, zero_mem_box⟩) isCompact_box.measure_lt_top.ne ?_` and prove the remaining obligations. Rewrite using `[himage, box, Measure.pi_pi, Measure.pi_pi, ENNReal.ofNNReal_finsetProd, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `(distribHaarChar_mul ν (u i) _).symm`.
-/
theorem distribHaarChar_glEquiv_diagonal {D : ι → F} (h : (Matrix.diagonal D).det ≠ 0) :
    distribHaarChar (ι → F) (glEquiv (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)) =
      distribHaarChar F (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)) := by
  have hD : ∀ i, D i ≠ 0 := fun i => by
    rw [Matrix.det_diagonal] at h
    exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)
  let u : ι → Fˣ := fun i => Units.mk0 (D i) (hD i)
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) =
      ∏ i, u i := by
    ext
    simp [u, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_diagonal]
  rw [hdet, map_prod]
  borelize F
  let ν : Measure F := Measure.addHaar
  let μ : Measure (ι → F) := Measure.pi fun _ => ν
  have himage : glEquiv (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) • box F ι =
      Set.univ.pi fun i => u i • (𝒪[F] : Set F) := by
    ext x
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      refine ⟨y i, mem_box.1 hy i, ?_⟩
      simp [LinearEquiv.smul_def, glEquiv_apply, u, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mulVec_diagonal]
    · intro hx
      choose y hy hyx using hx
      refine ⟨y, mem_box.2 hy, funext fun i => ?_⟩
      simpa [LinearEquiv.smul_def, glEquiv_apply, u, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mulVec_diagonal, Units.smul_def] using hyx i
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := box F ι)
    (isOpen_box.measure_ne_zero μ ⟨0, zero_mem_box⟩) isCompact_box.measure_lt_top.ne ?_
  rw [himage, box, Measure.pi_pi, Measure.pi_pi, ENNReal.ofNNReal_finsetProd,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (distribHaarChar_mul ν (u i) _).symm

/- English proof (translation)
Take `⟨i, j, hij, c⟩` from `t`. Establish `h1 : ∀ d : F, (Matrix.transvection i j d).det ≠ 0` using `fun d => by`. Rewrite using `[Matrix.det_transvection_of_ne _ _ hij]`. Conclude with `one_ne_zero`. Set `T : F → GL ι F` to `fun d => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (h1 d)`.

Establish `hT : ∀ d d', T d * T d' = T (d + d')` using `fun d d' => by`. Use extensionality with `: 1`. Simplify using `[T, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.transvection_mul_transvection_same (h := hij)]`. Establish `hT1 : distribHaarChar (ι → F) (glEquiv (T 1)) = 1`. Establish `hinv : (T 1)⁻¹ = T (-1)`.

Rewrite using `[inv_eq_iff_mul_eq_one, hT, add_neg_cancel]`. Use extensionality with `: 1`. Simplify using `[T, Matrix.GeneralLinearGroup.mkOfDetNeZero]`. Use `distribHaarChar_glEquiv_eq_one (fun a b => ?_) (fun a b => ?_)` and prove the remaining obligations. Conclude with `transvection_mem_integer (Subring.one_mem _) a b`.

Rewrite using `[hinv]`. Conclude with `transvection_mem_integer (Subring.neg_mem _ (Subring.one_mem _)) a b`. Express the relevant statement in the definitionally equal form `distribHaarChar (ι → F) (glEquiv (T c)) = 1`. Distinguish the cases in `hc : c = 0`. Establish `: T c = 1`.

Use extensionality with `: 1`. Simplify using `[T, hc, Matrix.GeneralLinearGroup.mkOfDetNeZero]`. Rewrite using `[this, map_one, map_one]`. Set `d : ι → F` to `Function.update 1 i c`. Establish `hd : (Matrix.diagonal d).det ≠ 0`.

Rewrite using `[Matrix.det_diagonal]`. Use `Finset.prod_ne_zero_iff.2 fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify `hc` using `[d]`.

Simplify using `[d, hk]`. Set `Dg : GL ι F` to `Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd`. Establish `hM : Matrix.transvection i j c * Matrix.diagonal d = Matrix.diagonal d * Matrix.transvection i j 1`. Use extensionality with `a b`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`.

Simplify using `only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, d]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Distinguish the cases in `hai : a = i`. Substitute `hai` using the available equality.

Simplify using `[Ne.symm hij]`. Simplify using `[hai, Ne.symm hai]`. Distinguish the cases in `hai : a = i`. Substitute `hai` using the available equality. Distinguish the cases in `hbj : b = j`.

Substitute `hbj` using the available equality. Simplify using `[hab, Ne.symm hij]`. Simplify using `[hab, Ne.symm hbj]`. Simplify using `[hab, hai, Ne.symm hai]`. Establish `hcomm : T c * Dg = Dg * T 1`.

Use extensionality with `: 1`. Simplify `hM` using `[T, Dg, Matrix.GeneralLinearGroup.mkOfDetNeZero]`. Establish `key` using `congrArg (fun g => distribHaarChar (ι → F) (glEquiv g)) hcomm`. Simplify using `only [map_mul, hT1, mul_one] at key`. Establish `hpos : distribHaarChar (ι → F) (glEquiv Dg) ≠ 0` using `distribHaarChar_pos.ne'`.

Rewrite `key` using `[mul_comm]`. Conclude with `(mul_eq_left₀ hpos).1 key`.
-/
theorem distribHaarChar_glEquiv_transvection (t : Matrix.TransvectionStruct ι F)
    (h : t.toMatrix.det ≠ 0) :
    distribHaarChar (ι → F) (glEquiv (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)) = 1 := by
  classical
  obtain ⟨i, j, hij, c⟩ := t
  have h1 : ∀ d : F, (Matrix.transvection i j d).det ≠ 0 := fun d => by
    rw [Matrix.det_transvection_of_ne _ _ hij]
    exact one_ne_zero
  let T : F → GL ι F := fun d => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (h1 d)
  have hT : ∀ d d', T d * T d' = T (d + d') := fun d d' => by
    ext : 1
    simp [T, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.transvection_mul_transvection_same (h := hij)]
  have hT1 : distribHaarChar (ι → F) (glEquiv (T 1)) = 1 := by
    have hinv : (T 1)⁻¹ = T (-1) := by
      rw [inv_eq_iff_mul_eq_one, hT, add_neg_cancel]
      ext : 1
      simp [T, Matrix.GeneralLinearGroup.mkOfDetNeZero]
    refine distribHaarChar_glEquiv_eq_one (fun a b => ?_) (fun a b => ?_)
    · exact transvection_mem_integer (Subring.one_mem _) a b
    · rw [hinv]
      exact transvection_mem_integer (Subring.neg_mem _ (Subring.one_mem _)) a b
  change distribHaarChar (ι → F) (glEquiv (T c)) = 1
  by_cases hc : c = 0
  · have : T c = 1 := by
      ext : 1
      simp [T, hc, Matrix.GeneralLinearGroup.mkOfDetNeZero]
    rw [this, map_one, map_one]
  let d : ι → F := Function.update 1 i c
  have hd : (Matrix.diagonal d).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    by_cases hk : k = i
    · subst hk; simpa [d] using hc
    · simp [d, hk]
  let Dg : GL ι F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd
  have hM : Matrix.transvection i j c * Matrix.diagonal d =
      Matrix.diagonal d * Matrix.transvection i j 1 := by
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, d]
    by_cases hab : a = b
    · subst hab
      by_cases hai : a = i
      · subst hai; simp [Ne.symm hij]
      · simp [hai, Ne.symm hai]
    · by_cases hai : a = i
      · subst hai
        by_cases hbj : b = j
        · subst hbj; simp [hab, Ne.symm hij]
        · simp [hab, Ne.symm hbj]
      · simp [hab, hai, Ne.symm hai]
  have hcomm : T c * Dg = Dg * T 1 := by
    ext : 1
    simpa [T, Dg, Matrix.GeneralLinearGroup.mkOfDetNeZero] using hM
  have key := congrArg (fun g => distribHaarChar (ι → F) (glEquiv g)) hcomm
  simp only [map_mul, hT1, mul_one] at key
  have hpos : distribHaarChar (ι → F) (glEquiv Dg) ≠ 0 := distribHaarChar_pos.ne'
  rw [mul_comm] at key
  exact (mul_eq_left₀ hpos).1 key

/- English proof (translation)
Set `φ : GL ι F →* ℝ≥0` to `(distribHaarChar (ι → F)).comp glEquiv.toMonoidHom`. Set `ψ : GL ι F →* ℝ≥0` to `(distribHaarChar F).comp Matrix.GeneralLinearGroup.det`. Establish `key : ∀ (M : Matrix ι ι F) (h : M.det ≠ 0), φ (Matrix.GeneralLinearGroup.mkOfDetNeZero M h) = ψ (Matrix.GeneralLinearGroup.mkOfDetNeZero M h)`. Introduce `M hM`. Use `Matrix.diagonal_transvection_induction_of_det_ne_zero (fun M => ∀ h : M.det ≠ 0, φ (Matrix.GeneralLinearGroup.mkOfDetNeZero M h) = ψ (Matrix.GeneralLinearGroup.mkOfDetNeZero M h)) M hM ?_ ?_ ?_ hM` and prove the remaining obligations.

Introduce `D _ h`. Conclude with `distribHaarChar_glEquiv_diagonal h`. Introduce `t h`. Establish `hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) = 1`. Use `ext`.

Simplify using `[Matrix.GeneralLinearGroup.mkOfDetNeZero]`. Express the relevant statement in the definitionally equal form `distribHaarChar (ι → F) (glEquiv _) = distribHaarChar F _`. Rewrite using `[distribHaarChar_glEquiv_transvection t h, hdet, map_one]`. Introduce `A B hA hB IHA IHB h`. Establish `: Matrix.GeneralLinearGroup.mkOfDetNeZero (A * B) h = Matrix.GeneralLinearGroup.mkOfDetNeZero A hA * Matrix.GeneralLinearGroup.mkOfDetNeZero B hB`.

Use extensionality with `: 1`. Both sides reduce to the same expression. Rewrite using `[this, map_mul, map_mul, IHA hA, IHB hB]`. Establish `hg : Matrix.GeneralLinearGroup.mkOfDetNeZero (g : Matrix ι ι F) (Matrix.det_ne_zero_of_left_inverse (g.inv_mul)) = g`. Use extensionality with `: 1`.

Both sides reduce to the same expression. Use `key _ (Matrix.det_ne_zero_of_left_inverse (g.inv_mul))` as an intermediate fact. Rewrite `this` using `[hg]`. Conclude with `this`.
-/
theorem distribHaarChar_glEquiv (g : GL ι F) :
    distribHaarChar (ι → F) (glEquiv g) = distribHaarChar F (Matrix.GeneralLinearGroup.det g) := by
  let φ : GL ι F →* ℝ≥0 := (distribHaarChar (ι → F)).comp glEquiv.toMonoidHom
  let ψ : GL ι F →* ℝ≥0 := (distribHaarChar F).comp Matrix.GeneralLinearGroup.det
  have key : ∀ (M : Matrix ι ι F) (h : M.det ≠ 0),
      φ (Matrix.GeneralLinearGroup.mkOfDetNeZero M h) =
        ψ (Matrix.GeneralLinearGroup.mkOfDetNeZero M h) := by
    intro M hM
    refine Matrix.diagonal_transvection_induction_of_det_ne_zero
      (fun M => ∀ h : M.det ≠ 0, φ (Matrix.GeneralLinearGroup.mkOfDetNeZero M h) =
        ψ (Matrix.GeneralLinearGroup.mkOfDetNeZero M h)) M hM ?_ ?_ ?_ hM
    · intro D _ h
      exact distribHaarChar_glEquiv_diagonal h
    · intro t h
      have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) = 1 := by
        ext
        simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
      change distribHaarChar (ι → F) (glEquiv _) = distribHaarChar F _
      rw [distribHaarChar_glEquiv_transvection t h, hdet, map_one]
    · intro A B hA hB IHA IHB h
      have : Matrix.GeneralLinearGroup.mkOfDetNeZero (A * B) h =
          Matrix.GeneralLinearGroup.mkOfDetNeZero A hA *
            Matrix.GeneralLinearGroup.mkOfDetNeZero B hB := by
        ext : 1
        rfl
      rw [this, map_mul, map_mul, IHA hA, IHB hB]
  have hg : Matrix.GeneralLinearGroup.mkOfDetNeZero (g : Matrix ι ι F)
      (Matrix.det_ne_zero_of_left_inverse (g.inv_mul)) = g := by
    ext : 1
    rfl
  have := key _ (Matrix.det_ne_zero_of_left_inverse (g.inv_mul))
  rw [hg] at this
  exact this

/- English proof (translation)
Take `⟨g, rfl⟩` from `glEquiv.surjective L`. Rewrite using `[distribHaarChar_glEquiv, det_glEquiv]`.
-/
theorem distribHaarChar_pi_eq (L : (ι → F) ≃ₗ[F] (ι → F)) :
    distribHaarChar (ι → F) L = distribHaarChar F (LinearEquiv.det L) := by
  obtain ⟨g, rfl⟩ := glEquiv.surjective L
  rw [distribHaarChar_glEquiv, det_glEquiv]

end Modulus

end Measures

end GroundTheory.Automorphic
