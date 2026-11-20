import Mathlib

import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.Imports
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.ContinuousOnChartProjM
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.FramePairAddRight
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.InstSecondCountableTopologyFrameSp

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

namespace IsoFrames

namespace Chart

open MeasureTheory Topology Filter Set Matrix TensorProduct GroundTheory.Automorphic FibreMeasure

noncomputable section

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} {H : Matrix ι ι E}

attribute [local instance] scTop finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

local infixl:70 " ⬝ " => @HMul.hMul _ _ _ instHMulOfFintypeOfMulOfAddCommMonoid

def toM {κ : Type*} [Fintype κ] [DecidableEq κ] (X : FrameSp K E R κ p) : Matrix κ (Fin p) (R ⊗[K] E) := X

def ofM {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix κ (Fin p) (R ⊗[K] E)) : FrameSp K E R κ p := M

variable (R p) in

def gramH (hH : IsHermitianFor (conjHom K E) H) (X : FrameSp K E R ι p) : HermSp K E R p :=
  ⟨gram K E R H (toM X), cT_framePair hH _ _⟩

/- English proof (translation)
The claim follows from `continuous_id`.
-/
theorem continuous_toM {κ : Type*} [Fintype κ] [DecidableEq κ] :
    Continuous (toM : FrameSp K E R κ p → Matrix κ (Fin p) (R ⊗[K] E)) := continuous_id

/- English proof (translation)
The claim follows from `continuous_id`.
-/
theorem continuous_ofM {κ : Type*} [Fintype κ] [DecidableEq κ] :
    Continuous (ofM : Matrix κ (Fin p) (R ⊗[K] E) → FrameSp K E R κ p) := continuous_id

/- English proof (translation)
Simplify using `only [framePair_eq]`. Conclude with `continuous_const.matrix_mul continuous_toM`.
-/
theorem continuous_framePair_left {q : ℕ} (Z : Matrix ι (Fin q) (R ⊗[K] E)) :
    Continuous (fun X : FrameSp K E R ι p ↦ framePair K E R H Z (toM X)) := by
  simp only [framePair_eq]
  exact continuous_const.matrix_mul continuous_toM

/- English proof (translation)
Simplify using `only [gram, framePair_eq]`. Conclude with `(((continuous_toM.matrix_map (continuous_conjBase R)).matrix_transpose).matrix_mul continuous_const).matrix_mul continuous_toM`.
-/
theorem continuous_gram :
    Continuous (fun X : FrameSp K E R ι p ↦ gram K E R H (toM X)) := by
  simp only [gram, framePair_eq]
  exact (((continuous_toM.matrix_map (continuous_conjBase R)).matrix_transpose).matrix_mul
    continuous_const).matrix_mul continuous_toM

/- English proof (translation)
The claim follows from `continuous_gram.subtype_mk _`.
-/
theorem continuous_gramH (hH : IsHermitianFor (conjHom K E) H) :
    Continuous (gramH R p hH) :=
  continuous_gram.subtype_mk _

variable (R p H) in

def chartSet (Z : Matrix ι (Fin p) (R ⊗[K] E)) : Set (FrameSp K E R ι p) :=
  {X | IsUnit (framePair K E R H Z (toM X)).det}

variable (H) in

def chartShift (Z : Matrix ι (Fin p) (R ⊗[K] E)) (S : HermSp K E R p) :
    FrameSp K E R ι p → FrameSp K E R (Fin p) p := by
  classical exact (chartSet R p H Z).piecewise (fun X ↦ ofM (shiftT (H := H) Z (toM X) S.mat)) 0

variable (H) in

def chartAct (Z : Matrix ι (Fin p) (R ⊗[K] E)) (S : HermSp K E R p) (X : FrameSp K E R ι p) :
    FrameSp K E R ι p :=
  ofM (toM X + Z ⬝ toM (chartShift H Z S X))

variable {Z : Matrix ι (Fin p) (R ⊗[K] E)}

/- English proof (translation)
Simplify using `only [chartShift, Set.piecewise, hX, if_true]`. Both sides reduce to the same expression.
-/
theorem chartShift_of_mem {S : HermSp K E R p} {X : FrameSp K E R ι p}
    (hX : X ∈ chartSet R p H Z) :
    toM (chartShift H Z S X) = shiftT (H := H) Z (toM X) S.mat := by
  classical
  simp only [chartShift, Set.piecewise, hX, if_true]
  rfl

/- English proof (translation)
Simplify using `only [chartShift, Set.piecewise, hX, if_false]`. Both sides reduce to the same expression.
-/
theorem chartShift_of_notMem {S : HermSp K E R p} {X : FrameSp K E R ι p}
    (hX : X ∉ chartSet R p H Z) : chartShift H Z S X = 0 := by
  classical
  simp only [chartShift, Set.piecewise, hX, if_false]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toM_chartAct (S : HermSp K E R p) (X : FrameSp K E R ι p) :
    toM (chartAct H Z S X) = toM X + Z ⬝ toM (chartShift H Z S X) := rfl

/- English proof (translation)
Rewrite using `[toM_chartAct]`. Conclude with `framePair_add_iso hZ _ _`.
-/
theorem framePair_chartAct (hZ : gram K E R H Z = 0) (S : HermSp K E R p) (X : FrameSp K E R ι p) :
    framePair K E R H Z (toM (chartAct H Z S X)) = framePair K E R H Z (toM X) := by
  rw [toM_chartAct]
  exact framePair_add_iso hZ _ _

/- English proof (translation)
Use `show IsUnit _ ↔ IsUnit _`. Rewrite using `[framePair_chartAct hZ]`.
-/
theorem mem_chartSet_chartAct (hZ : gram K E R H Z = 0) (S : HermSp K E R p)
    (X : FrameSp K E R ι p) : chartAct H Z S X ∈ chartSet R p H Z ↔ X ∈ chartSet R p H Z := by
  show IsUnit _ ↔ IsUnit _
  rw [framePair_chartAct hZ]

/- English proof (translation)
The claim follows from `((continuous_fst.matrix_mul continuous_snd : Continuous fun q : Matrix m n (R ⊗[K] E) × Matrix n l (R ⊗[K] E) ↦ q.1 ⬝ q.2).continuousAt).comp (hf.prodMk hg)`.
-/
theorem continuousAt_mulM {X : Type*} [TopologicalSpace X] {m n l : Type*} [Fintype n]
    {f : X → Matrix m n (R ⊗[K] E)} {g : X → Matrix n l (R ⊗[K] E)} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun y ↦ f y ⬝ g y) x :=
  ((continuous_fst.matrix_mul continuous_snd :
    Continuous fun q : Matrix m n (R ⊗[K] E) × Matrix n l (R ⊗[K] E) ↦ q.1 ⬝ q.2).continuousAt).comp
    (hf.prodMk hg)

variable (hRu : IsOpen {r : R | IsUnit r}) (hRi : ∀ r : R, IsUnit r → ContinuousAt Ring.inverse r)

include hRu in
/- English proof (translation)
The claim follows from `(isOpen_isUnit_det hRu).preimage (continuous_framePair_left Z)`.
-/
theorem isOpen_chartSet : IsOpen (chartSet R p H Z) :=
  (isOpen_isUnit_det hRu).preimage (continuous_framePair_left Z)

/- English proof (translation)
Rewrite using `[shiftT, shiftT, shiftT, smul_add, Matrix.mul_add]`.
-/
theorem shiftT_add (X : Matrix ι (Fin p) (R ⊗[K] E)) (S T : Matrix (Fin p) (Fin p) (R ⊗[K] E)) :
    shiftT (H := H) Z X (S + T) = shiftT (H := H) Z X S + shiftT (H := H) Z X T := by
  rw [shiftT, shiftT, shiftT, smul_add, Matrix.mul_add]

/- English proof (translation)
Rewrite using `[shiftT, smul_zero, Matrix.mul_zero]`.
-/
theorem shiftT_zero (X : Matrix ι (Fin p) (R ⊗[K] E)) : shiftT (H := H) Z X 0 = 0 := by
  rw [shiftT, smul_zero, Matrix.mul_zero]

/- English proof (translation)
Rewrite using `[shiftT, shiftT, framePair_add_iso hZ]`.
-/
theorem shiftT_add_iso (hZ : gram K E R H Z = 0) (X : Matrix ι (Fin p) (R ⊗[K] E))
    (d : Matrix (Fin p) (Fin p) (R ⊗[K] E)) (S : Matrix (Fin p) (Fin p) (R ⊗[K] E)) :
    shiftT (H := H) Z (X + Z ⬝ d) S = shiftT (H := H) Z X S := by
  rw [shiftT, shiftT, framePair_add_iso hZ]

/- English proof (translation)
Establish `hmem : ofM (toM X + Z ⬝ toM d) ∈ chartSet R p H Z ↔ X ∈ chartSet R p H Z` using `by show IsUnit _ ↔ IsUnit _`. Rewrite using `[show toM (ofM (toM X + Z ⬝ toM d) : FrameSp K E R ι p) = toM X + Z ⬝ toM d from rfl, framePair_add_iso hZ]`. Distinguish the cases in `hX : X ∈ chartSet R p H Z`. Establish `h1` using `chartShift_of_mem (S := S) hX`. Establish `h2` using `chartShift_of_mem (S := S) (hmem.2 hX)`.

Rewrite `h2` using `[show toM (ofM (toM X + Z ⬝ toM d) : FrameSp K E R ι p) = toM X + Z ⬝ toM d from rfl, shiftT_add_iso hZ, ← h1]`. Conclude with `h2`. Rewrite using `[chartShift_of_notMem hX, chartShift_of_notMem (fun h ↦ hX (hmem.1 h))]`.
-/
theorem chartShift_add_iso (hZ : gram K E R H Z = 0) (S : HermSp K E R p) (X : FrameSp K E R ι p)
    (d : FrameSp K E R (Fin p) p) :
    chartShift H Z S (ofM (toM X + Z ⬝ toM d)) = chartShift H Z S X := by
  have hmem : ofM (toM X + Z ⬝ toM d) ∈ chartSet R p H Z ↔ X ∈ chartSet R p H Z := by
    show IsUnit _ ↔ IsUnit _
    rw [show toM (ofM (toM X + Z ⬝ toM d) : FrameSp K E R ι p) = toM X + Z ⬝ toM d from rfl,
      framePair_add_iso hZ]
  by_cases hX : X ∈ chartSet R p H Z
  · have h1 := chartShift_of_mem (S := S) hX
    have h2 := chartShift_of_mem (S := S) (hmem.2 hX)
    rw [show toM (ofM (toM X + Z ⬝ toM d) : FrameSp K E R ι p) = toM X + Z ⬝ toM d from rfl,
      shiftT_add_iso hZ, ← h1] at h2
    exact h2
  · rw [chartShift_of_notMem hX, chartShift_of_notMem (fun h ↦ hX (hmem.1 h))]

include hRu hRi in
/- English proof (translation)
Introduce `X hX`. Use `ContinuousAt.continuousWithinAt ?_` and prove the remaining obligations. Establish `hu : IsUnit (cT K E R (framePair K E R H Z (toM X))).det`. Rewrite using `[det_cT]`. Conclude with `hX.map _`.

Establish `hc : Continuous (fun X : FrameSp K E R ι p ↦ cT K E R (framePair K E R H Z (toM X)))` using `((continuous_framePair_left Z).matrix_map (continuous_conjBase R)).matrix_transpose`. Establish `hinv : ContinuousAt (fun X : FrameSp K E R ι p ↦ (cT K E R (framePair K E R H Z (toM X)))⁻¹) X` using `ContinuousAt.comp (g := Inv.inv) (continuousAt_matrix_inv_A hRu hRi _ hu) hc.continuousAt`. Conclude with `continuous_ofM.continuousAt.comp (continuousAt_mulM hinv continuousAt_const)`.
-/
theorem continuousOn_shiftT (S : HermSp K E R p) :
    ContinuousOn (fun X : FrameSp K E R ι p ↦
      (ofM (shiftT (H := H) Z (toM X) S.mat) : FrameSp K E R (Fin p) p)) (chartSet R p H Z) := by
  intro X hX
  refine ContinuousAt.continuousWithinAt ?_
  have hu : IsUnit (cT K E R (framePair K E R H Z (toM X))).det := by
    rw [det_cT]
    exact hX.map _
  have hc : Continuous (fun X : FrameSp K E R ι p ↦ cT K E R (framePair K E R H Z (toM X))) :=
    ((continuous_framePair_left Z).matrix_map (continuous_conjBase R)).matrix_transpose
  have hinv : ContinuousAt (fun X : FrameSp K E R ι p ↦ (cT K E R (framePair K E R H Z (toM X)))⁻¹) X :=
    ContinuousAt.comp (g := Inv.inv) (continuousAt_matrix_inv_A hRu hRi _ hu) hc.continuousAt
  exact continuous_ofM.continuousAt.comp (continuousAt_mulM hinv continuousAt_const)

include hRu hRi in
/- English proof (translation)
Conclude with `ContinuousOn.measurable_piecewise (γ := FrameSp K E R (Fin p) p) (continuousOn_shiftT hRu hRi S) continuousOn_const (isOpen_chartSet hRu).measurableSet`.
-/
theorem measurable_chartShift (S : HermSp K E R p) : Measurable (chartShift H Z S) := by
  classical
  exact ContinuousOn.measurable_piecewise (γ := FrameSp K E R (Fin p) p)
    (continuousOn_shiftT hRu hRi S) continuousOn_const (isOpen_chartSet hRu).measurableSet

include hRu hRi in

/- English proof (translation)
Establish `hΩ : IsOpen (chartSet R p H Z)` using `isOpen_chartSet hRu`. Use `⟨hΩ, ?_, fun S X hX ↦ (mem_chartSet_chartAct hZ S X).2 hX, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `q hq`. Use `ContinuousAt.continuousWithinAt ?_` and prove the remaining obligations. Establish `hu : IsUnit (cT K E R (framePair K E R H Z (toM q.2))).det`.

Rewrite using `[det_cT]`. Conclude with `hq.2.map _`. Establish `hc : Continuous (fun q : HermSp K E R p × FrameSp K E R ι p ↦ cT K E R (framePair K E R H Z (toM q.2)))` using `(((continuous_framePair_left Z).comp continuous_snd).matrix_map (continuous_conjBase R)).matrix_transpose`. Establish `hinv : ContinuousAt (fun q : HermSp K E R p × FrameSp K E R ι p ↦ (cT K E R (framePair K E R H Z (toM q.2)))⁻¹) q` using `ContinuousAt.comp (g := Inv.inv) (continuousAt_matrix_inv_A hRu hRi _ hu) hc.continuousAt`. Establish `hS : Continuous (fun q : HermSp K E R p × FrameSp K E R ι p ↦ (2 : K)⁻¹ • q.1.mat)` using `(continuous_hermSpMat.comp continuous_fst).const_smul ((2 : K)⁻¹)`.

Establish `hf : ContinuousAt (fun q : HermSp K E R p × FrameSp K E R ι p ↦ ofM (toM q.2 + Z ⬝ ((cT K E R (framePair K E R H Z (toM q.2)))⁻¹ ⬝ ((2 : K)⁻¹ • q.1.mat))) : HermSp K E R p × FrameSp K E R ι p → FrameSp K E R ι p) q` using `continuous_ofM.continuousAt.comp ((continuous_toM.comp continuous_snd).continuousAt.add (continuousAt_mulM continuousAt_const (continuousAt_mulM hinv hS.continuousAt)))`. Use `hf.congr ?_` and prove the remaining obligations. Use `filter_upwards [(isOpen_univ.prod hΩ).mem_nhds hq] with q' hq'`. Use `show _ = ofM (toM q'.2 + Z ⬝ toM (chartShift H Z q'.1 q'.2))`. Rewrite using `[chartShift_of_mem hq'.2]`.

Both sides reduce to the same expression. Introduce `X hX`. Use `show ofM (toM X + Z ⬝ toM (chartShift H Z 0 X)) = X`. Rewrite using `[chartShift_of_mem hX]`. Use `show ofM (toM X + Z ⬝ shiftT (H := H) Z (toM X) 0) = X`.

Rewrite using `[shiftT_zero, Matrix.mul_zero, add_zero]`. Both sides reduce to the same expression. Introduce `S T X hX`. Establish `hX'` using `(mem_chartSet_chartAct hZ T X).2 hX`. Use `show ofM (toM (chartAct H Z T X) + Z ⬝ toM (chartShift H Z S (chartAct H Z T X))) = ofM (toM X + Z ⬝ toM (chartShift H Z (S + T) X))`.

Rewrite using `[chartShift_of_mem hX', chartShift_of_mem hX, toM_chartAct, chartShift_of_mem hX, shiftT_add_iso hZ]`. Use `show ofM (toM X + Z ⬝ shiftT (H := H) Z (toM X) T.mat + Z ⬝ shiftT (H := H) Z (toM X) S.mat) = ofM (toM X + Z ⬝ shiftT (H := H) Z (toM X) (S.mat + T.mat))`. Rewrite using `[shiftT_add, Matrix.mul_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws.

Introduce `S X hX`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show gram K E R H (toM X + Z ⬝ toM (chartShift H Z S X)) = gram K E R H (toM X) + S.mat`. Rewrite using `[chartShift_of_mem hX]`. Conclude with `gram_add_shiftT hH hZ hX S.2`.

Introduce `S`. Take `⟨B, hBc, hB0⟩` from `exists_compact_mem_nhds (0 : FrameSp K E R (Fin p) p)`. Set `ν : Measure (FrameSp K E R (Fin p) p)` to `Measure.addHaar`. Set `ζ : FrameSp K E R (Fin p) p →+ FrameSp K E R ι p` to `{ toFun := fun d ↦ ofM (Z ⬝ toM d) map_zero' := Matrix.mul_zero Z map_add' := fun d d' ↦ Matrix.mul_add Z _ _ }`. Establish `hζ : Continuous ζ` using `continuous_ofM.comp (continuous_const.matrix_mul continuous_toM)`.

Establish `hsh` using `measurePreserving_shear dX ν hBc.measurableSet (Measure.measure_pos_of_mem_nhds ν hB0).ne' hBc.measure_lt_top.ne ζ hζ.measurable (chartShift H Z S) (measurable_chartShift hRu hRi S) (fun X d ↦ chartShift_add_iso hZ S X d)`. Establish `hpre : (fun X ↦ X + ζ (chartShift H Z S X)) ⁻¹' chartSet R p H Z = chartSet R p H Z`. Use extensionality with `X`. Conclude with `mem_chartSet_chartAct hZ S X`. Use `hsh.restrict_preimage (isOpen_chartSet (H := H) (Z := Z) hRu).measurableSet` as an intermediate fact.

Rewrite `this` using `[hpre]`. Conclude with `this`.
-/
theorem isTransChart_chart [CharZero K] (hH : IsHermitianFor (conjHom K E) H)
    (hZ : gram K E R H Z = 0) (dX : Measure (FrameSp K E R ι p)) [dX.IsAddHaarMeasure] :
    IsTransChart dX (gramH R p hH) (chartSet R p H Z) (chartAct H Z) := by
  have hΩ : IsOpen (chartSet R p H Z) := isOpen_chartSet hRu
  refine ⟨hΩ, ?_, fun S X hX ↦ (mem_chartSet_chartAct hZ S X).2 hX, ?_, ?_, ?_, ?_⟩
  ·
    intro q hq
    refine ContinuousAt.continuousWithinAt ?_
    have hu : IsUnit (cT K E R (framePair K E R H Z (toM q.2))).det := by
      rw [det_cT]
      exact hq.2.map _
    have hc : Continuous (fun q : HermSp K E R p × FrameSp K E R ι p ↦
        cT K E R (framePair K E R H Z (toM q.2))) :=
      (((continuous_framePair_left Z).comp continuous_snd).matrix_map
        (continuous_conjBase R)).matrix_transpose
    have hinv : ContinuousAt (fun q : HermSp K E R p × FrameSp K E R ι p ↦
        (cT K E R (framePair K E R H Z (toM q.2)))⁻¹) q :=
      ContinuousAt.comp (g := Inv.inv) (continuousAt_matrix_inv_A hRu hRi _ hu) hc.continuousAt
    have hS : Continuous (fun q : HermSp K E R p × FrameSp K E R ι p ↦ (2 : K)⁻¹ • q.1.mat) :=
      (continuous_hermSpMat.comp continuous_fst).const_smul ((2 : K)⁻¹)
    have hf : ContinuousAt (fun q : HermSp K E R p × FrameSp K E R ι p ↦
        ofM (toM q.2 + Z ⬝ ((cT K E R (framePair K E R H Z (toM q.2)))⁻¹ ⬝
            ((2 : K)⁻¹ • q.1.mat))) : HermSp K E R p × FrameSp K E R ι p → FrameSp K E R ι p) q :=
      continuous_ofM.continuousAt.comp ((continuous_toM.comp continuous_snd).continuousAt.add
        (continuousAt_mulM continuousAt_const (continuousAt_mulM hinv hS.continuousAt)))
    refine hf.congr ?_
    filter_upwards [(isOpen_univ.prod hΩ).mem_nhds hq] with q' hq'
    show _ = ofM (toM q'.2 + Z ⬝ toM (chartShift H Z q'.1 q'.2))
    rw [chartShift_of_mem hq'.2]
    rfl
  ·
    intro X hX
    show ofM (toM X + Z ⬝ toM (chartShift H Z 0 X)) = X
    rw [chartShift_of_mem hX]
    show ofM (toM X + Z ⬝ shiftT (H := H) Z (toM X) 0) = X
    rw [shiftT_zero, Matrix.mul_zero, add_zero]
    rfl
  ·
    intro S T X hX
    have hX' := (mem_chartSet_chartAct hZ T X).2 hX
    show ofM (toM (chartAct H Z T X) + Z ⬝ toM (chartShift H Z S (chartAct H Z T X))) =
      ofM (toM X + Z ⬝ toM (chartShift H Z (S + T) X))
    rw [chartShift_of_mem hX', chartShift_of_mem hX, toM_chartAct, chartShift_of_mem hX,
      shiftT_add_iso hZ]
    show ofM (toM X + Z ⬝ shiftT (H := H) Z (toM X) T.mat + Z ⬝ shiftT (H := H) Z (toM X) S.mat) =
      ofM (toM X + Z ⬝ shiftT (H := H) Z (toM X) (S.mat + T.mat))
    rw [shiftT_add, Matrix.mul_add]
    congr 1
    abel
  ·
    intro S X hX
    apply Subtype.ext
    show gram K E R H (toM X + Z ⬝ toM (chartShift H Z S X)) = gram K E R H (toM X) + S.mat
    rw [chartShift_of_mem hX]
    exact gram_add_shiftT hH hZ hX S.2
  ·
    intro S
    obtain ⟨B, hBc, hB0⟩ := exists_compact_mem_nhds (0 : FrameSp K E R (Fin p) p)
    let ν : Measure (FrameSp K E R (Fin p) p) := Measure.addHaar
    let ζ : FrameSp K E R (Fin p) p →+ FrameSp K E R ι p :=
      { toFun := fun d ↦ ofM (Z ⬝ toM d)
        map_zero' := Matrix.mul_zero Z
        map_add' := fun d d' ↦ Matrix.mul_add Z _ _ }
    have hζ : Continuous ζ :=
      continuous_ofM.comp (continuous_const.matrix_mul continuous_toM)
    have hsh := measurePreserving_shear dX ν hBc.measurableSet
      (Measure.measure_pos_of_mem_nhds ν hB0).ne' hBc.measure_lt_top.ne ζ hζ.measurable
      (chartShift H Z S) (measurable_chartShift hRu hRi S) (fun X d ↦ chartShift_add_iso hZ S X d)
    have hpre : (fun X ↦ X + ζ (chartShift H Z S X)) ⁻¹' chartSet R p H Z = chartSet R p H Z := by
      ext X
      exact mem_chartSet_chartAct hZ S X
    have := hsh.restrict_preimage (isOpen_chartSet (H := H) (Z := Z) hRu).measurableSet
    rw [hpre] at this
    exact this

end

end Chart

end IsoFrames

end GroundTheory.Heights₂.Theta
