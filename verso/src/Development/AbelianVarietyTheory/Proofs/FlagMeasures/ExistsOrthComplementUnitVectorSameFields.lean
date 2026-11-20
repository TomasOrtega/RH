import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeVolumeEqOfSemilinearIsometryGenusStatement
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaussDensDefinite

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PerpReduce

section Lat

variable {E E' : Type} [Field E] [Field E'] {n : ℕ} (e : E' ≃+* E)

instance ringHomSurjective_mapRingEquiv : RingHomSurjective (RingOfIntegers.mapRingEquiv e : 𝓞 E' →+* 𝓞 E) :=
  ⟨(RingOfIntegers.mapRingEquiv e).surjective⟩

def vecMap (n : ℕ) : (Fin n → E') →ₛₗ[(RingOfIntegers.mapRingEquiv e : 𝓞 E' →+* 𝓞 E)] (Fin n → E) where
  toFun y := fun i => e (y i)
  map_add' a b := by funext i; simp
  map_smul' r a := by
    funext i
    show e ((r : E') * a i) = e (r : E') * e (a i)
    rw [map_mul]

def latMap (L : Submodule (𝓞 E') (Fin n → E')) : Submodule (𝓞 E) (Fin n → E) := L.map (vecMap e n)

/- English proof (translation)
Use `⟨fun ⟨z, hz, h⟩ => ?_, fun h => ⟨y, h, rfl⟩⟩` and prove the remaining obligations. Establish `: z = y` using `funext fun i => e.injective (congrFun h i)`. Conclude with `this ▸ hz`.
-/
theorem mem_latMap (L : Submodule (𝓞 E') (Fin n → E')) (y : Fin n → E') :
    (fun i => e (y i)) ∈ latMap e L ↔ y ∈ L := by
  refine ⟨fun ⟨z, hz, h⟩ => ?_, fun h => ⟨y, h, rfl⟩⟩
  have : z = y := funext fun i => e.injective (congrFun h i)
  exact this ▸ hz

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i => e.symm (x i), by funext i; simp⟩`.
-/
theorem exists_vec (x : Fin n → E) : ∃ y : Fin n → E', x = fun i => e (y i) :=
  ⟨fun i => e.symm (x i), by funext i; simp⟩

/- English proof (translation)
The claim follows from `h.map _`.
-/
theorem latMap_fg (L : Submodule (𝓞 E') (Fin n → E')) (h : L.FG) : (latMap e L).FG := h.map _

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce and unpack `x -`. Take `⟨y, rfl⟩` from `exists_vec e x`. Establish `hy : y ∈ Submodule.span E' (L : Set (Fin n → E'))` using `h ▸ Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy => exact Submodule.subset_span ((mem_latMap e L y).2 hy)`. Consider the case `zero`. Establish `: (fun i => e ((0 : Fin n → E') i)) = 0` using `by funext i; simp`. Rewrite using `[this]`. Conclude with `zero_mem _`.

Consider the case `add a b _ _ ha hb`. Establish `: (fun i => e ((a + b) i)) = (fun i => e (a i)) + (fun i => e (b i))` using `by funext i; simp`. Rewrite using `[this]`. Conclude with `add_mem ha hb`. Consider the case `smul r a _ ha`.

Establish `: (fun i => e ((r • a) i)) = e r • (fun i => e (a i))` using `by funext i; simp`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ ha`.
-/
theorem latMap_span (L : Submodule (𝓞 E') (Fin n → E'))
    (h : Submodule.span E' (L : Set (Fin n → E')) = ⊤) :
    Submodule.span E (latMap e L : Set (Fin n → E)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := exists_vec e x
  have hy : y ∈ Submodule.span E' (L : Set (Fin n → E')) := h ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ((mem_latMap e L y).2 hy)
  | zero =>
    have : (fun i => e ((0 : Fin n → E') i)) = 0 := by funext i; simp
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : (fun i => e ((a + b) i)) = (fun i => e (a i)) + (fun i => e (b i)) := by funext i; simp
    rw [this]; exact add_mem ha hb
  | smul r a _ ha =>
    have : (fun i => e ((r • a) i)) = e r • (fun i => e (a i)) := by funext i; simp
    rw [this]; exact Submodule.smul_mem _ _ ha

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb⟩`. Use `⟨RingOfIntegers.mapRingEquiv e.symm b, ?_⟩` and prove the remaining obligations. Use `show e.symm (b : E) = a`. Rewrite using `[show (b : E) = e a from hb]`.

Simplify using the standard rewrite rules. Introduce and unpack `⟨b, rfl⟩`. Conclude with `⟨RingOfIntegers.mapRingEquiv e b, rfl⟩`.
-/
theorem mem_range_iff (a : E') :
    e a ∈ (algebraMap (𝓞 E) E).range ↔ a ∈ (algebraMap (𝓞 E') E').range := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨RingOfIntegers.mapRingEquiv e.symm b, ?_⟩
    show e.symm (b : E) = a
    rw [show (b : E) = e a from hb]; simp
  · rintro ⟨b, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv e b, rfl⟩

variable [StarRing E] [StarRing E'] (he : ∀ y, e (star y) = star (e y))
include he

/- English proof (translation)
Simplify using `[Formalism.UG.hform, starRingEnd_apply, he]`.
-/
theorem hform_map (J : Matrix (Fin n) (Fin n) E') (y x : Fin n → E') :
    Formalism.UG.hform (starRingEnd E) (J.map e) (fun i => e (y i)) (fun i => e (x i)) =
      e (Formalism.UG.hform (starRingEnd E') J y x) := by
  simp [Formalism.UG.hform, starRingEnd_apply, he]

/- English proof (translation)
Use extensionality with `i j`. Establish `h : star (J j i) = J i j` using `congrFun (congrFun hJ i) j`. Use `show star (e (J j i)) = e (J i j)`. Rewrite using `[← h, he]`.
-/
theorem isHerm_map {J : Matrix (Fin n) (Fin n) E'} (hJ : Formalism.UG.IsHerm (starRingEnd E') J) :
    Formalism.UG.IsHerm (starRingEnd E) (J.map e) := by
  ext i j
  have h : star (J j i) = J i j := congrFun (congrFun hJ i) j
  show star (e (J j i)) = e (J i j)
  rw [← h, he]

/- English proof (translation)
Take `⟨x, rfl⟩` from `exists_vec e x`. Rewrite using `[mem_latMap, h]`. Use `⟨fun H y hy => ?_, fun H y hy => ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `exists_vec e y`. Rewrite using `[hform_map e he, mem_range_iff]`.

Conclude with `H y ((mem_latMap e L y).1 hy)`. Rewrite using `[← mem_range_iff e, ← hform_map e he]`. Conclude with `H _ ((mem_latMap e L y).2 hy)`.
-/
theorem latMap_dual {J : Matrix (Fin n) (Fin n) E'} {L : Submodule (𝓞 E') (Fin n → E')}
    (h : ∀ x : Fin n → E', x ∈ L ↔
      ∀ y ∈ L, Formalism.UG.hform (starRingEnd E') J y x ∈ (algebraMap (𝓞 E') E').range) (x : Fin n → E) :
    x ∈ latMap e L ↔
      ∀ y ∈ latMap e L, Formalism.UG.hform (starRingEnd E) (J.map e) y x ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨x, rfl⟩ := exists_vec e x
  rw [mem_latMap, h]
  refine ⟨fun H y hy => ?_, fun H y hy => ?_⟩
  · obtain ⟨y, rfl⟩ := exists_vec e y
    rw [hform_map e he, mem_range_iff]
    exact H y ((mem_latMap e L y).1 hy)
  · rw [← mem_range_iff e, ← hform_map e he]
    exact H _ ((mem_latMap e L y).2 hy)

end Lat

/- English proof (translation)
Use `(IsUnit.mk0 _ h).map (e : E' →+* E)` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Conclude with `this.ne_zero`.
-/
theorem det_map_ne {E E' : Type} [Field E] [Field E'] {n : ℕ} (e : E' ≃+* E)
    {J : Matrix (Fin n) (Fin n) E'} (h : J.det ≠ 0) : (J.map e).det ≠ 0 := by
  have := (IsUnit.mk0 _ h).map (e : E' →+* E)
  rw [RingHom.map_det] at this
  exact this.ne_zero

def sibOf (I I' : AutInst) (e : I'.E ≃+* I.E) (he : ∀ y, e (star y) = star (e y)) : Sib I :=
  have h := fun v : InfinitePlace I.F =>
    GlobalTheory.AutInhab.exists_frame (GlobalTheory.AutInhab.isHerm_map I.cm (isHerm_map e he I'.J_herm) (I.φ v))
      (GlobalTheory.AutInhab.isUnit_det_map (det_map_ne e I'.J_det) (I.φ v))
  { n := I'.n
    J := I'.J.map e
    J_herm := isHerm_map e he I'.J_herm
    J_det := det_map_ne e I'.J_det
    L := latMap e I'.L
    L_span := latMap_span e _ I'.L_span
    L_fg := latMap_fg e _ I'.L_fg
    L_dual := latMap_dual e he I'.L_dual
    ε := fun v => (h v).choose
    P := fun v => (h v).choose_spec.choose
    P_unit := fun v => (h v).choose_spec.choose_spec.1
    P_spec := fun v => (h v).choose_spec.choose_spec.2 }

/- English proof (translation)
Introduce `I I' e s x A xf ⟨he, hn, hx, hxA, hA, hxL, hL⟩`. Use `⟨sibOf I I' e he, A, ⟨hn, hx, hxA, hA, hxL, fun y => ?_⟩, ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `exists_vec (n := I'.n) e y`. Conclude with `(mem_latMap e I'.L y).trans (hL y)`. Introduce `c μ _ _ c' μ' _ _ hc hc'`.

Use `GlobalTheory.T.gaugeVolume_eq_of_semilinear_isometry_genus (sibOf I I' e he).inst I' e (1 : Matrix (Fin I'.n) (Fin I'.n) I.E) 1 he rfl ?_ (fun y => ?_) c μ c' μ' hc hc'` and prove the remaining obligations. Use `show (1 : Matrix (Fin I'.n) (Fin I'.n) I.E)ᴴ * I'.J.map e * (1 : Matrix (Fin I'.n) (Fin I'.n) I.E) = I'.J.map e`. Rewrite using `[Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[GlobalTheory.GaussMean.Test.lamX_one] show _ ↔ (1 : Matrix (Fin I'.n) (Fin I'.n) I.E) *ᵥ (fun i => e (y i)) ∈ latMap e I'.L`. Rewrite using `[Matrix.one_mulVec, mem_latMap]`.
-/
theorem exists_sib : ∀ (I I' : AutInst) (e : I'.E ≃+* I.E) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), IsPerpInst I I' e s x A xf → ∃ (D : Sib I) (B : Matrix (Fin I.n) (Fin D.n) I.E), IsPerp D s x B xf ∧ ∀ (c : InfinitePlace I.F → ℝ) (μ : Measure D.inst.Gf) [SigmaFinite μ] [μ.IsHaarMeasure] (c' : InfinitePlace I'.F → ℝ) (μ' : Measure I'.Gf) [SigmaFinite μ'] [μ'.IsHaarMeasure], IsGaugeAll D.inst c → IsGaugeAll I' c' → gaugeVol D.inst c μ = gaugeVol I' c' μ' := by
  intro I I' e s x A xf ⟨he, hn, hx, hxA, hA, hxL, hL⟩
  refine ⟨sibOf I I' e he, A, ⟨hn, hx, hxA, hA, hxL, fun y => ?_⟩, ?_⟩
  · obtain ⟨y, rfl⟩ := exists_vec (n := I'.n) e y
    exact (mem_latMap e I'.L y).trans (hL y)
  · intro c μ _ _ c' μ' _ _ hc hc'
    refine GlobalTheory.T.gaugeVolume_eq_of_semilinear_isometry_genus (sibOf I I' e he).inst I' e (1 : Matrix (Fin I'.n) (Fin I'.n) I.E) 1 he rfl ?_
      (fun y => ?_) c μ c' μ' hc hc'
    · show (1 : Matrix (Fin I'.n) (Fin I'.n) I.E)ᴴ * I'.J.map e * (1 : Matrix (Fin I'.n) (Fin I'.n) I.E) =
        I'.J.map e
      rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    · rw [GlobalTheory.GaussMean.Test.lamX_one]
      show _ ↔ (1 : Matrix (Fin I'.n) (Fin I'.n) I.E) *ᵥ (fun i => e (y i)) ∈ latMap e I'.L
      rw [Matrix.one_mulVec, mem_latMap]

end GlobalTheory.PerpReduce
