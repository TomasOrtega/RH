import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJStandardLDefs

open MeasureTheory Filter Set Topology Metric IsDedekindDomain NumberField NumberField.mixedEmbedding
open scoped NumberField.AdeleRing SchwartzMap Classical ENNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace GJStandardL

open GodementJacquet GLnLocal

set_option linter.unusedSectionVars false

section Local

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

/- English proof (translation)
Use `set U : Subgroup (GL (Fin n) F) := stabilizerOf π ξ ⊓ integralGL F n with hU`. Establish `hUo : IsOpen (U : Set (GL (Fin n) F))`. Rewrite using `[hU, Subgroup.coe_inf]`. Conclude with `(mem_smoothVectors.1 hξ).inter (isOpen_integralGL F n)`. Establish `hUc : IsCompact (U : Set (GL (Fin n) F))` using `(isCompact_integralGL F n).of_isClosed_subset (Subgroup.isClosed_of_isOpen U hUo) (by rw [hU, Subgroup.coe_inf]; exact inter_subset_right)`.

Use `set W : Set (GL (Fin n) F) := (g₀ * ·) '' (U : Set (GL (Fin n) F)) with hW`. Establish `hWo : IsOpen W` using `(Homeomorph.mulLeft g₀).isOpenMap _ hUo`. Establish `hWc : IsCompact W` using `hUc.image (continuous_const_mul g₀)`. Establish `hWm : MeasurableSet W` using `hWo.measurableSet`. Establish `hg₀ : g₀ ∈ W` using `⟨1, U.one_mem, mul_one g₀⟩`.

Establish `hval` using `Measures.isOpenEmbedding_val F n`. Use `set S : Set (Matrix (Fin n) (Fin n) F) := Units.val '' W with hS`. Establish `hSo : IsOpen S` using `hval.isOpenMap _ hWo`. Establish `hSc : IsCompact S` using `hWc.image Units.continuous_val`. Establish `hmemS : ∀ g : GL (Fin n) F, (g : Matrix (Fin n) (Fin n) F) ∈ S ↔ g ∈ W`.

Introduce `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, hh, he⟩`. Rewrite using `[← Units.ext he]` and apply the resulting hypothesis. Introduce `h`.

Conclude with `⟨g, h, rfl⟩`. Use `set Φ : Matrix (Fin n) (Fin n) F → ℂ := S.indicator fun _ ↦ (1 : ℂ) with hΦ`. Use `set c : ℂ := Parabolic.matrixCoeff π ξ ℓ g₀ with hc`. Establish `hfW : ∀ g ∈ W, Parabolic.matrixCoeff π ξ ℓ g = c`. Introduce and unpack `g ⟨u, hu, rfl⟩`.

Establish `hu1 : π u ξ = ξ` using `mem_stabilizerOf.1 (Subgroup.mem_inf.1 hu).1`. Simplify using `only [hc, Parabolic.matrixCoeff, map_mul, Module.End.mul_apply, hu1]`. Establish `hdW : ∀ g ∈ W, ∀ s, detPow g s = detPow g₀ s`. Introduce and unpack `g ⟨u, hu, rfl⟩ s`. Rewrite using `[detPow_mul, detPow_of_mem_integralGL (Subgroup.mem_inf.1 hu).2, mul_one]`.

Establish `hfun' : ∀ (s : ℂ) (g : GL (Fin n) F), Φ g * Parabolic.matrixCoeff π ξ ℓ g * detPow g s = W.indicator (fun _ ↦ c * detPow g₀ s) g`. Introduce `s g`. Distinguish the cases in `hg : g ∈ W`. Rewrite using `[hΦ, indicator_of_mem ((hmemS g).2 hg), indicator_of_mem hg, one_mul, hfW g hg, hdW g hg]`. Rewrite using `[hΦ, indicator_of_notMem (fun h ↦ hg ((hmemS g).1 h)), indicator_of_notMem hg, zero_mul, zero_mul]`.

Establish `hfun : ∀ s : ℂ, (fun g : GL (Fin n) F ↦ Φ g * Parabolic.matrixCoeff π ξ ℓ g * detPow g s) = W.indicator fun _ ↦ c * detPow g₀ s` using `fun s ↦ funext (hfun' s)`. Establish `hdne : ∀ s, detPow g₀ s ≠ 0` using `fun s ↦ by`. Rewrite using `[detPow_eq_qs_zpow]`. Conclude with `zpow_ne_zero _ (qs_ne_zero s)`. Establish `hWpos : 0 < μ.real W` using `ENNReal.toReal_pos (hWo.measure_pos μ ⟨g₀, hg₀⟩).ne' hWc.measure_lt_top.ne`.

Use `⟨Φ, ⟨?_, ?_⟩, (μ.real W : ℂ) * c, mul_ne_zero (by exact_mod_cast hWpos.ne') h0, fun s ↦ ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `X`. Distinguish the cases in `hX : X ∈ S`. Conclude with `⟨S, hSo, hX, fun Y hY ↦ by rw [hΦ, indicator_of_mem hY, indicator_of_mem hX]⟩`.

Conclude with `⟨Sᶜ, hSc.isClosed.isOpen_compl, hX, fun Y hY ↦ by`. Rewrite using `[hΦ, indicator_of_notMem hY, indicator_of_notMem hX]⟩`. Conclude with `HasCompactSupport.intro hSc fun x hx ↦ indicator_of_notMem hx _`. Rewrite using `[hfun]`. Conclude with `(integrableOn_const hWc.measure_lt_top.ne).integrable_indicator hWm`.

Repeatedly rewrite using `[hfun', enorm_indicator_eq_indicator_enorm]`. Rewrite using `[lintegral_indicator_const hWm]`. Conclude with `mul_ne_zero (enorm_ne_zero.2 (mul_ne_zero h0 (hdne _))) (hWo.measure_pos μ ⟨g₀, hg₀⟩).ne'`. Rewrite using `[zetaIntegral]`. Rewrite using `[hfun, integral_indicator_const _ hWm, Complex.real_smul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_localBump (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] {V : Type*} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) F) V) {ξ : V} (hξ : ξ ∈ smoothVectors π)
    (ℓ : Module.Dual ℂ V) {g₀ : GL (Fin n) F} (h0 : Parabolic.matrixCoeff π ξ ℓ g₀ ≠ 0) :
    ∃ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ ∧ ∃ a : ℂ, a ≠ 0 ∧ ∀ s : ℂ,
      Integrable (fun g : GL (Fin n) F ↦ Φ (g : Matrix (Fin n) (Fin n) F) * Parabolic.matrixCoeff π ξ ℓ g *
        detPow g (s + ((n : ℂ) - 1) / 2)) μ ∧
      ∫⁻ g : GL (Fin n) F, ‖Φ (g : Matrix (Fin n) (Fin n) F) * Parabolic.matrixCoeff π ξ ℓ g *
        detPow g (s + ((n : ℂ) - 1) / 2)‖ₑ ∂μ ≠ 0 ∧
      zetaIntegral μ Φ (Parabolic.matrixCoeff π ξ ℓ) s = a * detPow g₀ (s + ((n : ℂ) - 1) / 2) := by
  set U : Subgroup (GL (Fin n) F) := stabilizerOf π ξ ⊓ integralGL F n with hU
  have hUo : IsOpen (U : Set (GL (Fin n) F)) := by
    rw [hU, Subgroup.coe_inf]
    exact (mem_smoothVectors.1 hξ).inter (isOpen_integralGL F n)
  have hUc : IsCompact (U : Set (GL (Fin n) F)) :=
    (isCompact_integralGL F n).of_isClosed_subset (Subgroup.isClosed_of_isOpen U hUo)
      (by rw [hU, Subgroup.coe_inf]; exact inter_subset_right)
  set W : Set (GL (Fin n) F) := (g₀ * ·) '' (U : Set (GL (Fin n) F)) with hW
  have hWo : IsOpen W := (Homeomorph.mulLeft g₀).isOpenMap _ hUo
  have hWc : IsCompact W := hUc.image (continuous_const_mul g₀)
  have hWm : MeasurableSet W := hWo.measurableSet
  have hg₀ : g₀ ∈ W := ⟨1, U.one_mem, mul_one g₀⟩
  have hval := Measures.isOpenEmbedding_val F n
  set S : Set (Matrix (Fin n) (Fin n) F) := Units.val '' W with hS
  have hSo : IsOpen S := hval.isOpenMap _ hWo
  have hSc : IsCompact S := hWc.image Units.continuous_val
  have hmemS : ∀ g : GL (Fin n) F, (g : Matrix (Fin n) (Fin n) F) ∈ S ↔ g ∈ W := by
    intro g
    constructor
    · rintro ⟨h, hh, he⟩
      rwa [← Units.ext he]
    · intro h
      exact ⟨g, h, rfl⟩
  set Φ : Matrix (Fin n) (Fin n) F → ℂ := S.indicator fun _ ↦ (1 : ℂ) with hΦ
  set c : ℂ := Parabolic.matrixCoeff π ξ ℓ g₀ with hc
  have hfW : ∀ g ∈ W, Parabolic.matrixCoeff π ξ ℓ g = c := by
    rintro g ⟨u, hu, rfl⟩
    have hu1 : π u ξ = ξ := mem_stabilizerOf.1 (Subgroup.mem_inf.1 hu).1
    simp only [hc, Parabolic.matrixCoeff, map_mul, Module.End.mul_apply, hu1]
  have hdW : ∀ g ∈ W, ∀ s, detPow g s = detPow g₀ s := by
    rintro g ⟨u, hu, rfl⟩ s
    rw [detPow_mul, detPow_of_mem_integralGL (Subgroup.mem_inf.1 hu).2, mul_one]
  have hfun' : ∀ (s : ℂ) (g : GL (Fin n) F), Φ g * Parabolic.matrixCoeff π ξ ℓ g * detPow g s =
      W.indicator (fun _ ↦ c * detPow g₀ s) g := by
    intro s g
    by_cases hg : g ∈ W
    · rw [hΦ, indicator_of_mem ((hmemS g).2 hg), indicator_of_mem hg, one_mul, hfW g hg, hdW g hg]
    · rw [hΦ, indicator_of_notMem (fun h ↦ hg ((hmemS g).1 h)), indicator_of_notMem hg, zero_mul,
        zero_mul]
  have hfun : ∀ s : ℂ, (fun g : GL (Fin n) F ↦ Φ g * Parabolic.matrixCoeff π ξ ℓ g * detPow g s) =
      W.indicator fun _ ↦ c * detPow g₀ s := fun s ↦ funext (hfun' s)
  have hdne : ∀ s, detPow g₀ s ≠ 0 := fun s ↦ by
    rw [detPow_eq_qs_zpow]
    exact zpow_ne_zero _ (qs_ne_zero s)
  have hWpos : 0 < μ.real W :=
    ENNReal.toReal_pos (hWo.measure_pos μ ⟨g₀, hg₀⟩).ne' hWc.measure_lt_top.ne
  refine ⟨Φ, ⟨?_, ?_⟩, (μ.real W : ℂ) * c, mul_ne_zero (by exact_mod_cast hWpos.ne') h0, fun s ↦ ⟨?_, ?_, ?_⟩⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro X
    by_cases hX : X ∈ S
    · exact ⟨S, hSo, hX, fun Y hY ↦ by rw [hΦ, indicator_of_mem hY, indicator_of_mem hX]⟩
    · exact ⟨Sᶜ, hSc.isClosed.isOpen_compl, hX, fun Y hY ↦ by
        rw [hΦ, indicator_of_notMem hY, indicator_of_notMem hX]⟩
  · exact HasCompactSupport.intro hSc fun x hx ↦ indicator_of_notMem hx _
  · rw [hfun]
    exact (integrableOn_const hWc.measure_lt_top.ne).integrable_indicator hWm
  · simp_rw [hfun', enorm_indicator_eq_indicator_enorm]
    rw [lintegral_indicator_const hWm]
    exact mul_ne_zero (enorm_ne_zero.2 (mul_ne_zero h0 (hdne _))) (hWo.measure_pos μ ⟨g₀, hg₀⟩).ne'
  · rw [zetaIntegral]
    rw [hfun, integral_indicator_const _ hWm, Complex.real_smul]
    ring

end Local

section Arch

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩ w hw`. Establish `h` using `congrFun u.mul_inv w`. Express the relevant statement in the definitionally equal form `(u : InfiniteAdeleRing K) w * (↑u⁻¹ : InfiniteAdeleRing K) w = 1 at h`. Rewrite `h` using `[hw, zero_mul]`.

Conclude with `zero_ne_one h`. Introduce `h`. Use `⟨⟨x, fun w ↦ (x w)⁻¹, ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Conclude with `mul_inv_cancel₀ (h w)`.

Use function extensionality and compare the values at `w`. Conclude with `inv_mul_cancel₀ (h w)`.
-/
theorem isUnit_infiniteAdeleRing_iff {x : InfiniteAdeleRing K} :
    IsUnit x ↔ ∀ w : InfinitePlace K, x w ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩ w hw
    have h := congrFun u.mul_inv w
    change (u : InfiniteAdeleRing K) w * (↑u⁻¹ : InfiniteAdeleRing K) w = 1 at h
    rw [hw, zero_mul] at h
    exact zero_ne_one h
  · intro h
    refine ⟨⟨x, fun w ↦ (x w)⁻¹, ?_, ?_⟩, rfl⟩
    · funext w
      exact mul_inv_cancel₀ (h w)
    · funext w
      exact inv_mul_cancel₀ (h w)

def infInv (x : InfiniteAdeleRing K) : InfiniteAdeleRing K := fun w ↦ (x w)⁻¹

/- English proof (translation)
Establish `h1 : Ring.inverse x * x = 1` using `Ring.inverse_mul_cancel x hx`. Use function extensionality and compare the values at `w`. Establish `h2` using `congrFun h1 w`. Conclude with `eq_inv_of_mul_eq_one_left h2`.
-/
theorem ringInverse_eq_infInv {x : InfiniteAdeleRing K} (hx : IsUnit x) : Ring.inverse x = infInv x := by
  have h1 : Ring.inverse x * x = 1 := Ring.inverse_mul_cancel x hx
  funext w
  have h2 := congrFun h1 w
  exact eq_inv_of_mul_eq_one_left h2

variable (K n) in

/- English proof (translation)
Establish `hdet : Continuous fun A : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) ↦ A.det` using `Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)))`. Use `⟨Units.isEmbedding_val_mk' (f := fun A ↦ infInv A.det • A.adjugate) ?_ fun u ↦ ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : ContinuousOn (fun A : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) ↦ ((fun w ↦ (A.det w)⁻¹ : ∀ w : InfinitePlace K, w.Completion))) {A | IsUnit A}`. Use `continuousOn_pi.2 fun w ↦ ?_` and prove the remaining obligations. Conclude with `((continuous_apply (A := fun v : InfinitePlace K ↦ v.Completion) w).comp hdet).continuousOn.inv₀ fun A hA ↦ isUnit_infiniteAdeleRing_iff.1 ((Matrix.isUnit_iff_isUnit_det A).1 hA) w`.

Establish `h2 : Continuous fun A : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) ↦ A.adjugate` using `Continuous.matrix_adjugate (continuous_id (X := Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)))`. Conclude with `ContinuousOn.smul (M := InfiniteAdeleRing K) h1 h2.continuousOn`. Establish `hu : IsUnit (u : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).det` using `(Matrix.isUnit_iff_isUnit_det _).1 u.isUnit show infInv (u : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).det • (u : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).adjugate = ↑u⁻¹`. Rewrite using `[Matrix.coe_units_inv, Matrix.inv_def, ringInverse_eq_infInv hu]`. Establish `: Set.range (Units.val : AdelicGLn.InfiniteAdelicGL K n → Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) = ⋂ w : InfinitePlace K, (fun A : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) ↦ A.det w) ⁻¹' {0}ᶜ`.

Use extensionality with `A`. Simplify using `only [Set.mem_range, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩`. Conclude with `isUnit_infiniteAdeleRing_iff.1 ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)`.

Introduce `h`. Conclude with `⟨((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_infiniteAdeleRing_iff.2 h)).unit, rfl⟩`. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun w ↦ isOpen_compl_singleton.preimage ((continuous_apply w).comp hdet)`.
-/
theorem isOpenEmbedding_val_infiniteAdelicGL :
    IsOpenEmbedding (Units.val : AdelicGLn.InfiniteAdelicGL K n → Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) := by
  have hdet : Continuous fun A : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) ↦ A.det :=
    Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)))
  refine ⟨Units.isEmbedding_val_mk' (f := fun A ↦ infInv A.det • A.adjugate) ?_ fun u ↦ ?_, ?_⟩
  · have h1 : ContinuousOn (fun A : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) ↦
        ((fun w ↦ (A.det w)⁻¹ : ∀ w : InfinitePlace K, w.Completion))) {A | IsUnit A} := by
      refine continuousOn_pi.2 fun w ↦ ?_
      exact ((continuous_apply (A := fun v : InfinitePlace K ↦ v.Completion) w).comp hdet).continuousOn.inv₀
        fun A hA ↦ isUnit_infiniteAdeleRing_iff.1 ((Matrix.isUnit_iff_isUnit_det A).1 hA) w
    have h2 : Continuous fun A : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) ↦ A.adjugate :=
      Continuous.matrix_adjugate (continuous_id (X := Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)))
    exact ContinuousOn.smul (M := InfiniteAdeleRing K) h1 h2.continuousOn
  · have hu : IsUnit (u : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
    show infInv (u : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).det •
      (u : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).adjugate = ↑u⁻¹
    rw [Matrix.coe_units_inv, Matrix.inv_def, ringInverse_eq_infInv hu]
  · have : Set.range (Units.val : AdelicGLn.InfiniteAdelicGL K n → Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) =
        ⋂ w : InfinitePlace K, (fun A : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) ↦ A.det w) ⁻¹' {0}ᶜ := by
      ext A
      simp only [Set.mem_range, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨u, rfl⟩
        exact isUnit_infiniteAdeleRing_iff.1 ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)
      · intro h
        exact ⟨((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_infiniteAdeleRing_iff.2 h)).unit, rfl⟩
    rw [this]
    exact isOpen_iInter_of_finite fun w ↦
      isOpen_compl_singleton.preimage ((continuous_apply w).comp hdet)

variable (K n) in

def archEntries : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) ≃ₜ (Fin n × Fin n → mixedSpace K) where
  toFun x ij := GroundTheory.Global.homeomorphMixedSpace K (x ij.1 ij.2)
  invFun y := Matrix.of fun i j ↦ (GroundTheory.Global.homeomorphMixedSpace K).symm (y (i, j))
  left_inv x := by
    ext i j
    simp
  right_inv y := by
    funext ij
    simp
  continuous_toFun := continuous_pi fun ij ↦ (GroundTheory.Global.homeomorphMixedSpace K).continuous.comp
    ((continuous_apply ij.2).comp (continuous_apply ij.1))
  continuous_invFun := continuous_pi fun i ↦ continuous_pi fun j ↦
    (GroundTheory.Global.homeomorphMixedSpace K).symm.continuous.comp (continuous_apply (i, j))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem archSchwartz_eq (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ))
    (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) : archSchwartz φ x = φ (archEntries K n x) := rfl

/- English proof (translation)
Establish `hu : IsUnit (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).det` using `(Matrix.isUnit_iff_isUnit_det _).1 x.isUnit`. Conclude with `Finset.prod_pos fun w _ ↦ pow_pos (norm_pos_iff.2 (isUnit_infiniteAdeleRing_iff.1 hu w)) _`.
-/
theorem archAbsDet_pos (x : AdelicGLn.InfiniteAdelicGL K n) : 0 < archAbsDet x := by
  have hu : IsUnit (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
  exact Finset.prod_pos fun w _ ↦ pow_pos (norm_pos_iff.2 (isUnit_infiniteAdeleRing_iff.1 hu w)) _

/- English proof (translation)
The claim follows from `(Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)))).comp Units.continuous_val`.
-/
theorem continuous_det_infiniteAdelicGL :
    Continuous fun x : AdelicGLn.InfiniteAdelicGL K n ↦ (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).det :=
  (Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)))).comp
    Units.continuous_val

/- English proof (translation)
Use `continuous_finsetProd _ fun w _ ↦ ?_` and prove the remaining obligations. Establish `h : Continuous fun x : AdelicGLn.InfiniteAdelicGL K n ↦ (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).det w` using `(continuous_apply (A := fun v : InfinitePlace K ↦ v.Completion) w).comp continuous_det_infiniteAdelicGL`. Conclude with `(continuous_norm.comp h).pow _`.
-/
theorem continuous_archAbsDet : Continuous (archAbsDet (K := K) (n := n)) := by
  refine continuous_finsetProd _ fun w _ ↦ ?_
  have h : Continuous fun x : AdelicGLn.InfiniteAdelicGL K n ↦
      (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).det w :=
    (continuous_apply (A := fun v : InfinitePlace K ↦ v.Completion) w).comp continuous_det_infiniteAdelicGL
  exact (continuous_norm.comp h).pow _

/- English proof (translation)
The claim follows from `(Complex.continuous_ofReal.comp continuous_archAbsDet).cpow continuous_const fun x ↦ Complex.ofReal_mem_slitPlane.2 (archAbsDet_pos x)`.
-/
theorem continuous_archDetPow (s : ℂ) : Continuous fun x : AdelicGLn.InfiniteAdelicGL K n ↦ archDetPow x s :=
  (Complex.continuous_ofReal.comp continuous_archAbsDet).cpow continuous_const fun x ↦
    Complex.ofReal_mem_slitPlane.2 (archAbsDet_pos x)

/- English proof (translation)
Rewrite using `[archDetPow, Ne, Complex.cpow_eq_zero_iff]`. Conclude with `fun h ↦ (archAbsDet_pos x).ne' (by exact_mod_cast h.1)`.
-/
theorem archDetPow_ne_zero (x : AdelicGLn.InfiniteAdelicGL K n) (s : ℂ) : archDetPow x s ≠ 0 := by
  rw [archDetPow, Ne, Complex.cpow_eq_zero_iff]
  exact fun h ↦ (archAbsDet_pos x).ne' (by exact_mod_cast h.1)

/- English proof (translation)
Use `set J : AdelicGLn.InfiniteAdelicGL K n → (Fin n × Fin n → mixedSpace K) := fun x ↦ archEntries K n (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) with hJdef`. Establish `hJ : IsOpenEmbedding J` using `(archEntries K n).isOpenEmbedding.comp (isOpenEmbedding_val_infiniteAdelicGL K n)`. Use `set c₀ : ℂ := f x₀ with hc₀`. Use `set W : Set (AdelicGLn.InfiniteAdelicGL K n) := {x | 0 < (starRingEnd ℂ c₀ * f x).re} with hWdef`. Establish `hWo : IsOpen W` using `isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_const.mul hf))`.

Establish `hc₀re : 0 < (starRingEnd ℂ c₀ * c₀).re`. Rewrite using `[Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]`. Conclude with `pow_pos (norm_pos_iff.2 h0) 2`. Establish `hx₀W : x₀ ∈ W` using `hc₀re`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 (hJ.isOpenMap W hWo) (J x₀) ⟨x₀, hx₀W, rfl⟩`.

Set `ψ : ContDiffBump (J x₀)` to `⟨ε / 4, ε / 2, by positivity, by linarith⟩`. Establish `hψc : HasCompactSupport fun y ↦ (ψ y : ℂ)` using `ψ.hasCompactSupport.comp_left Complex.ofReal_zero`. Establish `hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y ↦ (ψ y : ℂ)` using `Complex.ofRealCLM.contDiff.comp ψ.contDiff`. Use `set φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ) := hψc.toSchwartzMap hψd with hφdef`. Establish `hsub : closedBall (J x₀) (ε / 2) ⊆ J '' W` using `fun y hy ↦ hball (closedBall_subset_ball (by linarith) hy)`.

Establish `hKc : IsCompact (J ⁻¹' closedBall (J x₀) (ε / 2))`. Rewrite using `[hJ.isEmbedding.isCompact_iff, image_preimage_eq_of_subset (hsub.trans (image_subset_range _ _))]`. Conclude with `isCompact_closedBall _ _`. Establish `hψzero : ∀ x, x ∉ J ⁻¹' closedBall (J x₀) (ε / 2) → ψ (J x) = 0`. Introduce `x hx`.

Assume the negation of the conclusion as `h`. Establish `: J x ∈ Function.support ψ` using `h`. Rewrite `this` using `[ψ.support_eq]`. Conclude with `hx (ball_subset_closedBall this)`. Establish `hψW : ∀ x, ψ (J x) ≠ 0 → x ∈ W`.

Introduce `x hx`. Establish `: J x ∈ Function.support ψ` using `hx`. Rewrite `this` using `[ψ.support_eq]`. Take `⟨y, hy, hyx⟩` from `hball (ball_subset_ball (show ψ.rOut ≤ ε from by show ε / 2 ≤ ε; linarith) this)`. Rewrite using `[← hJ.injective hyx]` and apply the resulting hypothesis.

Establish `hcontψ : Continuous fun x ↦ (ψ (J x) : ℂ)` using `Complex.continuous_ofReal.comp (ψ.continuous.comp hJ.continuous)`. Establish `hint_eq : ∀ s x, archIntegrand φ f s x = (ψ (J x) : ℂ) * f x * archDetPow x (s + ((n : ℂ) - 1) / 2)` using `fun s x ↦ rfl`. Establish `hcont : ∀ s, Continuous (archIntegrand φ f s)` using `fun s ↦ by`. Establish `: archIntegrand φ f s = fun x ↦ (ψ (J x) : ℂ) * f x * archDetPow x (s + ((n : ℂ) - 1) / 2)`. Use function extensionality and compare the values at `(hint_eq s)`.

Rewrite using `[this]`. Conclude with `(hcontψ.mul hf).mul (continuous_archDetPow _)`. Establish `hcs : ∀ s, HasCompactSupport (archIntegrand φ f s)` using `fun s ↦ HasCompactSupport.intro hKc fun x hx ↦ by`. Rewrite using `[hint_eq, hψzero x hx, Complex.ofReal_zero, zero_mul, zero_mul]`. Establish `hInt : ∀ s, Integrable (archIntegrand φ f s) μ` using `fun s ↦ (hcont s).integrable_of_hasCompactSupport (hcs s)`.

Establish `hψ₀ : ψ (J x₀) = 1` using `ψ.one_of_mem_closedBall (mem_closedBall_self (by positivity))`. Establish `hne₀ : ∀ s, archIntegrand φ f s x₀ ≠ 0` using `fun s ↦ by`. Rewrite using `[hint_eq, hψ₀, Complex.ofReal_one, one_mul]`. Conclude with `mul_ne_zero h0 (archDetPow_ne_zero _ _)`. Use `⟨φ, hInt, fun s hzero ↦ ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `hae` using `(lintegral_eq_zero_iff' (hcont s).enorm.aemeasurable).1 hzero`. Establish `hae' : archIntegrand φ f s =ᵐ[μ] 0` using `hae.mono fun x hx ↦ enorm_eq_zero.1 hx`. Use `(Continuous.ae_eq_iff_eq μ (hcont s) continuous_const).1 hae'` as an intermediate fact. Conclude with `hne₀ s (congrFun this x₀)`. Introduce `s₀`.

Use `set c' : ℂ := ((n : ℂ) - 1) / 2 with hc'`. Use `set σ : ℝ := (s₀ + c').re with hσ`. Use `set A : AdelicGLn.InfiniteAdelicGL K n → ℝ := archAbsDet with hAdef`. Establish `hA : ∀ x, 0 < A x` using `archAbsDet_pos`. Establish `hAc : Continuous A` using `continuous_archAbsDet`.

Use `set g : AdelicGLn.InfiniteAdelicGL K n → ℂ := fun x ↦ (ψ (J x) : ℂ) * f x with hg`. Establish `hgc : Continuous g` using `hcontψ.mul hf`. Use `set F' : ℂ → AdelicGLn.InfiniteAdelicGL K n → ℂ := fun s x ↦ g x * ((A x : ℂ) ^ (s + c') * Complex.log (A x)) with hF'`. Use `set bound : AdelicGLn.InfiniteAdelicGL K n → ℝ := fun x ↦ ‖g x‖ * (A x ^ (σ - 1) + A x ^ (σ + 1)) * |Real.log (A x)| with hbound`. Establish `hderiv : ∀ x, ∀ s ∈ ball s₀ 1, HasDerivAt (fun s ↦ archIntegrand φ f s x) (F' s x) s`.

Introduce `x s _`. Establish `h1 : HasDerivAt (fun s : ℂ ↦ (A x : ℂ) ^ (s + c')) ((A x : ℂ) ^ (s + c') * Complex.log (A x) * 1) s` using `((hasDerivAt_id s).add_const c').const_cpow (Or.inl (by exact_mod_cast (hA x).ne'))`. Establish `h2` using `h1.const_mul (g x)`. Simplify using `only [mul_one] at h2`. Conclude with `h2`.

Establish `hbd : ∀ x, ∀ s ∈ ball s₀ 1, ‖F' s x‖ ≤ bound x`. Introduce `x s hs`. Establish `hre : |s.re - s₀.re| < 1`. Rewrite using `[← Complex.sub_re]`. Conclude with `(Complex.abs_re_le_norm _).trans_lt (by rwa [mem_ball, dist_eq_norm] at hs)`.

Establish `hnorm1 : ‖(A x : ℂ) ^ (s + c')‖ = A x ^ (s + c').re` using `Complex.norm_cpow_eq_rpow_re_of_pos (hA x) _`. Establish `hnorm2 : ‖Complex.log (A x : ℂ)‖ = |Real.log (A x)|`. Rewrite using `[← Complex.ofReal_log (hA x).le, Complex.norm_real, Real.norm_eq_abs]`. Establish `hexp : (s + c').re = s.re + c'.re` using `Complex.add_re _ _`. Establish `hσ' : σ = s₀.re + c'.re` using `Complex.add_re _ _`.

Establish `hrpow : A x ^ (s + c').re ≤ A x ^ (σ - 1) + A x ^ (σ + 1)`. Rewrite `hre` using `[abs_lt]`. Distinguish the cases in `h1 : 1 ≤ A x`. Combine the equalities or inequalities in the displayed calculation. Use `push Not at h1`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hF', hbound, norm_mul, hnorm1, hnorm2]`. Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrpow (abs_nonneg _)) (norm_nonneg _)`. Establish `hboundc : Continuous bound` using `((continuous_norm.comp hgc).mul ((hAc.rpow_const fun x ↦ Or.inl (hA x).ne').add (hAc.rpow_const fun x ↦ Or.inl (hA x).ne'))).mul (hAc.log fun x ↦ (hA x).ne').abs`.

Establish `hbint : Integrable bound μ`. Use `hboundc.integrable_of_hasCompactSupport (HasCompactSupport.intro hKc fun x hx ↦ ?_)` and prove the remaining obligations. Simplify using `only [hbound, hg, hψzero x hx, Complex.ofReal_zero, zero_mul, norm_zero]`. Establish `hF'c : Continuous (F' s₀)` using `hgc.mul ((continuous_archDetPow (s₀ + c')).mul ((Complex.continuous_ofReal.comp hAc).clog fun x ↦ Complex.ofReal_mem_slitPlane.2 (hA x)))`. Establish `key` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := fun s x ↦ archIntegrand φ f s x) (x₀ := s₀) (ball_mem_nhds s₀ one_pos) (Filter.Eventually.of_forall fun s ↦ (hcont s).aestronglyMeasurable) (hInt s₀) (F' := F') hF'c.aestronglyMeasurable (ae_of_all _ fun x s hs ↦ hbd …`.

Conclude with `key.2.differentiableAt`. Use `⟨-(((n : ℂ) - 1) / 2), fun hz ↦ ?_⟩` and prove the remaining obligations. Establish `hint1 : ∀ x, archIntegrand φ f (-(((n : ℂ) - 1) / 2)) x = (ψ (J x) : ℂ) * f x` using `fun x ↦ by`. Rewrite using `[hint_eq, neg_add_cancel, archDetPow, Complex.cpow_zero, mul_one]`. Use `set r : AdelicGLn.InfiniteAdelicGL K n → ℝ := fun x ↦ ψ (J x) * (starRingEnd ℂ c₀ * f x).re with hr`.

Establish `hr_eq : ∀ x, (starRingEnd ℂ c₀ * archIntegrand φ f (-(((n : ℂ) - 1) / 2)) x).re = r x` using `fun x ↦ by`. Rewrite using `[hint1, mul_left_comm, Complex.re_ofReal_mul]`. Establish `hrc : Continuous r` using `(ψ.continuous.comp hJ.continuous).mul (Complex.continuous_re.comp (continuous_const.mul hf))`. Establish `hr0 : 0 ≤ r` using `fun x ↦ by`. Distinguish the cases in `hx : ψ (J x) = 0`.

Simplify using `only [hr, hx, zero_mul, Pi.zero_apply, le_refl]`. Conclude with `mul_nonneg ψ.nonneg (hψW x hx).le`. Establish `hrint : Integrable r μ`. Use `hrc.integrable_of_hasCompactSupport (HasCompactSupport.intro hKc fun x hx ↦ ?_)` and prove the remaining obligations. Simplify using `only [hr, hψzero x hx, zero_mul]`.

Establish `hpos : 0 < ∫ x, r x ∂μ`. Rewrite using `[integral_pos_iff_support_of_nonneg hr0 hrint]`. Use `hrc.isOpen_support.measure_pos μ ⟨x₀, ?_⟩` and prove the remaining obligations. Use `show r x₀ ≠ 0`. Simplify using `only [hr, hψ₀, one_mul]`.

Conclude with `hc₀re.ne'`. Establish `hre` using `integral_re ((hInt (-(((n : ℂ) - 1) / 2))).const_mul (starRingEnd ℂ c₀))`. Simplify using `only [RCLike.re_to_complex] at hre`. Establish `heq : ∫ x, r x ∂μ = (starRingEnd ℂ c₀ * archZeta μ φ f (-(((n : ℂ) - 1) / 2))).re`. Rewrite using `[archZeta, ← integral_const_mul, ← hre]`.

Conclude with `integral_congr_ae (ae_of_all _ fun x ↦ (hr_eq x).symm)`. Rewrite `heq` using `[hz, mul_zero, Complex.zero_re]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_archBump (μ : Measure (AdelicGLn.InfiniteAdelicGL K n)) [μ.IsHaarMeasure]
    {f : AdelicGLn.InfiniteAdelicGL K n → ℂ} (hf : Continuous f) {x₀ : AdelicGLn.InfiniteAdelicGL K n}
    (h0 : f x₀ ≠ 0) :
    ∃ φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ), (∀ s, Integrable (archIntegrand φ f s) μ) ∧
      (∀ s, ∫⁻ x, ‖archIntegrand φ f s x‖ₑ ∂μ ≠ 0) ∧ Differentiable ℂ (archZeta μ φ f) ∧
      ∃ s, archZeta μ φ f s ≠ 0 := by
  set J : AdelicGLn.InfiniteAdelicGL K n → (Fin n × Fin n → mixedSpace K) :=
    fun x ↦ archEntries K n (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) with hJdef
  have hJ : IsOpenEmbedding J :=
    (archEntries K n).isOpenEmbedding.comp (isOpenEmbedding_val_infiniteAdelicGL K n)
  set c₀ : ℂ := f x₀ with hc₀
  set W : Set (AdelicGLn.InfiniteAdelicGL K n) := {x | 0 < (starRingEnd ℂ c₀ * f x).re} with hWdef
  have hWo : IsOpen W := isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_const.mul hf))
  have hc₀re : 0 < (starRingEnd ℂ c₀ * c₀).re := by
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    exact pow_pos (norm_pos_iff.2 h0) 2
  have hx₀W : x₀ ∈ W := hc₀re
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hJ.isOpenMap W hWo) (J x₀) ⟨x₀, hx₀W, rfl⟩
  let ψ : ContDiffBump (J x₀) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hψc : HasCompactSupport fun y ↦ (ψ y : ℂ) := ψ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y ↦ (ψ y : ℂ) := Complex.ofRealCLM.contDiff.comp ψ.contDiff
  set φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ) := hψc.toSchwartzMap hψd with hφdef
  have hsub : closedBall (J x₀) (ε / 2) ⊆ J '' W := fun y hy ↦
    hball (closedBall_subset_ball (by linarith) hy)
  have hKc : IsCompact (J ⁻¹' closedBall (J x₀) (ε / 2)) := by
    rw [hJ.isEmbedding.isCompact_iff, image_preimage_eq_of_subset (hsub.trans (image_subset_range _ _))]
    exact isCompact_closedBall _ _
  have hψzero : ∀ x, x ∉ J ⁻¹' closedBall (J x₀) (ε / 2) → ψ (J x) = 0 := by
    intro x hx
    by_contra h
    have : J x ∈ Function.support ψ := h
    rw [ψ.support_eq] at this
    exact hx (ball_subset_closedBall this)
  have hψW : ∀ x, ψ (J x) ≠ 0 → x ∈ W := by
    intro x hx
    have : J x ∈ Function.support ψ := hx
    rw [ψ.support_eq] at this
    obtain ⟨y, hy, hyx⟩ := hball (ball_subset_ball (show ψ.rOut ≤ ε from by show ε / 2 ≤ ε; linarith) this)
    rwa [← hJ.injective hyx]
  have hcontψ : Continuous fun x ↦ (ψ (J x) : ℂ) :=
    Complex.continuous_ofReal.comp (ψ.continuous.comp hJ.continuous)
  have hint_eq : ∀ s x, archIntegrand φ f s x =
      (ψ (J x) : ℂ) * f x * archDetPow x (s + ((n : ℂ) - 1) / 2) := fun s x ↦ rfl
  have hcont : ∀ s, Continuous (archIntegrand φ f s) := fun s ↦ by
    have : archIntegrand φ f s = fun x ↦ (ψ (J x) : ℂ) * f x * archDetPow x (s + ((n : ℂ) - 1) / 2) :=
      funext (hint_eq s)
    rw [this]
    exact (hcontψ.mul hf).mul (continuous_archDetPow _)
  have hcs : ∀ s, HasCompactSupport (archIntegrand φ f s) := fun s ↦
    HasCompactSupport.intro hKc fun x hx ↦ by
      rw [hint_eq, hψzero x hx, Complex.ofReal_zero, zero_mul, zero_mul]
  have hInt : ∀ s, Integrable (archIntegrand φ f s) μ := fun s ↦
    (hcont s).integrable_of_hasCompactSupport (hcs s)
  have hψ₀ : ψ (J x₀) = 1 := ψ.one_of_mem_closedBall (mem_closedBall_self (by positivity))
  have hne₀ : ∀ s, archIntegrand φ f s x₀ ≠ 0 := fun s ↦ by
    rw [hint_eq, hψ₀, Complex.ofReal_one, one_mul]
    exact mul_ne_zero h0 (archDetPow_ne_zero _ _)
  refine ⟨φ, hInt, fun s hzero ↦ ?_, ?_, ?_⟩
  · have hae := (lintegral_eq_zero_iff' (hcont s).enorm.aemeasurable).1 hzero
    have hae' : archIntegrand φ f s =ᵐ[μ] 0 := hae.mono fun x hx ↦ enorm_eq_zero.1 hx
    have := (Continuous.ae_eq_iff_eq μ (hcont s) continuous_const).1 hae'
    exact hne₀ s (congrFun this x₀)
  ·
    intro s₀
    set c' : ℂ := ((n : ℂ) - 1) / 2 with hc'
    set σ : ℝ := (s₀ + c').re with hσ
    set A : AdelicGLn.InfiniteAdelicGL K n → ℝ := archAbsDet with hAdef
    have hA : ∀ x, 0 < A x := archAbsDet_pos
    have hAc : Continuous A := continuous_archAbsDet
    set g : AdelicGLn.InfiniteAdelicGL K n → ℂ := fun x ↦ (ψ (J x) : ℂ) * f x with hg
    have hgc : Continuous g := hcontψ.mul hf
    set F' : ℂ → AdelicGLn.InfiniteAdelicGL K n → ℂ :=
      fun s x ↦ g x * ((A x : ℂ) ^ (s + c') * Complex.log (A x)) with hF'
    set bound : AdelicGLn.InfiniteAdelicGL K n → ℝ :=
      fun x ↦ ‖g x‖ * (A x ^ (σ - 1) + A x ^ (σ + 1)) * |Real.log (A x)| with hbound
    have hderiv : ∀ x, ∀ s ∈ ball s₀ 1, HasDerivAt (fun s ↦ archIntegrand φ f s x) (F' s x) s := by
      intro x s _
      have h1 : HasDerivAt (fun s : ℂ ↦ (A x : ℂ) ^ (s + c'))
          ((A x : ℂ) ^ (s + c') * Complex.log (A x) * 1) s :=
        ((hasDerivAt_id s).add_const c').const_cpow (Or.inl (by exact_mod_cast (hA x).ne'))
      have h2 := h1.const_mul (g x)
      simp only [mul_one] at h2
      exact h2
    have hbd : ∀ x, ∀ s ∈ ball s₀ 1, ‖F' s x‖ ≤ bound x := by
      intro x s hs
      have hre : |s.re - s₀.re| < 1 := by
        rw [← Complex.sub_re]
        exact (Complex.abs_re_le_norm _).trans_lt (by rwa [mem_ball, dist_eq_norm] at hs)
      have hnorm1 : ‖(A x : ℂ) ^ (s + c')‖ = A x ^ (s + c').re :=
        Complex.norm_cpow_eq_rpow_re_of_pos (hA x) _
      have hnorm2 : ‖Complex.log (A x : ℂ)‖ = |Real.log (A x)| := by
        rw [← Complex.ofReal_log (hA x).le, Complex.norm_real, Real.norm_eq_abs]
      have hexp : (s + c').re = s.re + c'.re := Complex.add_re _ _
      have hσ' : σ = s₀.re + c'.re := Complex.add_re _ _
      have hrpow : A x ^ (s + c').re ≤ A x ^ (σ - 1) + A x ^ (σ + 1) := by
        rw [abs_lt] at hre
        by_cases h1 : 1 ≤ A x
        · calc A x ^ (s + c').re ≤ A x ^ (σ + 1) :=
                Real.rpow_le_rpow_of_exponent_le h1 (by rw [hexp, hσ']; linarith)
            _ ≤ _ := le_add_of_nonneg_left (Real.rpow_nonneg (hA x).le _)
        · push Not at h1
          calc A x ^ (s + c').re ≤ A x ^ (σ - 1) :=
                Real.rpow_le_rpow_of_exponent_ge (hA x) h1.le (by rw [hexp, hσ']; linarith)
            _ ≤ _ := le_add_of_nonneg_right (Real.rpow_nonneg (hA x).le _)
      simp only [hF', hbound, norm_mul, hnorm1, hnorm2]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrpow (abs_nonneg _)) (norm_nonneg _)
    have hboundc : Continuous bound :=
      ((continuous_norm.comp hgc).mul ((hAc.rpow_const fun x ↦ Or.inl (hA x).ne').add
        (hAc.rpow_const fun x ↦ Or.inl (hA x).ne'))).mul (hAc.log fun x ↦ (hA x).ne').abs
    have hbint : Integrable bound μ := by
      refine hboundc.integrable_of_hasCompactSupport (HasCompactSupport.intro hKc fun x hx ↦ ?_)
      simp only [hbound, hg, hψzero x hx, Complex.ofReal_zero, zero_mul, norm_zero]
    have hF'c : Continuous (F' s₀) :=
      hgc.mul ((continuous_archDetPow (s₀ + c')).mul
        ((Complex.continuous_ofReal.comp hAc).clog fun x ↦ Complex.ofReal_mem_slitPlane.2 (hA x)))
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun s x ↦ archIntegrand φ f s x) (x₀ := s₀) (ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall fun s ↦ (hcont s).aestronglyMeasurable) (hInt s₀) (F' := F')
      hF'c.aestronglyMeasurable (ae_of_all _ fun x s hs ↦ hbd x s hs) hbint
      (ae_of_all _ fun x s hs ↦ hderiv x s hs)
    exact key.2.differentiableAt
  ·
    refine ⟨-(((n : ℂ) - 1) / 2), fun hz ↦ ?_⟩
    have hint1 : ∀ x, archIntegrand φ f (-(((n : ℂ) - 1) / 2)) x = (ψ (J x) : ℂ) * f x := fun x ↦ by
      rw [hint_eq, neg_add_cancel, archDetPow, Complex.cpow_zero, mul_one]
    set r : AdelicGLn.InfiniteAdelicGL K n → ℝ := fun x ↦ ψ (J x) * (starRingEnd ℂ c₀ * f x).re with hr
    have hr_eq : ∀ x, (starRingEnd ℂ c₀ * archIntegrand φ f (-(((n : ℂ) - 1) / 2)) x).re = r x := fun x ↦ by
      rw [hint1, mul_left_comm, Complex.re_ofReal_mul]
    have hrc : Continuous r :=
      (ψ.continuous.comp hJ.continuous).mul (Complex.continuous_re.comp (continuous_const.mul hf))
    have hr0 : 0 ≤ r := fun x ↦ by
      by_cases hx : ψ (J x) = 0
      · simp only [hr, hx, zero_mul, Pi.zero_apply, le_refl]
      · exact mul_nonneg ψ.nonneg (hψW x hx).le
    have hrint : Integrable r μ := by
      refine hrc.integrable_of_hasCompactSupport (HasCompactSupport.intro hKc fun x hx ↦ ?_)
      simp only [hr, hψzero x hx, zero_mul]
    have hpos : 0 < ∫ x, r x ∂μ := by
      rw [integral_pos_iff_support_of_nonneg hr0 hrint]
      refine hrc.isOpen_support.measure_pos μ ⟨x₀, ?_⟩
      show r x₀ ≠ 0
      simp only [hr, hψ₀, one_mul]
      exact hc₀re.ne'
    have hre := integral_re ((hInt (-(((n : ℂ) - 1) / 2))).const_mul (starRingEnd ℂ c₀))
    simp only [RCLike.re_to_complex] at hre
    have heq : ∫ x, r x ∂μ = (starRingEnd ℂ c₀ * archZeta μ φ f (-(((n : ℂ) - 1) / 2))).re := by
      rw [archZeta, ← integral_const_mul, ← hre]
      exact integral_congr_ae (ae_of_all _ fun x ↦ (hr_eq x).symm)
    rw [hz, mul_zero, Complex.zero_re] at heq
    linarith

end Arch

end GJStandardL

end

end GroundTheory.Automorphic
