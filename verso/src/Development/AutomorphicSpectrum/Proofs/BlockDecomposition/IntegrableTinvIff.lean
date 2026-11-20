import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2LocalData.HaarTinv

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((g * h)⁻¹ : GL (Fin 2) F).valᵀ = (g⁻¹ : GL (Fin 2) F).valᵀ * (h⁻¹ : GL (Fin 2) F).valᵀ`. Rewrite using `[_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]`.
-/
theorem tinv_mul (g h : GL (Fin 2) F) : tinv (g * h) = tinv g * tinv h := by
  apply Units.ext
  change ((g * h)⁻¹ : GL (Fin 2) F).valᵀ = (g⁻¹ : GL (Fin 2) F).valᵀ * (h⁻¹ : GL (Fin 2) F).valᵀ
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(g.valᵀ)ᵀ = g.val`. Simplify using the standard rewrite rules.
-/
theorem tinv_tinv (g : GL (Fin 2) F) : tinv (tinv g) = g := by
  apply Units.ext
  change (g.valᵀ)ᵀ = g.val
  simp

/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Conclude with `⟨(Units.continuous_coe_inv (M := Matrix (Fin 2) (Fin 2) F)).matrix_transpose, (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) F)).matrix_transpose⟩`.
-/
theorem continuous_tinv : Continuous (tinv : GL (Fin 2) F → GL (Fin 2) F) := by
  rw [Units.continuous_iff]
  exact ⟨(Units.continuous_coe_inv (M := Matrix (Fin 2) (Fin 2) F)).matrix_transpose,
    (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) F)).matrix_transpose⟩

def tinvEquiv : GL (Fin 2) F ≃* GL (Fin 2) F where
  toFun := tinv
  invFun := tinv
  left_inv := tinv_tinv
  right_inv := tinv_tinv
  map_mul' := tinv_mul

/- English proof (translation)
Establish `key : ∀ {k : GL (Fin 2) F}, k ∈ GLnLocal.integralGL F 2 → tinv k ∈ GLnLocal.integralGL F 2`. Introduce `k hk`. Take `⟨h1, h2⟩` from `(GLnLocal.mem_integralGL_iff F 2).1 hk`. Conclude with `(GLnLocal.mem_integralGL_iff F 2).2 ⟨fun i j => h2 j i, fun i j => h1 j i⟩`. Conclude with `⟨fun h => by simpa [tinv_tinv] using key h, key⟩`.
-/
theorem tinv_mem_iff (k : GL (Fin 2) F) :
    tinv k ∈ GLnLocal.integralGL F 2 ↔ k ∈ GLnLocal.integralGL F 2 := by
  have key : ∀ {k : GL (Fin 2) F}, k ∈ GLnLocal.integralGL F 2 → tinv k ∈ GLnLocal.integralGL F 2 := by
    intro k hk
    obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
    exact (GLnLocal.mem_integralGL_iff F 2).2 ⟨fun i j => h2 j i, fun i j => h1 j i⟩
  exact ⟨fun h => by simpa [tinv_tinv] using key h, key⟩

variable [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Establish `hc : Continuous (tinv : GL (Fin 2) F → GL (Fin 2) F)` using `continuous_tinv`. Establish `hm : Measurable (tinvEquiv (F` using `F)) := hc.measurable`. Use `haveI : (LFS.hG ψ).IsHaarMeasure := by unfold LFS.hG; infer_instance`. Use `haveI hH : ((LFS.hG ψ).map (tinvEquiv (F := F))).IsHaarMeasure := MulEquiv.isHaarMeasure_map (LFS.hG ψ) tinvEquiv hc hc`. Express the relevant statement in the definitionally equal form `(LFS.hG ψ).map (tinvEquiv (F := F)) = LFS.hG ψ`.

Use `set μ := LFS.hG ψ with hμ`. Use `set K := GLnLocal.integralGL F 2 with hKdef`. Establish `hKo : IsOpen (K : Set (GL (Fin 2) F))` using `GLnLocal.isOpen_integralGL F 2`. Establish `hK0 : μ K ≠ 0` using `hKo.measure_ne_zero μ ⟨1, K.one_mem⟩`. Establish `hKT : μ K ≠ ⊤` using `(GLnLocal.isCompact_integralGL F 2).measure_lt_top.ne`.

Establish `e` using `Measure.isMulLeftInvariant_eq_smul (μ.map (tinvEquiv (F := F))) μ`. Establish `hpre : (tinvEquiv (F` using `F)) ⁻¹' (K : Set (GL (Fin 2) F)) = K := by`. Use extensionality with `k`. Conclude with `tinv_mem_iff k`. Establish `hmap : (μ.map (tinvEquiv (F` using `F))) K = μ K := by`.

Rewrite using `[Measure.map_apply hm hKo.measurableSet]`. Conclude with `congrArg μ hpre`. Establish `hs : Measure.haarScalarFactor (μ.map (tinvEquiv (F` using `F))) μ = 1 := by`. Establish `h` using `congrArg (fun ν : Measure (GL (Fin 2) F) => ν K) e`. Simplify using `only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h`.

Rewrite `h` using `[hmap]`. Use `(ENNReal.mul_eq_right hK0 hKT).1 h.symm` as an intermediate fact. Conclude with `this` after adjusting the coercions. Rewrite using `[e, hs, one_smul]`.
-/
theorem map_tinv_hG (ψ : AddChar F Circle) :
    Measure.map (tinv : GL (Fin 2) F → GL (Fin 2) F) (LFS.hG ψ) = LFS.hG ψ := by
  have hc : Continuous (tinv : GL (Fin 2) F → GL (Fin 2) F) := continuous_tinv
  have hm : Measurable (tinvEquiv (F := F)) := hc.measurable
  haveI : (LFS.hG ψ).IsHaarMeasure := by unfold LFS.hG; infer_instance
  haveI hH : ((LFS.hG ψ).map (tinvEquiv (F := F))).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map (LFS.hG ψ) tinvEquiv hc hc
  change (LFS.hG ψ).map (tinvEquiv (F := F)) = LFS.hG ψ
  set μ := LFS.hG ψ with hμ
  set K := GLnLocal.integralGL F 2 with hKdef
  have hKo : IsOpen (K : Set (GL (Fin 2) F)) := GLnLocal.isOpen_integralGL F 2
  have hK0 : μ K ≠ 0 := hKo.measure_ne_zero μ ⟨1, K.one_mem⟩
  have hKT : μ K ≠ ⊤ := (GLnLocal.isCompact_integralGL F 2).measure_lt_top.ne
  have e := Measure.isMulLeftInvariant_eq_smul (μ.map (tinvEquiv (F := F))) μ
  have hpre : (tinvEquiv (F := F)) ⁻¹' (K : Set (GL (Fin 2) F)) = K := by
    ext k
    exact tinv_mem_iff k
  have hmap : (μ.map (tinvEquiv (F := F))) K = μ K := by
    rw [Measure.map_apply hm hKo.measurableSet]
    exact congrArg μ hpre
  have hs : Measure.haarScalarFactor (μ.map (tinvEquiv (F := F))) μ = 1 := by
    have h := congrArg (fun ν : Measure (GL (Fin 2) F) => ν K) e
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    rw [hmap] at h
    have := (ENNReal.mul_eq_right hK0 hKT).1 h.symm
    exact_mod_cast this
  rw [e, hs, one_smul]

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ ψ _` and use `map_tinv_hG ψ`.
-/
theorem tinv_hG : ForS fun F _ _ _ _ _ _ ψ =>
    Measure.map (tinv : GL (Fin 2) F → GL (Fin 2) F) (LFS.hG ψ) = LFS.hG ψ :=
  fun _ _ _ _ _ _ _ ψ _ => map_tinv_hG ψ

def tinvHomeo : GL (Fin 2) F ≃ₜ GL (Fin 2) F where
  toEquiv := (tinvEquiv (F := F)).toEquiv
  continuous_toFun := continuous_tinv
  continuous_invFun := continuous_tinv

/- English proof (translation)
Establish `he : MeasurableEmbedding (tinv : GL (Fin 2) F → GL (Fin 2) F)` using `(tinvHomeo (F := F)).measurableEmbedding`. Use `conv_rhs => rw [← map_tinv_hG ψ]`. Conclude with `(he.integral_map f).symm`.
-/
theorem integral_tinv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ψ : AddChar F Circle)
    (f : GL (Fin 2) F → E) : ∫ g, f (tinv g) ∂LFS.hG ψ = ∫ g, f g ∂LFS.hG ψ := by
  have he : MeasurableEmbedding (tinv : GL (Fin 2) F → GL (Fin 2) F) :=
    (tinvHomeo (F := F)).measurableEmbedding
  conv_rhs => rw [← map_tinv_hG ψ]
  exact (he.integral_map f).symm

/- English proof (translation)
Establish `he : MeasurableEmbedding (tinv : GL (Fin 2) F → GL (Fin 2) F)` using `(tinvHomeo (F := F)).measurableEmbedding`. Use `conv_rhs => rw [← map_tinv_hG ψ]`. Conclude with `(he.integrable_map_iff (f := tinv) (g := f)).symm`.
-/
theorem integrable_tinv_iff {E : Type*} [NormedAddCommGroup E] (ψ : AddChar F Circle)
    (f : GL (Fin 2) F → E) :
    Integrable (fun g => f (tinv g)) (LFS.hG ψ) ↔ Integrable f (LFS.hG ψ) := by
  have he : MeasurableEmbedding (tinv : GL (Fin 2) F → GL (Fin 2) F) :=
    (tinvHomeo (F := F)).measurableEmbedding
  conv_rhs => rw [← map_tinv_hG ψ]
  exact (he.integrable_map_iff (f := tinv) (g := f)).symm

end GlobalTheory.CompanionTheory.GL2LocalData.HaarTinv
