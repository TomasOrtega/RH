import Mathlib
import GroundTheory.AutomorphicForms.HeckeIrreducible
import GroundTheory.AutomorphicForms.MeasuresGL

noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory Measure Matrix GLnLocal HeckeAlgebra

namespace Spherical

variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)

def transposeInv : GL (Fin n) F ≃* GL (Fin n) F where
  toFun g := ⟨((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ,
    ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  invFun g := ⟨((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ,
    ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  left_inv g := Units.ext (transpose_transpose _)
  right_inv g := Units.ext (transpose_transpose _)
  map_mul' g h := Units.ext (by
    change (((g * h)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ =
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ * ((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, transpose_mul])

variable {F n}

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem coe_transposeInv (g : GL (Fin n) F) :
    ((transposeInv F n g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ := rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_inv_transposeInv (g : GL (Fin n) F) :
    (((transposeInv F n g)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ := rfl

/- English proof (translation)
The claim follows from `(transposeInv F n).left_inv g`.
-/
theorem transposeInv_transposeInv (g : GL (Fin n) F) : transposeInv F n (transposeInv F n g) = g :=
  (transposeInv F n).left_inv g

/- English proof (translation)
Rewrite `hk`, the goal using `[mem_integralGL_iff]`. Conclude with `⟨fun i j => hk.2 j i, fun i j => hk.1 j i⟩`.
-/
theorem transposeInv_mem_integralGL {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    transposeInv F n k ∈ integralGL F n := by
  rw [mem_integralGL_iff] at hk ⊢
  exact ⟨fun i j => hk.2 j i, fun i j => hk.1 j i⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => by simpa [transposeInv_transposeInv] using transposeInv_mem_integralGL h, transposeInv_mem_integralGL⟩`.
-/
theorem transposeInv_mem_integralGL_iff {k : GL (Fin n) F} :
    transposeInv F n k ∈ integralGL F n ↔ k ∈ integralGL F n :=
  ⟨fun h => by simpa [transposeInv_transposeInv] using transposeInv_mem_integralGL h,
    transposeInv_mem_integralGL⟩

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[coe_inv_transposeInv, Cartan.coe_diagPow, diagonal_transpose]`.
-/
theorem inv_transposeInv_diagPow [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (l : Fin n → ℤ) : (transposeInv F n (Cartan.diagPow F n l))⁻¹ = Cartan.diagPow F n l := by
  ext i j
  rw [coe_inv_transposeInv, Cartan.coe_diagPow, diagonal_transpose]

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Continuous fun g : GL (Fin n) F => ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ`. Conclude with `(Units.continuous_val.comp continuous_inv).matrix_transpose`. Express the relevant statement in the definitionally equal form `Continuous fun g : GL (Fin n) F => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ`. Conclude with `Units.continuous_val.matrix_transpose`.
-/
theorem continuous_transposeInv : Continuous (transposeInv F n) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous fun g : GL (Fin n) F => ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ
    exact (Units.continuous_val.comp continuous_inv).matrix_transpose
  · change Continuous fun g : GL (Fin n) F => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ
    exact Units.continuous_val.matrix_transpose

def transposeInvHomeomorph : GL (Fin n) F ≃ₜ GL (Fin n) F where
  toEquiv := (transposeInv F n).toEquiv
  continuous_toFun := continuous_transposeInv
  continuous_invFun := continuous_transposeInv

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]

/- English proof (translation)
Establish `hH : (μ.map (transposeInv F n)).IsHaarMeasure` using `(transposeInv F n).isHaarMeasure_map μ continuous_transposeInv (transposeInvHomeomorph (F := F) (n := n)).continuous_invFun`. Use `set K := integralGL F n`. Establish `hK0 : μ K ≠ 0` using `(isOpen_integralGL F n).measure_ne_zero μ ⟨1, K.one_mem⟩`. Establish `hKT : μ K ≠ ⊤` using `(isCompact_integralGL F n).measure_lt_top.ne`. Establish `e` using `isMulLeftInvariant_eq_smul (μ.map (transposeInv F n)) μ`.

Establish `hpre : transposeInv F n ⁻¹' (K : Set (GL (Fin n) F)) = K`. Use extensionality with `x`. Conclude with `transposeInv_mem_integralGL_iff`. Establish `hK : μ.map (transposeInv F n) K = μ K`. Rewrite using `[map_apply continuous_transposeInv.measurable (isOpen_integralGL F n).measurableSet, hpre]`.

Establish `hc : haarScalarFactor (μ.map (transposeInv F n)) μ = 1`. Establish `h` using `congrArg (fun ν : Measure (GL (Fin n) F) => ν K) e`. Simplify using `only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h`. Rewrite `h` using `[hK]`. Use `(ENNReal.mul_eq_right hK0 hKT).1 h.symm` as an intermediate fact.

Conclude with `this` after adjusting the coercions. Rewrite using `[e, hc, one_smul]`.
-/
theorem map_transposeInv : μ.map (transposeInv F n) = μ := by
  have hH : (μ.map (transposeInv F n)).IsHaarMeasure :=
    (transposeInv F n).isHaarMeasure_map μ continuous_transposeInv
      (transposeInvHomeomorph (F := F) (n := n)).continuous_invFun
  set K := integralGL F n
  have hK0 : μ K ≠ 0 := (isOpen_integralGL F n).measure_ne_zero μ ⟨1, K.one_mem⟩
  have hKT : μ K ≠ ⊤ := (isCompact_integralGL F n).measure_lt_top.ne
  have e := isMulLeftInvariant_eq_smul (μ.map (transposeInv F n)) μ
  have hpre : transposeInv F n ⁻¹' (K : Set (GL (Fin n) F)) = K := by
    ext x
    exact transposeInv_mem_integralGL_iff
  have hK : μ.map (transposeInv F n) K = μ K := by
    rw [map_apply continuous_transposeInv.measurable (isOpen_integralGL F n).measurableSet, hpre]
  have hc : haarScalarFactor (μ.map (transposeInv F n)) μ = 1 := by
    have h := congrArg (fun ν : Measure (GL (Fin n) F) => ν K) e
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    rw [hK] at h
    have := (ENNReal.mul_eq_right hK0 hKT).1 h.symm
    exact_mod_cast this
  rw [e, hc, one_smul]

/- English proof (translation)
Use `integral_map_equiv (μ := μ) (transposeInvHomeomorph (F := F) (n := n)).toMeasurableEquiv f` as an intermediate fact. Express the relevant statement in the definitionally equal form `∫ g, f g ∂(μ.map (transposeInv F n)) = _ at this`. Rewrite `this` using `[map_transposeInv]`. Conclude with `this.symm`.
-/
theorem integral_comp_transposeInv (f : GL (Fin n) F → ℂ) :
    ∫ g, f (transposeInv F n g) ∂μ = ∫ g, f g ∂μ := by
  have := integral_map_equiv (μ := μ) (transposeInvHomeomorph (F := F) (n := n)).toMeasurableEquiv f
  change ∫ g, f g ∂(μ.map (transposeInv F n)) = _ at this
  rw [map_transposeInv] at this
  exact this.symm

/- English proof (translation)
Take `⟨l, -, k₁, hk₁, k₂, hk₂, rfl⟩` from `Cartan.exists_eq_mul_diagPow_mul F n g`. Establish `: (transposeInv F n (k₁ * Cartan.diagPow F n l * k₂))⁻¹ = (transposeInv F n k₂)⁻¹ * Cartan.diagPow F n l * (transposeInv F n k₁)⁻¹`. Rewrite using `[map_mul, map_mul, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_transposeInv_diagPow, mul_assoc]`. Establish `h₁` using `(integralGL F n).inv_mem (transposeInv_mem_integralGL hk₁)`. Establish `h₂` using `(integralGL F n).inv_mem (transposeInv_mem_integralGL hk₂)`.

Rewrite using `[this, (hf _ h₁ _).2, (hf _ h₂ _).1, (hf _ hk₂ _).2, (hf _ hk₁ _).1]`.
-/
theorem apply_inv_transposeInv {f : GL (Fin n) F → ℂ}
    (hf : ∀ k ∈ integralGL F n, ∀ x, f (k * x) = f x ∧ f (x * k) = f x) (g : GL (Fin n) F) :
    f (transposeInv F n g)⁻¹ = f g := by
  obtain ⟨l, -, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul F n g
  have : (transposeInv F n (k₁ * Cartan.diagPow F n l * k₂))⁻¹ =
      (transposeInv F n k₂)⁻¹ * Cartan.diagPow F n l * (transposeInv F n k₁)⁻¹ := by
    rw [map_mul, map_mul, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_transposeInv_diagPow, mul_assoc]
  have h₁ := (integralGL F n).inv_mem (transposeInv_mem_integralGL hk₁)
  have h₂ := (integralGL F n).inv_mem (transposeInv_mem_integralGL hk₂)
  rw [this, (hf _ h₁ _).2, (hf _ h₂ _).1, (hf _ hk₂ _).2, (hf _ hk₁ _).1]

variable {μ}

/- English proof (translation)
Establish `ha` using `HeckeAlgebraLevel.val_mem (isCompact_integralGL F n) (isOpen_integralGL F n) a`. Establish `hb` using `HeckeAlgebraLevel.val_mem (isCompact_integralGL F n) (isOpen_integralGL F n) b`. Establish `hab` using `HeckeAlgebraLevel.val_mem (isCompact_integralGL F n) (isOpen_integralGL F n) (a * b)`. Use `HeckeAlgebraLevel.ext (isCompact_integralGL F n) (isOpen_integralGL F n) (HeckeAlgebra.ext fun x => ?_)` and prove the remaining obligations. Rewrite using `[HeckeAlgebraLevel.val_mul, HeckeAlgebraLevel.val_mul]`.

Rewrite using `[HeckeAlgebra.mul_apply (b : HeckeAlgebra μ)]`. Use `set c := (transposeInv F n x)⁻¹`. Establish `step1 : ∫ y, (b : HeckeAlgebra μ) y * (a : HeckeAlgebra μ) (y⁻¹ * x) ∂μ = ∫ y, (b : HeckeAlgebra μ) (transposeInv F n y)⁻¹ * (a : HeckeAlgebra μ) (c * transposeInv F n y) ∂μ`. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Establish `e1` using `apply_inv_transposeInv hb y`.

Establish `e2` using `apply_inv_transposeInv ha (y⁻¹ * x)`. Establish `hyx : (transposeInv F n (y⁻¹ * x))⁻¹ = c * transposeInv F n y`. Rewrite using `[map_mul, map_inv (transposeInv F n), _root_.mul_inv_rev, inv_inv]`. Use `show _ * _ = _ * _`. Rewrite using `[← e1, ← e2, hyx]`.

Establish `step2 : ∫ y, (b : HeckeAlgebra μ) (transposeInv F n y)⁻¹ * (a : HeckeAlgebra μ) (c * transposeInv F n y) ∂μ = ∫ w, (b : HeckeAlgebra μ) w⁻¹ * (a : HeckeAlgebra μ) (c * w) ∂μ` using `integral_comp_transposeInv μ (fun w => (b : HeckeAlgebra μ) w⁻¹ * (a : HeckeAlgebra μ) (c * w))`. Establish `step3 : ∫ w, (b : HeckeAlgebra μ) w⁻¹ * (a : HeckeAlgebra μ) (c * w) ∂μ = ((a : HeckeAlgebra μ) * (b : HeckeAlgebra μ)) c`. Establish `key` using `integral_mul_left_eq_self (μ := μ) (fun y => (a : HeckeAlgebra μ) y * (b : HeckeAlgebra μ) (y⁻¹ * c)) c`. Rewrite using `[HeckeAlgebra.mul_apply, ← key]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)` and prove the remaining obligations.

Simplify using `only [_root_.mul_inv_rev, inv_mul_cancel_right]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[step1, step2, step3]`. Use `apply_inv_transposeInv hab x` as an intermediate fact. Rewrite `this` using `[HeckeAlgebraLevel.val_mul]`.

Conclude with `this.symm`.
-/
theorem heckeAlgebraLevel_mul_comm
    (a b : HeckeAlgebraLevel μ (integralGL F n) (isCompact_integralGL F n)
      (isOpen_integralGL F n)) : a * b = b * a := by
  have ha := HeckeAlgebraLevel.val_mem (isCompact_integralGL F n) (isOpen_integralGL F n) a
  have hb := HeckeAlgebraLevel.val_mem (isCompact_integralGL F n) (isOpen_integralGL F n) b
  have hab := HeckeAlgebraLevel.val_mem (isCompact_integralGL F n) (isOpen_integralGL F n) (a * b)
  refine HeckeAlgebraLevel.ext (isCompact_integralGL F n) (isOpen_integralGL F n)
    (HeckeAlgebra.ext fun x => ?_)
  rw [HeckeAlgebraLevel.val_mul, HeckeAlgebraLevel.val_mul]
  rw [HeckeAlgebra.mul_apply (b : HeckeAlgebra μ)]
  set c := (transposeInv F n x)⁻¹
  have step1 : ∫ y, (b : HeckeAlgebra μ) y * (a : HeckeAlgebra μ) (y⁻¹ * x) ∂μ =
      ∫ y, (b : HeckeAlgebra μ) (transposeInv F n y)⁻¹ *
        (a : HeckeAlgebra μ) (c * transposeInv F n y) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have e1 := apply_inv_transposeInv hb y
    have e2 := apply_inv_transposeInv ha (y⁻¹ * x)
    have hyx : (transposeInv F n (y⁻¹ * x))⁻¹ = c * transposeInv F n y := by
      rw [map_mul, map_inv (transposeInv F n), _root_.mul_inv_rev, inv_inv]
    show _ * _ = _ * _
    rw [← e1, ← e2, hyx]
  have step2 : ∫ y, (b : HeckeAlgebra μ) (transposeInv F n y)⁻¹ *
        (a : HeckeAlgebra μ) (c * transposeInv F n y) ∂μ =
      ∫ w, (b : HeckeAlgebra μ) w⁻¹ * (a : HeckeAlgebra μ) (c * w) ∂μ :=
    integral_comp_transposeInv μ (fun w => (b : HeckeAlgebra μ) w⁻¹ * (a : HeckeAlgebra μ) (c * w))
  have step3 : ∫ w, (b : HeckeAlgebra μ) w⁻¹ * (a : HeckeAlgebra μ) (c * w) ∂μ =
      ((a : HeckeAlgebra μ) * (b : HeckeAlgebra μ)) c := by
    have key := integral_mul_left_eq_self (μ := μ)
      (fun y => (a : HeckeAlgebra μ) y * (b : HeckeAlgebra μ) (y⁻¹ * c)) c
    rw [HeckeAlgebra.mul_apply, ← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [_root_.mul_inv_rev, inv_mul_cancel_right]
    ring
  rw [step1, step2, step3]
  have := apply_inv_transposeInv hab x
  rw [HeckeAlgebraLevel.val_mul] at this
  exact this.symm

instance instCommRing :
    CommRing (HeckeAlgebraLevel μ (integralGL F n) (isCompact_integralGL F n)
      (isOpen_integralGL F n)) :=
  { (inferInstance : Ring (HeckeAlgebraLevel μ (integralGL F n) (isCompact_integralGL F n)
      (isOpen_integralGL F n))) with
    mul_comm := heckeAlgebraLevel_mul_comm }

end Spherical

namespace HeckeAlgebra.HeckeAlgebraLevel

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))

instance : IsScalarTower ℂ (HeckeAlgebraLevel μ K hKc hKo) (HeckeAlgebraLevel μ K hKc hKo) where
  smul_assoc c a b := ext hKc hKo (by
    change ((c • a : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ) * (b : HeckeAlgebra μ) =
      c • ((a : HeckeAlgebra μ) * (b : HeckeAlgebra μ))
    rw [val_smul, smul_mul_assoc])

instance : SMulCommClass ℂ (HeckeAlgebraLevel μ K hKc hKo) (HeckeAlgebraLevel μ K hKc hKo) where
  smul_comm c a b := ext hKc hKo (by
    change c • ((a : HeckeAlgebra μ) * (b : HeckeAlgebra μ)) =
      (a : HeckeAlgebra μ) * ((c • b : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ)
    rw [val_smul, mul_smul_comm])

instance instAlgebra : Algebra ℂ (HeckeAlgebraLevel μ K hKc hKo) := Algebra.ofModule
  (fun c a b => smul_mul_assoc c a b) (fun c a b => (mul_smul_comm c a b))

end HeckeAlgebra.HeckeAlgebraLevel

end GroundTheory.Automorphic
