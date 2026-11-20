import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply

set_option autoImplicit false

open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff

namespace GlobalTheory.TorsionForm

/- English proof (translation)
Establish `h : γ.mat * (γ⁻¹).mat = 1` using `congrArg Subtype.val (mul_inv_cancel γ)`. Rewrite using `[Matrix.vecMul_vecMul, h, Matrix.vecMul_one]`.
-/
theorem sp_vecMul_vecMul_inv {g : ℕ} (γ : Sp g) (x : Fl g) :
    (x ᵥ* γ.mat) ᵥ* (γ⁻¹).mat = x := by
  have h : γ.mat * (γ⁻¹).mat = 1 := congrArg Subtype.val (mul_inv_cancel γ)
  rw [Matrix.vecMul_vecMul, h, Matrix.vecMul_one]

/- English proof (translation)
Establish `h : (γ⁻¹).mat * γ.mat = 1` using `congrArg Subtype.val (inv_mul_cancel γ)`. Rewrite using `[Matrix.vecMul_vecMul, h, Matrix.vecMul_one]`.
-/
theorem sp_vecMul_inv_vecMul {g : ℕ} (γ : Sp g) (x : Fl g) :
    (x ᵥ* (γ⁻¹).mat) ᵥ* γ.mat = x := by
  have h : (γ⁻¹).mat * γ.mat = 1 := congrArg Subtype.val (inv_mul_cancel γ)
  rw [Matrix.vecMul_vecMul, h, Matrix.vecMul_one]

/- English proof (translation)
Establish `h : γ.mat * (γ⁻¹).mat = 1` using `congrArg Subtype.val (mul_inv_cancel γ)`. Establish `hd : (γ.mat).det ≠ 0`. Introduce `h0`. Use `congrArg Matrix.det h` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_one]`.

Conclude with `zero_ne_one this`. Establish `hdet : LinearMap.det (Matrix.toLin' (γ.mat)ᵀ) ≠ 0`. Rewrite using `[LinearMap.det_toLin', Matrix.det_transpose]`. Conclude with `hd`. Use `Measure.LinearMap.quasiMeasurePreserving (volume : Measure (Fl g)) _ hdet` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Rewrite using `[Matrix.toLin'_apply, Matrix.mulVec_transpose]`.
-/
theorem sp_vecMul_quasiMeasurePreserving {g : ℕ} (γ : Sp g) :
    Measure.QuasiMeasurePreserving (fun x : Fl g => x ᵥ* γ.mat) volume volume := by
  have h : γ.mat * (γ⁻¹).mat = 1 := congrArg Subtype.val (mul_inv_cancel γ)
  have hd : (γ.mat).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdet : LinearMap.det (Matrix.toLin' (γ.mat)ᵀ) ≠ 0 := by
    rw [LinearMap.det_toLin', Matrix.det_transpose]; exact hd
  have := Measure.LinearMap.quasiMeasurePreserving (volume : Measure (Fl g)) _ hdet
  convert this using 1
  funext x
  rw [Matrix.toLin'_apply, Matrix.mulVec_transpose]

/- English proof (translation)
Establish `hmem : ∀ y : Fl g, y ∈ latAct M γ ↔ y ᵥ* γ.mat ∈ M`. Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Express the relevant statement in the definitionally equal form `(x ᵥ* (γ⁻¹).mat) ᵥ* γ.mat ∈ M`.

Rewrite using `[sp_vecMul_inv_vecMul]`. Conclude with `hx`. Introduce `hy`. Conclude with `⟨y ᵥ* γ.mat, hy, sp_vecMul_vecMul_inv γ y⟩`. Use `hD.preimage_of_equiv (sp_vecMul_quasiMeasurePreserving γ⁻¹) (e := fun l => (⟨(l : Fl g) ᵥ* γ.mat, (hmem l).1 l.2⟩ : M)) ⟨?_, ?_⟩ ?_` and prove the remaining obligations.

Introduce `a b hab`. Establish `h` using `congrArg (fun l : M => (l : Fl g) ᵥ* (γ⁻¹).mat) hab`. Simplify using `only [sp_vecMul_vecMul_inv] at h`. Conclude with `Subtype.ext h`. Introduce `l`.

Use `⟨⟨(l : Fl g) ᵥ* (γ⁻¹).mat, (hmem _).2 ?_⟩, Subtype.ext (sp_vecMul_inv_vecMul γ l)⟩` and prove the remaining obligations. Rewrite using `[sp_vecMul_inv_vecMul]`. Conclude with `l.2`. Introduce `l x`. Express the relevant statement in the definitionally equal form `((l : Fl g) ᵥ* γ.mat + x) ᵥ* (γ⁻¹).mat = (l : Fl g) + x ᵥ* (γ⁻¹).mat`.

Rewrite using `[Matrix.add_vecMul, sp_vecMul_vecMul_inv]`.
-/
theorem isAddFundamentalDomain_preimage_latAct {g : ℕ} (M : Submodule ℤ (Fl g)) (γ : Sp g)
    (D : Set (Fl g)) (hD : IsAddFundamentalDomain (latAct M γ) D volume) :
    IsAddFundamentalDomain M ((fun x : Fl g => x ᵥ* (γ⁻¹).mat) ⁻¹' D) volume := by
  have hmem : ∀ y : Fl g, y ∈ latAct M γ ↔ y ᵥ* γ.mat ∈ M := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (x ᵥ* (γ⁻¹).mat) ᵥ* γ.mat ∈ M
      rw [sp_vecMul_inv_vecMul]; exact hx
    · intro hy
      exact ⟨y ᵥ* γ.mat, hy, sp_vecMul_vecMul_inv γ y⟩
  refine hD.preimage_of_equiv (sp_vecMul_quasiMeasurePreserving γ⁻¹)
    (e := fun l => (⟨(l : Fl g) ᵥ* γ.mat, (hmem l).1 l.2⟩ : M)) ⟨?_, ?_⟩ ?_
  · intro a b hab
    have h := congrArg (fun l : M => (l : Fl g) ᵥ* (γ⁻¹).mat) hab
    simp only [sp_vecMul_vecMul_inv] at h
    exact Subtype.ext h
  · intro l
    refine ⟨⟨(l : Fl g) ᵥ* (γ⁻¹).mat, (hmem _).2 ?_⟩, Subtype.ext (sp_vecMul_inv_vecMul γ l)⟩
    rw [sp_vecMul_inv_vecMul]; exact l.2
  · intro l x
    change ((l : Fl g) ᵥ* γ.mat + x) ᵥ* (γ⁻¹).mat = (l : Fl g) + x ᵥ* (γ⁻¹).mat
    rw [Matrix.add_vecMul, sp_vecMul_vecMul_inv]

end GlobalTheory.TorsionForm
