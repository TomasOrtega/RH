import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.S3x1

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3

section Blocks

variable {A : Type} {r k : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i | i <;> rcases j with j | j | j`. Conclude with `congrFun (congrFun h11 i) j`. Conclude with `congrFun (congrFun h12 i) j`. Conclude with `congrFun (congrFun h13 i) j`.

Conclude with `congrFun (congrFun h21 i) j`. Conclude with `congrFun (congrFun h22 i) j`. Conclude with `congrFun (congrFun h23 i) j`. Conclude with `congrFun (congrFun h31 i) j`. Conclude with `congrFun (congrFun h32 i) j`.

Conclude with `congrFun (congrFun h33 i) j`.
-/
theorem ext9 {x y : Matrix (Idx r k) (Idx r k) A} (h11 : b11 x = b11 y) (h12 : b12 x = b12 y)
    (h13 : b13 x = b13 y) (h21 : b21 x = b21 y) (h22 : b22 x = b22 y) (h23 : b23 x = b23 y)
    (h31 : b31 x = b31 y) (h32 : b32 x = b32 y) (h33 : b33 x = b33 y) : x = y := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j
  · exact congrFun (congrFun h11 i) j
  · exact congrFun (congrFun h12 i) j
  · exact congrFun (congrFun h13 i) j
  · exact congrFun (congrFun h21 i) j
  · exact congrFun (congrFun h22 i) j
  · exact congrFun (congrFun h23 i) j
  · exact congrFun (congrFun h31 i) j
  · exact congrFun (congrFun h32 i) j
  · exact congrFun (congrFun h33 i) j

variable [CommRing A]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b11, b11, b12, b13, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]`.
-/
theorem block11_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b11 (x * y) = b11 x * b11 y + b12 x * b21 y + b13 x * b31 y := by
  ext a b
  simp [b11, b11, b12, b13, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b11, Matrix.one_apply]`.
-/
theorem one_block11 : b11 (1 : Matrix (Idx r k) (Idx r k) A) = 1 := by
  ext a b
  simp [b11, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b12, b11, b12, b13, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]`.
-/
theorem block12_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b12 (x * y) = b11 x * b12 y + b12 x * b22 y + b13 x * b32 y := by
  ext a b
  simp [b12, b11, b12, b13, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b12, Matrix.one_apply]`.
-/
theorem block12_one : b12 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b12, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b13, b11, b12, b13, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]`.
-/
theorem block13_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b13 (x * y) = b11 x * b13 y + b12 x * b23 y + b13 x * b33 y := by
  ext a b
  simp [b13, b11, b12, b13, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b13, Matrix.one_apply]`.
-/
theorem block13_one : b13 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b13, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b21, b21, b22, b23, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]`.
-/
theorem block21_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b21 (x * y) = b21 x * b11 y + b22 x * b21 y + b23 x * b31 y := by
  ext a b
  simp [b21, b21, b22, b23, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b21, Matrix.one_apply]`.
-/
theorem one_block21 : b21 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b21, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b22, b21, b22, b23, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]`.
-/
theorem block22_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b22 (x * y) = b21 x * b12 y + b22 x * b22 y + b23 x * b32 y := by
  ext a b
  simp [b22, b21, b22, b23, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b22, Matrix.one_apply]`.
-/
theorem block22_one : b22 (1 : Matrix (Idx r k) (Idx r k) A) = 1 := by
  ext a b
  simp [b22, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b23, b21, b22, b23, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]`.
-/
theorem block23_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b23 (x * y) = b21 x * b13 y + b22 x * b23 y + b23 x * b33 y := by
  ext a b
  simp [b23, b21, b22, b23, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b23, Matrix.one_apply]`.
-/
theorem block23_one : b23 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b23, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b31, b31, b32, b33, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]`.
-/
theorem block31_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b31 (x * y) = b31 x * b11 y + b32 x * b21 y + b33 x * b31 y := by
  ext a b
  simp [b31, b31, b32, b33, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b31, Matrix.one_apply]`.
-/
theorem one_block31 : b31 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b31, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b32, b31, b32, b33, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]`.
-/
theorem block32_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b32 (x * y) = b31 x * b12 y + b32 x * b22 y + b33 x * b32 y := by
  ext a b
  simp [b32, b31, b32, b33, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b32, Matrix.one_apply]`.
-/
theorem block32_one : b32 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b32, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b33, b31, b32, b33, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]`.
-/
theorem block33_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b33 (x * y) = b31 x * b13 y + b32 x * b23 y + b33 x * b33 y := by
  ext a b
  simp [b33, b31, b32, b33, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b33, Matrix.one_apply]`.
-/
theorem block33_one : b33 (1 : Matrix (Idx r k) (Idx r k) A) = 1 := by
  ext a b
  simp [b33, Matrix.one_apply]

/- English proof (translation)
Simplify using `[midEmb, Matrix.fromBlocks_multiply]`.
-/
theorem midEmb_mul (h h' : Matrix (Fin k) (Fin k) A) : midEmb h * midEmb h' = midEmb (h * h') := by
  simp [midEmb, Matrix.fromBlocks_multiply]

/- English proof (translation)
Simplify using `[midEmb]`.
-/
theorem midEmb_one : midEmb (1 : Matrix (Fin k) (Fin k) A) = 1 := by
  simp [midEmb]

/- English proof (translation)
The claim follows from `(Matrix.fromBlocks_inj.1 e).1`.
-/
theorem midEmb_inj {h h' : Matrix (Fin k) (Fin k) A} (e : midEmb h = midEmb h') : h = h' :=
  (Matrix.fromBlocks_inj.1 e).1

/- English proof (translation)
Simplify using `[midEmb]`.
-/
theorem midEmb_det (h : Matrix (Fin k) (Fin k) A) : (midEmb h).det = h.det := by
  simp [midEmb]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b11, hEmb]`.
-/
theorem levi_embedding_block11 (h : Matrix (Fin k) (Fin k) A) : b11 (hEmb r h) = 1 := by
  ext a b; simp [b11, hEmb]
/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b12, hEmb]`.
-/
theorem levi_embedding_block12 (h : Matrix (Fin k) (Fin k) A) : b12 (hEmb r h) = 0 := by
  ext a b; simp [b12, hEmb]
/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b13, hEmb]`.
-/
theorem levi_embedding_block13 (h : Matrix (Fin k) (Fin k) A) : b13 (hEmb r h) = 0 := by
  ext a b; simp [b13, hEmb]
/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b21, hEmb]`.
-/
theorem levi_embedding_block21 (h : Matrix (Fin k) (Fin k) A) : b21 (hEmb r h) = 0 := by
  ext a b; simp [b21, hEmb]
/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b22, hEmb]`.
-/
theorem levi_embedding_block22 (h : Matrix (Fin k) (Fin k) A) : b22 (hEmb r h) = midEmb h := by
  ext a b; simp [b22, hEmb]
/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b23, hEmb]`.
-/
theorem levi_embedding_block23 (h : Matrix (Fin k) (Fin k) A) : b23 (hEmb r h) = 0 := by
  ext a b; simp [b23, hEmb]
/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b31, hEmb]`.
-/
theorem levi_embedding_block31 (h : Matrix (Fin k) (Fin k) A) : b31 (hEmb r h) = 0 := by
  ext a b; simp [b31, hEmb]
/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b32, hEmb]`.
-/
theorem levi_embedding_block32 (h : Matrix (Fin k) (Fin k) A) : b32 (hEmb r h) = 0 := by
  ext a b; simp [b32, hEmb]
/- English proof (translation)
Use extensionality with `a b`. Simplify using `[b33, hEmb]`.
-/
theorem levi_embedding_block33 (h : Matrix (Fin k) (Fin k) A) : b33 (hEmb r h) = 1 := by
  ext a b; simp [b33, hEmb]

/- English proof (translation)
Simplify using `[hEmb, Matrix.fromBlocks_multiply, midEmb_mul]`.
-/
theorem hEmb_mul (h h' : Matrix (Fin k) (Fin k) A) : hEmb r h * hEmb r h' = hEmb r (h * h') := by
  simp [hEmb, Matrix.fromBlocks_multiply, midEmb_mul]

/- English proof (translation)
Simplify using `[hEmb, midEmb_one]`.
-/
theorem hEmb_one : hEmb r (1 : Matrix (Fin k) (Fin k) A) = 1 := by
  simp [hEmb, midEmb_one]

/- English proof (translation)
Use `congrArg b22 e` as an intermediate fact. Rewrite `this` using `[levi_embedding_block22, levi_embedding_block22]`. Conclude with `midEmb_inj this`.
-/
theorem hEmb_inj {h h' : Matrix (Fin k) (Fin k) A} (e : hEmb r h = hEmb r h') : h = h' := by
  have := congrArg b22 e
  rw [levi_embedding_block22, levi_embedding_block22] at this
  exact midEmb_inj this

/- English proof (translation)
Rewrite using `[← Matrix.nonsing_inv_mul_cancel_left f Y hf, h, Matrix.nonsing_inv_mul_cancel_left f Z hf]`.
-/
theorem lcancel {n m : Type} [Fintype n] [DecidableEq n] {f : Matrix n n A} (hf : IsUnit f.det)
    {Y Z : Matrix n m A} (h : f * Y = f * Z) : Y = Z := by
  rw [← Matrix.nonsing_inv_mul_cancel_left f Y hf, h, Matrix.nonsing_inv_mul_cancel_left f Z hf]

structure GP (P : Matrix (Fin k) (Fin k) A → Prop) : Prop where
  one : P 1
  mul : ∀ {h h'}, P h → P h' → P (h * h')
  inv : ∀ {h}, P h → P h⁻¹
  unit : ∀ {h}, P h → IsUnit h.det

/- English proof (translation)
The claim follows from `rfl mul := by rintro _ _ rfl rfl; simp inv := by rintro _ rfl; simp unit := by rintro _ rfl; simp`.
-/
theorem gpOne : GP (fun h : Matrix (Fin k) (Fin k) A => h = 1) where
  one := rfl
  mul := by rintro _ _ rfl rfl; simp
  inv := by rintro _ rfl; simp
  unit := by rintro _ rfl; simp

/- English proof (translation)
Simplify using `mul := by intro h h' a b; rw [Matrix.det_mul]; exact a.mul b inv := by intro h a; exact Matrix.isUnit_nonsing_inv_det h a unit := fun a => a`.
-/
theorem gpUnit : GP (fun h : Matrix (Fin k) (Fin k) A => IsUnit h.det) where
  one := by simp
  mul := by intro h h' a b; rw [Matrix.det_mul]; exact a.mul b
  inv := by intro h a; exact Matrix.isUnit_nonsing_inv_det h a
  unit := fun a => a

/- English proof (translation)
The claim follows from `isUpUni_one A mul := fun a b => isUpUni_mul A a b inv := fun a => isUpUni_inv A a unit := by intro h a; rw [isUpUni_det A a]; exact isUnit_one`.
-/
theorem gpUni : GP (IsUpUni : Matrix (Fin k) (Fin k) A → Prop) where
  one := isUpUni_one A
  mul := fun a b => isUpUni_mul A a b
  inv := fun a => isUpUni_inv A a
  unit := by intro h a; rw [isUpUni_det A a]; exact isUnit_one

def Par (P : Matrix (Fin k) (Fin k) A → Prop) (x : Matrix (Idx r k) (Idx r k) A) : Prop :=
  IsUpUni (b11 x) ∧ IsUpUni (b33 x) ∧ b21 x = 0 ∧ b31 x = 0 ∧ b32 x = 0 ∧ ∃ h, P h ∧ b22 x = midEmb h

def Emb (P : Matrix (Fin k) (Fin k) A → Prop) (x : Matrix (Idx r k) (Idx r k) A) : Prop :=
  ∃ h, P h ∧ x = hEmb r h

variable {P : Matrix (Fin k) (Fin k) A → Prop}

/- English proof (translation)
Rewrite using `[isUpUni_det A hu]`. Conclude with `isUnit_one`.
-/
theorem uni_unit {n : ℕ} {u : Matrix (Fin n) (Fin n) A} (hu : IsUpUni u) : IsUnit u.det := by
  rw [isUpUni_det A hu]; exact isUnit_one

/- English proof (translation)
Take `⟨h11, h33, h21, h31, h32, h, hh, h22⟩` from `hx`. Establish `e : x = Matrix.fromBlocks (b11 x) x.toBlocks₁₂ 0 (Matrix.fromBlocks (b22 x) (b23 x) 0 (b33 x))`. Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i | i <;> rcases j with j | j | j`. Both sides reduce to the same expression.

Both sides reduce to the same expression. Both sides reduce to the same expression. Conclude with `congrFun (congrFun h21 i) j`. Both sides reduce to the same expression. Both sides reduce to the same expression.

Conclude with `congrFun (congrFun h31 i) j`. Conclude with `congrFun (congrFun h32 i) j`. Both sides reduce to the same expression. Rewrite using `[e, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, h22, midEmb_det, isUpUni_det A h11, isUpUni_det A h33]`. Simplify using `using hP.unit hh`.
-/
theorem par_det (hP : GP P) {x : Matrix (Idx r k) (Idx r k) A} (hx : Par P x) : IsUnit x.det := by
  obtain ⟨h11, h33, h21, h31, h32, h, hh, h22⟩ := hx
  have e : x = Matrix.fromBlocks (b11 x) x.toBlocks₁₂ 0 (Matrix.fromBlocks (b22 x) (b23 x) 0 (b33 x)) := by
    ext i j
    rcases i with i | i | i <;> rcases j with j | j | j
    · rfl
    · rfl
    · rfl
    · exact congrFun (congrFun h21 i) j
    · rfl
    · rfl
    · exact congrFun (congrFun h31 i) j
    · exact congrFun (congrFun h32 i) j
    · rfl
  rw [e, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, h22, midEmb_det,
    isUpUni_det A h11, isUpUni_det A h33]
  simpa using hP.unit hh

/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [one_block11]; exact isUpUni_one A, by rw [block33_one]; exact isUpUni_one A, one_block21, one_block31, block32_one, 1, hP.one, by rw [block22_one, midEmb_one]⟩`.
-/
theorem par_one (hP : GP P) : Par P (1 : Matrix (Idx r k) (Idx r k) A) :=
  ⟨by rw [one_block11]; exact isUpUni_one A, by rw [block33_one]; exact isUpUni_one A, one_block21, one_block31,
    block32_one, 1, hP.one, by rw [block22_one, midEmb_one]⟩

/- English proof (translation)
Take `⟨h11, h33, h21, h31, h32, h, hh, h22⟩` from `hx`. Take `⟨g11, g33, g21, g31, g32, g, hg, g22⟩` from `hy`. Use `⟨?_, ?_, ?_, ?_, ?_, h * g, hP.mul hh hg, ?_⟩` and prove the remaining obligations. Rewrite using `[block11_mul, g21, g31]`. Simplify using `using isUpUni_mul A h11 g11`.

Rewrite using `[block33_mul, h31, h32]`. Simplify using `using isUpUni_mul A h33 g33`. Rewrite using `[block21_mul, h21, g21, g31]`. Simplify using the standard rewrite rules. Rewrite using `[block31_mul, h31, h32, g31]`.

Simplify using the standard rewrite rules. Rewrite using `[block32_mul, h31, h32, g32]`. Simplify using the standard rewrite rules. Rewrite using `[block22_mul, h21, g32, h22, g22, midEmb_mul]`. Simplify using the standard rewrite rules.
-/
theorem par_mul (hP : GP P) {x y : Matrix (Idx r k) (Idx r k) A} (hx : Par P x) (hy : Par P y) :
    Par P (x * y) := by
  obtain ⟨h11, h33, h21, h31, h32, h, hh, h22⟩ := hx
  obtain ⟨g11, g33, g21, g31, g32, g, hg, g22⟩ := hy
  refine ⟨?_, ?_, ?_, ?_, ?_, h * g, hP.mul hh hg, ?_⟩
  · rw [block11_mul, g21, g31]; simpa using isUpUni_mul A h11 g11
  · rw [block33_mul, h31, h32]; simpa using isUpUni_mul A h33 g33
  · rw [block21_mul, h21, g21, g31]; simp
  · rw [block31_mul, h31, h32, g31]; simp
  · rw [block32_mul, h31, h32, g32]; simp
  · rw [block22_mul, h21, g32, h22, g22, midEmb_mul]; simp

/- English proof (translation)
Take `⟨h11, h33, h21, h31, h32, h, hh, h22⟩` from `hx`. Establish `um : IsUnit (midEmb h).det` using `by rw [midEmb_det]; exact hP.unit hh`. Establish `y31 : b31 y = 0`. Use `block31_mul x y` as an intermediate fact. Rewrite `this` using `[e, one_block31, h31, h32]`.

Conclude with `lcancel (uni_unit h33) (by simpa using this.symm)`. Establish `y32 : b32 y = 0`. Use `block32_mul x y` as an intermediate fact. Rewrite `this` using `[e, block32_one, h31, h32]`. Conclude with `lcancel (uni_unit h33) (by simpa using this.symm)`.

Establish `y33 : b33 y = (b33 x)⁻¹`. Use `block33_mul x y` as an intermediate fact. Rewrite `this` using `[e, block33_one, h31, h32]`. Conclude with `(Matrix.inv_eq_right_inv (by simpa using this.symm)).symm`. Establish `y21 : b21 y = 0`.

Use `block21_mul x y` as an intermediate fact. Rewrite `this` using `[e, one_block21, h21, y31, h22]`. Conclude with `lcancel um (by simpa using this.symm)`. Establish `y22 : b22 y = midEmb h⁻¹`. Use `block22_mul x y` as an intermediate fact.

Rewrite `this` using `[e, block22_one, h21, y32, h22]`. Use `lcancel um ?_` and prove the remaining obligations. Rewrite using `[midEmb_mul, Matrix.mul_nonsing_inv h (hP.unit hh), midEmb_one]`. Simplify using `using this.symm`. Establish `y11 : b11 y = (b11 x)⁻¹`.

Use `block11_mul x y` as an intermediate fact. Rewrite `this` using `[e, one_block11, y21, y31]`. Conclude with `(Matrix.inv_eq_right_inv (by simpa using this.symm)).symm`. Conclude with `⟨y11 ▸ isUpUni_inv A h11, y33 ▸ isUpUni_inv A h33, y21, y31, y32, h⁻¹, hP.inv hh, y22⟩`.
-/
theorem par_rinv (hP : GP P) {x y : Matrix (Idx r k) (Idx r k) A} (hx : Par P x) (e : x * y = 1) :
    Par P y := by
  obtain ⟨h11, h33, h21, h31, h32, h, hh, h22⟩ := hx
  have um : IsUnit (midEmb h).det := by rw [midEmb_det]; exact hP.unit hh
  have y31 : b31 y = 0 := by
    have := block31_mul x y
    rw [e, one_block31, h31, h32] at this
    exact lcancel (uni_unit h33) (by simpa using this.symm)
  have y32 : b32 y = 0 := by
    have := block32_mul x y
    rw [e, block32_one, h31, h32] at this
    exact lcancel (uni_unit h33) (by simpa using this.symm)
  have y33 : b33 y = (b33 x)⁻¹ := by
    have := block33_mul x y
    rw [e, block33_one, h31, h32] at this
    exact (Matrix.inv_eq_right_inv (by simpa using this.symm)).symm
  have y21 : b21 y = 0 := by
    have := block21_mul x y
    rw [e, one_block21, h21, y31, h22] at this
    exact lcancel um (by simpa using this.symm)
  have y22 : b22 y = midEmb h⁻¹ := by
    have := block22_mul x y
    rw [e, block22_one, h21, y32, h22] at this
    refine lcancel um ?_
    rw [midEmb_mul, Matrix.mul_nonsing_inv h (hP.unit hh), midEmb_one]
    simpa using this.symm
  have y11 : b11 y = (b11 x)⁻¹ := by
    have := block11_mul x y
    rw [e, one_block11, y21, y31] at this
    exact (Matrix.inv_eq_right_inv (by simpa using this.symm)).symm
  exact ⟨y11 ▸ isUpUni_inv A h11, y33 ▸ isUpUni_inv A h33, y21, y31, y32, h⁻¹, hP.inv hh, y22⟩

def parG (hP : GP P) : Subgroup (GL (Idx r k) A) where
  carrier := {g | Par P (g : Matrix (Idx r k) (Idx r k) A)}
  one_mem' := by simpa using par_one hP
  mul_mem' := by intro a b ha hb; simpa using par_mul hP ha hb
  inv_mem' := by
    intro a ha
    refine par_rinv hP ha ?_
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

/- English proof (translation)
Use `⟨parG hP, fun x => ⟨fun hx => ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `⟨Matrix.GeneralLinearGroup.mk'' x (par_det hP hx), hx, rfl⟩`. Introduce and unpack `⟨g, hg, rfl⟩`. Conclude with `hg`.
-/
theorem par_subgroupSet (hP : GP P) : IsSubgroupSet (Par (r := r) P) := by
  refine ⟨parG hP, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · exact ⟨Matrix.GeneralLinearGroup.mk'' x (par_det hP hx), hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact hg

/- English proof (translation)
Take `⟨h, hh, rfl⟩` from `hx`. Conclude with `⟨by rw [levi_embedding_block11]; exact isUpUni_one A, by rw [levi_embedding_block33]; exact isUpUni_one A, levi_embedding_block21 h, levi_embedding_block31 h, levi_embedding_block32 h, h, hh, levi_embedding_block22 h⟩`.
-/
theorem emb_par (hP : GP P) {x : Matrix (Idx r k) (Idx r k) A} (hx : Emb P x) : Par P x := by
  obtain ⟨h, hh, rfl⟩ := hx
  exact ⟨by rw [levi_embedding_block11]; exact isUpUni_one A, by rw [levi_embedding_block33]; exact isUpUni_one A, levi_embedding_block21 h,
    levi_embedding_block31 h, levi_embedding_block32 h, h, hh, levi_embedding_block22 h⟩

def embG (hP : GP P) : Subgroup (GL (Idx r k) A) where
  carrier := {g | Emb P (g : Matrix (Idx r k) (Idx r k) A)}
  one_mem' := ⟨1, hP.one, by simp [hEmb_one]⟩
  mul_mem' := by
    rintro a b ⟨h, hh, ea⟩ ⟨g, hg, eb⟩
    exact ⟨h * g, hP.mul hh hg, by rw [Units.val_mul, ea, eb, hEmb_mul]⟩
  inv_mem' := by
    rintro a ⟨h, hh, ea⟩
    refine ⟨h⁻¹, hP.inv hh, ?_⟩
    rw [Matrix.coe_units_inv, ea]
    refine Matrix.inv_eq_right_inv ?_
    rw [hEmb_mul, Matrix.mul_nonsing_inv h (hP.unit hh), hEmb_one]

/- English proof (translation)
Use `⟨embG hP, fun x => ⟨fun hx => ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `⟨Matrix.GeneralLinearGroup.mk'' x (par_det hP (emb_par hP hx)), hx, rfl⟩`. Introduce and unpack `⟨g, hg, rfl⟩`. Conclude with `hg`.
-/
theorem emb_subgroupSet (hP : GP P) : IsSubgroupSet (Emb (r := r) P) := by
  refine ⟨embG hP, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · exact ⟨Matrix.GeneralLinearGroup.mk'' x (par_det hP (emb_par hP hx)), hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact hg

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h11, h33, h22, h21, h31, h32⟩`. Conclude with `⟨h11, h33, h21, h31, h32, 1, rfl, by rw [h22, midEmb_one]⟩`. Introduce and unpack `⟨h11, h33, h21, h31, h32, h, rfl, h22⟩`. Conclude with `⟨h11, h33, by rw [h22, midEmb_one], h21, h31, h32⟩`.
-/
theorem isN_iff (x : Matrix (Idx r k) (Idx r k) A) : IsN x ↔ Par (fun h => h = 1) x := by
  constructor
  · rintro ⟨h11, h33, h22, h21, h31, h32⟩
    exact ⟨h11, h33, h21, h31, h32, 1, rfl, by rw [h22, midEmb_one]⟩
  · rintro ⟨h11, h33, h21, h31, h32, h, rfl, h22⟩
    exact ⟨h11, h33, by rw [h22, midEmb_one], h21, h31, h32⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, _, ⟨h11, h33, h22, h21, h31, h32⟩, ⟨h, hh, rfl⟩, rfl⟩`. Use `⟨?_, ?_, ?_, ?_, ?_, h, hh, ?_⟩` and prove the remaining obligations. Rewrite using `[block11_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31]`. Simplify using `using h11`.

Rewrite using `[block33_mul, levi_embedding_block13, levi_embedding_block23, levi_embedding_block33]`. Simplify using `using h33`. Rewrite using `[block21_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31, h21]`. Simplify using the standard rewrite rules. Rewrite using `[block31_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31, h31]`.

Simplify using the standard rewrite rules. Rewrite using `[block32_mul, levi_embedding_block12, levi_embedding_block22, levi_embedding_block32, h32]`. Simplify using the standard rewrite rules. Rewrite using `[block22_mul, levi_embedding_block12, levi_embedding_block22, levi_embedding_block32, h22]`. Simplify using the standard rewrite rules.

Introduce and unpack `⟨h11, h33, h21, h31, h32, h, hh, h22⟩`. Use `⟨x * hEmb r h⁻¹, hEmb r h, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨h, hh, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[block11_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31]`. Simplify using `using h11`. Rewrite using `[block33_mul, levi_embedding_block13, levi_embedding_block23, levi_embedding_block33]`.

Simplify using `using h33`. Rewrite using `[block22_mul, levi_embedding_block12, levi_embedding_block22, levi_embedding_block32, h22, midEmb_mul, Matrix.mul_nonsing_inv h (hP.unit hh), midEmb_one]`. Simplify using the standard rewrite rules. Rewrite using `[block21_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31, h21]`. Simplify using the standard rewrite rules.

Rewrite using `[block31_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31, h31]`. Simplify using the standard rewrite rules. Rewrite using `[block32_mul, levi_embedding_block12, levi_embedding_block22, levi_embedding_block32, h32]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.mul_assoc, hEmb_mul, Matrix.nonsing_inv_mul h (hP.unit hh), hEmb_one, Matrix.mul_one]`.
-/
theorem prod_iff (hP : GP P) (x : Matrix (Idx r k) (Idx r k) A) :
    (∃ n u, IsN n ∧ Emb P u ∧ x = n * u) ↔ Par P x := by
  constructor
  · rintro ⟨n, _, ⟨h11, h33, h22, h21, h31, h32⟩, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, h, hh, ?_⟩
    · rw [block11_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31]; simpa using h11
    · rw [block33_mul, levi_embedding_block13, levi_embedding_block23, levi_embedding_block33]; simpa using h33
    · rw [block21_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31, h21]; simp
    · rw [block31_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31, h31]; simp
    · rw [block32_mul, levi_embedding_block12, levi_embedding_block22, levi_embedding_block32, h32]; simp
    · rw [block22_mul, levi_embedding_block12, levi_embedding_block22, levi_embedding_block32, h22]; simp
  · rintro ⟨h11, h33, h21, h31, h32, h, hh, h22⟩
    refine ⟨x * hEmb r h⁻¹, hEmb r h, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨h, hh, rfl⟩, ?_⟩
    · rw [block11_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31]; simpa using h11
    · rw [block33_mul, levi_embedding_block13, levi_embedding_block23, levi_embedding_block33]; simpa using h33
    · rw [block22_mul, levi_embedding_block12, levi_embedding_block22, levi_embedding_block32, h22, midEmb_mul,
        Matrix.mul_nonsing_inv h (hP.unit hh), midEmb_one]; simp
    · rw [block21_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31, h21]; simp
    · rw [block31_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31, h31]; simp
    · rw [block32_mul, levi_embedding_block12, levi_embedding_block22, levi_embedding_block32, h32]; simp
    · rw [Matrix.mul_assoc, hEmb_mul, Matrix.nonsing_inv_mul h (hP.unit hh), hEmb_one, Matrix.mul_one]

/- English proof (translation)
The claim follows from `prod_iff gpUnit x`.
-/
theorem isS_iff (x : Matrix (Idx r k) (Idx r k) A) : IsS x ↔ Par (fun h => IsUnit h.det) x :=
  prod_iff gpUnit x

/- English proof (translation)
The claim follows from `prod_iff gpUni x`.
-/
theorem isNU_iff (x : Matrix (Idx r k) (Idx r k) A) : IsNU x ↔ Par IsUpUni x :=
  prod_iff gpUni x

/- English proof (translation)
Take `⟨B, hB⟩` from `hQ`. Conclude with `⟨B, fun x => (h x).trans (hB x)⟩`.
-/
theorem subgroupSet_congr {Q Q' : Matrix (Idx r k) (Idx r k) A → Prop} (h : ∀ x, Q x ↔ Q' x)
    (hQ : IsSubgroupSet Q') : IsSubgroupSet Q := by
  obtain ⟨B, hB⟩ := hQ
  exact ⟨B, fun x => (h x).trans (hB x)⟩

/- English proof (translation)
Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, midEmb]`.
-/
theorem mul_midEmb_last {m : Type} (M : Matrix m (Mid k) A) (h : Matrix (Fin k) (Fin k) A) (a : m) :
    (M * midEmb h) a (Sum.inr ()) = M a (Sum.inr ()) := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, midEmb]

/- English proof (translation)
Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, midEmb]`.
-/
theorem midEmb_mul_last {m : Type} (M : Matrix (Mid k) m A) (h : Matrix (Fin k) (Fin k) A) (b : m) :
    (midEmb h * M) (Sum.inr ()) b = M (Sum.inr ()) b := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, midEmb]

/- English proof (translation)
Unfold `IsInertiaInfiniteCyclotomic`. Rewrite using `[isS_iff]`.
-/
theorem mem_pointwise_stabiliser_iff (x : Matrix (Idx r k) (Idx r k) A) : IsInertiaInfiniteCyclotomic x ↔ Par (fun h => IsUnit h.det) x ∧
    b11 x = 1 ∧ b33 x = 1 ∧ (∀ a, b12 x a (Sum.inr ()) = 0) ∧ ∀ b, b23 x (Sum.inr ()) b = 0 := by
  unfold IsInertiaInfiniteCyclotomic; rw [isS_iff]

/- English proof (translation)
Rewrite using `[mem_pointwise_stabiliser_iff]`. Conclude with `⟨par_one gpUnit, one_block11, block33_one, by simp [block12_one], by simp [block23_one]⟩`.
-/
theorem pointwise_stabiliser_one_mem : IsInertiaInfiniteCyclotomic (1 : Matrix (Idx r k) (Idx r k) A) := by
  rw [mem_pointwise_stabiliser_iff]
  exact ⟨par_one gpUnit, one_block11, block33_one, by simp [block12_one], by simp [block23_one]⟩

/- English proof (translation)
Rewrite `hx`, `hy`, the goal using `[mem_pointwise_stabiliser_iff]`. Take `⟨px, x11, x33, x12, x23⟩` from `hx`. Take `⟨py, y11, y33, y12, y23⟩` from `hy`. Use `⟨par_mul gpUnit px py, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨-, -, g21, g31, -⟩` from `py`.

Rewrite using `[block11_mul, g21, g31, x11, y11]`. Simplify using the standard rewrite rules. Take `⟨-, -, -, h31, h32, -⟩` from `px`. Rewrite using `[block33_mul, h31, h32, x33, y33]`. Simplify using the standard rewrite rules.

Introduce `a`. Take `⟨-, -, -, -, g32, g, -, g22⟩` from `py`. Rewrite using `[block12_mul, g32, g22, x11]`. Simplify using `[Matrix.add_apply, mul_midEmb_last, x12, y12]`. Introduce `b`.

Take `⟨-, -, h21, -, -, h, -, h22⟩` from `px`. Rewrite using `[block23_mul, h21, h22, y33]`. Simplify using `[Matrix.add_apply, midEmb_mul_last, x23, y23]`.
-/
theorem pointwise_stabiliser_mul_mem {x y : Matrix (Idx r k) (Idx r k) A} (hx : IsInertiaInfiniteCyclotomic x) (hy : IsInertiaInfiniteCyclotomic y) : IsInertiaInfiniteCyclotomic (x * y) := by
  rw [mem_pointwise_stabiliser_iff] at hx hy ⊢
  obtain ⟨px, x11, x33, x12, x23⟩ := hx
  obtain ⟨py, y11, y33, y12, y23⟩ := hy
  refine ⟨par_mul gpUnit px py, ?_, ?_, ?_, ?_⟩
  · obtain ⟨-, -, g21, g31, -⟩ := py
    rw [block11_mul, g21, g31, x11, y11]; simp
  · obtain ⟨-, -, -, h31, h32, -⟩ := px
    rw [block33_mul, h31, h32, x33, y33]; simp
  · intro a
    obtain ⟨-, -, -, -, g32, g, -, g22⟩ := py
    rw [block12_mul, g32, g22, x11]
    simp [Matrix.add_apply, mul_midEmb_last, x12, y12]
  · intro b
    obtain ⟨-, -, h21, -, -, h, -, h22⟩ := px
    rw [block23_mul, h21, h22, y33]
    simp [Matrix.add_apply, midEmb_mul_last, x23, y23]

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_pointwise_stabiliser_iff]`. Take `⟨px, x11, x33, x12, x23⟩` from `hx`. Establish `py` using `par_rinv gpUnit px e`. Take `⟨-, -, h21, h31, h32, h, -, h22⟩` from `px`. Take `⟨-, -, g21, g31, g32, g, -, g22⟩` from `id py`.

Establish `y11 : b11 y = 1`. Use `block11_mul x y` as an intermediate fact. Rewrite `this` using `[e, one_block11, g21, g31, x11]`. Simplify using `using this.symm`. Establish `y33 : b33 y = 1`.

Use `block33_mul x y` as an intermediate fact. Rewrite `this` using `[e, block33_one, h31, h32, x33]`. Simplify using `using this.symm`. Use `⟨py, y11, y33, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`.

Use `congrFun (congrFun (block12_mul x y) a) (Sum.inr ())` as an intermediate fact. Rewrite `this` using `[e, block12_one, g32, g22, x11]`. Simplify `this.symm` using `[Matrix.add_apply, mul_midEmb_last, x12]`. Introduce `b`. Use `congrFun (congrFun (block23_mul x y) (Sum.inr ())) b` as an intermediate fact.

Rewrite `this` using `[e, block23_one, h21, h22, y33]`. Simplify `this.symm` using `[Matrix.add_apply, midEmb_mul_last, x23]`.
-/
theorem pointwise_stabiliser_right_inverse_mem {x y : Matrix (Idx r k) (Idx r k) A} (hx : IsInertiaInfiniteCyclotomic x) (e : x * y = 1) : IsInertiaInfiniteCyclotomic y := by
  rw [mem_pointwise_stabiliser_iff] at hx ⊢
  obtain ⟨px, x11, x33, x12, x23⟩ := hx
  have py := par_rinv gpUnit px e
  obtain ⟨-, -, h21, h31, h32, h, -, h22⟩ := px
  obtain ⟨-, -, g21, g31, g32, g, -, g22⟩ := id py
  have y11 : b11 y = 1 := by
    have := block11_mul x y
    rw [e, one_block11, g21, g31, x11] at this
    simpa using this.symm
  have y33 : b33 y = 1 := by
    have := block33_mul x y
    rw [e, block33_one, h31, h32, x33] at this
    simpa using this.symm
  refine ⟨py, y11, y33, ?_, ?_⟩
  · intro a
    have := congrFun (congrFun (block12_mul x y) a) (Sum.inr ())
    rw [e, block12_one, g32, g22, x11] at this
    simpa [Matrix.add_apply, mul_midEmb_last, x12] using this.symm
  · intro b
    have := congrFun (congrFun (block23_mul x y) (Sum.inr ())) b
    rw [e, block23_one, h21, h22, y33] at this
    simpa [Matrix.add_apply, midEmb_mul_last, x23] using this.symm

def s0G : Subgroup (GL (Idx r k) A) where
  carrier := {g | IsInertiaInfiniteCyclotomic (g : Matrix (Idx r k) (Idx r k) A)}
  one_mem' := by simpa using pointwise_stabiliser_one_mem
  mul_mem' := by intro a b ha hb; simpa using pointwise_stabiliser_mul_mem ha hb
  inv_mem' := by
    intro a ha
    refine pointwise_stabiliser_right_inverse_mem ha ?_
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

/- English proof (translation)
Use `⟨s0G, fun x => ⟨fun hx => ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `⟨Matrix.GeneralLinearGroup.mk'' x (par_det gpUnit ((mem_pointwise_stabiliser_iff x).1 hx).1), hx, rfl⟩`. Introduce and unpack `⟨g, hg, rfl⟩`. Conclude with `hg`.
-/
theorem pointwise_stabiliser_is_subgroup : IsSubgroupSet (IsInertiaInfiniteCyclotomic (A := A) (r := r) (k := k)) := by
  refine ⟨s0G, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · exact ⟨Matrix.GeneralLinearGroup.mk'' x (par_det gpUnit ((mem_pointwise_stabiliser_iff x).1 hx).1), hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact hg

end Blocks

end Formalism.FourierDecayAlt.P.S3x1

open Formalism.FourierDecayAlt.P.S3x1 in
/- English proof (translation)
Introduce `A _ r k`. Conclude with `⟨subgroupSet_congr isN_iff (par_subgroupSet gpOne), emb_subgroupSet gpUnit, emb_subgroupSet gpUni, subgroupSet_congr isS_iff (par_subgroupSet gpUnit), subgroupSet_congr isNU_iff (par_subgroupSet gpUni), pointwise_stabiliser_is_subgroup⟩`.
-/
theorem Formalism.FourierDecayAlt.P.level_groups_are_subgroups : Formalism.FourierDecayAlt.S3.GroupsAreGroups := by
  intro A _ r k
  exact ⟨subgroupSet_congr isN_iff (par_subgroupSet gpOne), emb_subgroupSet gpUnit,
    emb_subgroupSet gpUni, subgroupSet_congr isS_iff (par_subgroupSet gpUnit),
    subgroupSet_congr isNU_iff (par_subgroupSet gpUni), pointwise_stabiliser_is_subgroup⟩

open Formalism.FourierDecayAlt.P.S3x1 in
/- English proof (translation)
Introduce `A _ r k x`. Conclude with `isS_iff x`.
-/
theorem Formalism.FourierDecayAlt.P.frame_stabiliser_explicit : Formalism.FourierDecayAlt.S3.SExplicit := by
  intro A _ r k x
  exact isS_iff x

open Formalism.FourierDecayAlt.P.S3x1 in
/- English proof (translation)
Introduce `A _ r k x`. Conclude with `isNU_iff x`.
-/
theorem Formalism.FourierDecayAlt.P.unipotent_levi_explicit : Formalism.FourierDecayAlt.S3.NUExplicit := by
  intro A _ r k x
  exact isNU_iff x

namespace Formalism.FourierDecayAlt.P.S3x1

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3

section Count

/- English proof (translation)
Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]`. Establish `h : ∀ j : Fin n, ∑ i : Fin n, (if i < j then 1 else 0) = (j : ℕ)`. Introduce `j`. Rewrite using `[← Finset.card_filter]`. Establish `e : Finset.filter (fun i : Fin n => i < j) Finset.univ = Finset.Iio j` using `by ext i; simp`.

Rewrite using `[e, Fin.card_Iio]`. Repeatedly rewrite using `[h]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]`.
-/
theorem card_lt_pairs (n : ℕ) : Nat.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  have h : ∀ j : Fin n, ∑ i : Fin n, (if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter]
    have e : Finset.filter (fun i : Fin n => i < j) Finset.univ = Finset.Iio j := by ext i; simp
    rw [e, Fin.card_Iio]
  simp_rw [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

/- English proof (translation)
Use `show Nat.card (m → n → K) = _`. Rewrite using `[Nat.card_fun, Nat.card_fun, ← pow_mul, mul_comm]`.
-/
theorem card_matrix (m n K : Type) [Finite m] [Finite n] :
    Nat.card (Matrix m n K) = Nat.card K ^ (Nat.card m * Nat.card n) := by
  show Nat.card (m → n → K) = _
  rw [Nat.card_fun, Nat.card_fun, ← pow_mul, mul_comm]

variable {A : Type} [CommRing A]

def uniEquiv (n : ℕ) : {u : Matrix (Fin n) (Fin n) A // IsUpUni u} ≃ ({p : Fin n × Fin n // p.1 < p.2} → A) where
  toFun u := fun p => u.1 p.1.1 p.1.2
  invFun f := ⟨Matrix.of fun i j => if h : i < j then f ⟨(i, j), h⟩ else if i = j then 1 else 0, by
    constructor
    · intro i j hij
      have hij' : j < i := hij
      simp [not_lt.2 hij'.le, hij'.ne']
    · intro a; simp⟩
  left_inv u := by
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h]
    · subst h; simp [u.2.2 i]
    · have : u.1 i j = 0 := u.2.1 h
      simp [not_lt.2 h.le, h.ne', this]
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    have h' : i < j := h
    simp [h']

/- English proof (translation)
Rewrite using `[Nat.card_congr (uniEquiv n), Nat.card_fun, card_lt_pairs, Nat.card_eq_fintype_card]`.
-/
theorem card_uni (K : Type) [Field K] [Fintype K] (n : ℕ) :
    Nat.card {u : Matrix (Fin n) (Fin n) K // IsUpUni u} = Fintype.card K ^ (n * (n - 1) / 2) := by
  rw [Nat.card_congr (uniEquiv n), Nat.card_fun, card_lt_pairs, Nat.card_eq_fintype_card]

noncomputable def upUniGEquiv (n : ℕ) : upUniG A n ≃ {u : Matrix (Fin n) (Fin n) A // IsUpUni u} where
  toFun g := ⟨g.1.1, g.2⟩
  invFun u := ⟨Matrix.GeneralLinearGroup.mk'' u.1 (uni_unit u.2), u.2⟩
  left_inv g := Subtype.ext (Units.ext rfl)
  right_inv u := rfl

noncomputable def glEquiv (n : ℕ) : GL (Fin n) A ≃ {h : Matrix (Fin n) (Fin n) A // IsUnit h.det} where
  toFun g := ⟨g.1, (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit⟩
  invFun h := Matrix.GeneralLinearGroup.mk'' h.1 h.2
  left_inv g := Units.ext rfl
  right_inv h := rfl

variable {r k : ℕ}

def mk (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A) :
    Matrix (Idx r k) (Idx r k) A :=
  Matrix.fromBlocks a (Matrix.fromCols b c) 0 (Matrix.fromBlocks m e 0 f)

section mk
variable (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A)
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[b11, mk]`.
-/
theorem block11_of_blocks : b11 (mk a b c m e f) = a := by ext i j; simp [b11, mk]
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[b12, mk]`.
-/
theorem block12_of_blocks : b12 (mk a b c m e f) = b := by ext i j; simp [b12, mk]
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[b13, mk]`.
-/
theorem block13_of_blocks : b13 (mk a b c m e f) = c := by ext i j; simp [b13, mk]
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[b21, mk]`.
-/
theorem block21_of_blocks : b21 (mk a b c m e f) = 0 := by ext i j; simp [b21, mk]
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[b22, mk]`.
-/
theorem block22_of_blocks : b22 (mk a b c m e f) = m := by ext i j; simp [b22, mk]
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[b23, mk]`.
-/
theorem block23_of_blocks : b23 (mk a b c m e f) = e := by ext i j; simp [b23, mk]
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[b31, mk]`.
-/
theorem block31_of_blocks : b31 (mk a b c m e f) = 0 := by ext i j; simp [b31, mk]
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[b32, mk]`.
-/
theorem block32_of_blocks : b32 (mk a b c m e f) = 0 := by ext i j; simp [b32, mk]
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[b33, mk]`.
-/
theorem block33_of_blocks : b33 (mk a b c m e f) = f := by ext i j; simp [b33, mk]
end mk

def parMap (P : Matrix (Fin k) (Fin k) A → Prop) :
    ({a : Matrix (Fin r) (Fin r) A // IsUpUni a} × {f : Matrix (Fin r) (Fin r) A // IsUpUni f} ×
      {h : Matrix (Fin k) (Fin k) A // P h} × Matrix (Fin r) (Mid k) A × Matrix (Fin r) (Fin r) A ×
      Matrix (Mid k) (Fin r) A) → {x : Matrix (Idx r k) (Idx r k) A // Par P x} :=
  fun t => ⟨mk t.1.1 t.2.2.2.1 t.2.2.2.2.1 (midEmb t.2.2.1.1) t.2.2.2.2.2 t.2.1.1,
    by rw [block11_of_blocks]; exact t.1.2, by rw [block33_of_blocks]; exact t.2.1.2, block21_of_blocks .., block31_of_blocks .., block32_of_blocks ..,
    t.2.2.1.1, t.2.2.1.2, block22_of_blocks ..⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨a, ha⟩, ⟨f, hf⟩, ⟨h, hh⟩, b, c, e⟩ ⟨⟨a', ha'⟩, ⟨f', hf'⟩, ⟨h', hh'⟩, b', c', e'⟩ E`. Establish `E'` using `congrArg Subtype.val E`. Simplify using `only [parMap] at E'`. Establish `e11` using `congrArg b11 E'`.

Establish `e12` using `congrArg b12 E'`. Establish `e13` using `congrArg b13 E'`. Establish `e22` using `congrArg b22 E'`. Establish `e23` using `congrArg b23 E'`. Establish `e33` using `congrArg b33 E'`.

Rewrite `e11` using `[block11_of_blocks, block11_of_blocks]`. Rewrite `e12` using `[block12_of_blocks, block12_of_blocks]`. Rewrite `e13` using `[block13_of_blocks, block13_of_blocks]`. Rewrite `e22` using `[block22_of_blocks, block22_of_blocks]`. Rewrite `e23` using `[block23_of_blocks, block23_of_blocks]`.

Rewrite `e33` using `[block33_of_blocks, block33_of_blocks]`. Establish `e22'` using `midEmb_inj e22`. Substitute `e11 e12 e13 e22' e23 e33` using the available equality. Both sides reduce to the same expression. Introduce and unpack `⟨x, h11, h33, h21, h31, h32, h, hh, h22⟩`.

Use `⟨⟨⟨b11 x, h11⟩, ⟨b33 x, h33⟩, ⟨h, hh⟩, b12 x, b13 x, b23 x⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [parMap]`. Apply `ext9` to reduce the goal to its premises. Rewrite using `[block11_of_blocks]`. Rewrite using `[block12_of_blocks]`.

Rewrite using `[block13_of_blocks]`. Rewrite using `[block21_of_blocks, h21]`. Rewrite using `[block22_of_blocks, h22]`. Rewrite using `[block23_of_blocks]`. Rewrite using `[block31_of_blocks, h31]`.

Rewrite using `[block32_of_blocks, h32]`. Rewrite using `[block33_of_blocks]`.
-/
theorem parMap_bij (P : Matrix (Fin k) (Fin k) A → Prop) : Function.Bijective (parMap (r := r) P) := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨f, hf⟩, ⟨h, hh⟩, b, c, e⟩ ⟨⟨a', ha'⟩, ⟨f', hf'⟩, ⟨h', hh'⟩, b', c', e'⟩ E
    have E' := congrArg Subtype.val E
    simp only [parMap] at E'
    have e11 := congrArg b11 E'
    have e12 := congrArg b12 E'
    have e13 := congrArg b13 E'
    have e22 := congrArg b22 E'
    have e23 := congrArg b23 E'
    have e33 := congrArg b33 E'
    rw [block11_of_blocks, block11_of_blocks] at e11
    rw [block12_of_blocks, block12_of_blocks] at e12
    rw [block13_of_blocks, block13_of_blocks] at e13
    rw [block22_of_blocks, block22_of_blocks] at e22
    rw [block23_of_blocks, block23_of_blocks] at e23
    rw [block33_of_blocks, block33_of_blocks] at e33
    have e22' := midEmb_inj e22
    subst e11 e12 e13 e22' e23 e33
    rfl
  · rintro ⟨x, h11, h33, h21, h31, h32, h, hh, h22⟩
    refine ⟨⟨⟨b11 x, h11⟩, ⟨b33 x, h33⟩, ⟨h, hh⟩, b12 x, b13 x, b23 x⟩, Subtype.ext ?_⟩
    simp only [parMap]
    apply ext9
    · rw [block11_of_blocks]
    · rw [block12_of_blocks]
    · rw [block13_of_blocks]
    · rw [block21_of_blocks, h21]
    · rw [block22_of_blocks, h22]
    · rw [block23_of_blocks]
    · rw [block31_of_blocks, h31]
    · rw [block32_of_blocks, h32]
    · rw [block33_of_blocks]

/- English proof (translation)
Rewrite using `[← Nat.card_congr (Equiv.ofBijective _ (parMap_bij (r := r) P))]`. Simplify using `only [Nat.card_prod]`. Simplify using `only [card_uni, card_matrix]`. Simplify using `only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_sum, Fintype.card_unit]`. Establish `h2 : r * (r - 1) / 2 + r * (r - 1) / 2 = r * (r - 1)`.

Use `Nat.div_mul_cancel (Nat.even_mul_pred_self r).two_dvd` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `: Fintype.card K ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) = Fintype.card K ^ (r * (r - 1) / 2) * Fintype.card K ^ (r * (r - 1) / 2) * (Fintype.card K ^ (r * (k + 1)) * (Fintype.card K ^ (r * r) * Fintype.card K ^ ((k + 1) * r)))`. Rewrite using `[← pow_add, ← pow_add, ← pow_add, ← pow_add, h2]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_par (K : Type) [Field K] [Fintype K] (r k : ℕ) (P : Matrix (Fin k) (Fin k) K → Prop) :
    Nat.card {x : Matrix (Idx r k) (Idx r k) K // Par P x} =
      Nat.card {h : Matrix (Fin k) (Fin k) K // P h} *
        Fintype.card K ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (parMap_bij (r := r) P))]
  simp only [Nat.card_prod]
  simp only [card_uni, card_matrix]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_sum, Fintype.card_unit]
  have h2 : r * (r - 1) / 2 + r * (r - 1) / 2 = r * (r - 1) := by
    have := Nat.div_mul_cancel (Nat.even_mul_pred_self r).two_dvd
    omega
  have : Fintype.card K ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) =
      Fintype.card K ^ (r * (r - 1) / 2) * Fintype.card K ^ (r * (r - 1) / 2) *
        (Fintype.card K ^ (r * (k + 1)) * (Fintype.card K ^ (r * r) * Fintype.card K ^ ((k + 1) * r))) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, h2]
    congr 1
    ring
  rw [this]
  ring

end Count

end Formalism.FourierDecayAlt.P.S3x1

namespace Formalism.FourierDecayAlt.P.S3x1

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3

section Count2

variable {A : Type} [CommRing A] {r k : ℕ}

def pointwiseStabiliserParametrisation : ({h : Matrix (Fin k) (Fin k) A // IsUnit h.det} × Matrix (Fin r) (Fin k) A ×
      Matrix (Fin r) (Fin r) A × Matrix (Fin k) (Fin r) A) →
    {x : Matrix (Idx r k) (Idx r k) A // IsInertiaInfiniteCyclotomic x} :=
  fun t => ⟨mk 1 (Matrix.fromCols t.2.1 0) t.2.2.1 (midEmb t.1.1) (Matrix.fromRows t.2.2.2 0) 1,
    (mem_pointwise_stabiliser_iff _).2 ⟨⟨by rw [block11_of_blocks]; exact isUpUni_one A, by rw [block33_of_blocks]; exact isUpUni_one A,
      block21_of_blocks .., block31_of_blocks .., block32_of_blocks .., t.1.1, t.1.2, block22_of_blocks ..⟩, block11_of_blocks .., block33_of_blocks ..,
      by intro a; rw [block12_of_blocks]; simp, by intro b; rw [block23_of_blocks]; simp⟩⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h, hh⟩, b, c, e⟩ ⟨⟨h', hh'⟩, b', c', e'⟩ E`. Establish `E'` using `congrArg Subtype.val E`. Simplify using `only [pointwiseStabiliserParametrisation] at E'`. Establish `e12` using `congrArg b12 E'`.

Establish `e13` using `congrArg b13 E'`. Establish `e22` using `congrArg b22 E'`. Establish `e23` using `congrArg b23 E'`. Rewrite `e12` using `[block12_of_blocks, block12_of_blocks]`. Rewrite `e13` using `[block13_of_blocks, block13_of_blocks]`.

Rewrite `e22` using `[block22_of_blocks, block22_of_blocks]`. Rewrite `e23` using `[block23_of_blocks, block23_of_blocks]`. Establish `e22'` using `midEmb_inj e22`. Establish `e12'` using `(Matrix.fromCols_inj e12).1`. Establish `e23'` using `(Matrix.fromRows_inj e23).1`.

Substitute `e12' e13 e22' e23'` using the available equality. Both sides reduce to the same expression. Introduce and unpack `⟨x, hx⟩`. Take `⟨⟨-, -, h21, h31, h32, h, hh, h22⟩, x11, x33, x12, x23⟩` from `(mem_pointwise_stabiliser_iff x).1 hx`. Use `⟨⟨⟨h, hh⟩, (b12 x).toCols₁, b13 x, (b23 x).toRows₁⟩, Subtype.ext ?_⟩` and prove the remaining obligations.

Simplify using `only [pointwiseStabiliserParametrisation]`. Apply `ext9` to reduce the goal to its premises. Rewrite using `[block11_of_blocks, x11]`. Rewrite using `[block12_of_blocks]`. Use extensionality with `a j`.

Break down `j with j | j` into its components or cases. Simplify using `[Matrix.toCols₁]`. Simplify using `[x12 a]`. Rewrite using `[block13_of_blocks]`. Rewrite using `[block21_of_blocks, h21]`.

Rewrite using `[block22_of_blocks, h22]`. Rewrite using `[block23_of_blocks]`. Use extensionality with `j b`. Break down `j with j | j` into its components or cases. Simplify using `[Matrix.toRows₁]`.

Simplify using `[x23 b]`. Rewrite using `[block31_of_blocks, h31]`. Rewrite using `[block32_of_blocks, h32]`. Rewrite using `[block33_of_blocks, x33]`.
-/
theorem pointwise_stabiliser_parametrisation_bijective : Function.Bijective (pointwiseStabiliserParametrisation (A := A) (r := r) (k := k)) := by
  constructor
  · rintro ⟨⟨h, hh⟩, b, c, e⟩ ⟨⟨h', hh'⟩, b', c', e'⟩ E
    have E' := congrArg Subtype.val E
    simp only [pointwiseStabiliserParametrisation] at E'
    have e12 := congrArg b12 E'
    have e13 := congrArg b13 E'
    have e22 := congrArg b22 E'
    have e23 := congrArg b23 E'
    rw [block12_of_blocks, block12_of_blocks] at e12
    rw [block13_of_blocks, block13_of_blocks] at e13
    rw [block22_of_blocks, block22_of_blocks] at e22
    rw [block23_of_blocks, block23_of_blocks] at e23
    have e22' := midEmb_inj e22
    have e12' := (Matrix.fromCols_inj e12).1
    have e23' := (Matrix.fromRows_inj e23).1
    subst e12' e13 e22' e23'
    rfl
  · rintro ⟨x, hx⟩
    obtain ⟨⟨-, -, h21, h31, h32, h, hh, h22⟩, x11, x33, x12, x23⟩ := (mem_pointwise_stabiliser_iff x).1 hx
    refine ⟨⟨⟨h, hh⟩, (b12 x).toCols₁, b13 x, (b23 x).toRows₁⟩, Subtype.ext ?_⟩
    simp only [pointwiseStabiliserParametrisation]
    apply ext9
    · rw [block11_of_blocks, x11]
    · rw [block12_of_blocks]
      ext a j
      rcases j with j | j
      · simp [Matrix.toCols₁]
      · simp [x12 a]
    · rw [block13_of_blocks]
    · rw [block21_of_blocks, h21]
    · rw [block22_of_blocks, h22]
    · rw [block23_of_blocks]
      ext j b
      rcases j with j | j
      · simp [Matrix.toRows₁]
      · simp [x23 b]
    · rw [block31_of_blocks, h31]
    · rw [block32_of_blocks, h32]
    · rw [block33_of_blocks, x33]

/- English proof (translation)
Rewrite using `[← Nat.card_congr (Equiv.ofBijective _ (pointwise_stabiliser_parametrisation_bijective (A := K) (r := r) (k := k)))]`. Simplify using `only [Nat.card_prod]`. Simplify using `only [card_matrix]`. Simplify using `only [Nat.card_eq_fintype_card, Fintype.card_fin]`. Rewrite using `[pow_add, pow_add]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem nat_card_pointwise_stabiliser (K : Type) [Field K] [Fintype K] (r k : ℕ) :
    Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsInertiaInfiniteCyclotomic x} =
      Nat.card {h : Matrix (Fin k) (Fin k) K // IsUnit h.det} *
        Fintype.card K ^ (r * k + r * r + k * r) := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (pointwise_stabiliser_parametrisation_bijective (A := K) (r := r) (k := k)))]
  simp only [Nat.card_prod]
  simp only [card_matrix]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [pow_add, pow_add]
  ring

/- English proof (translation)
Rewrite using `[Nat.card_congr (Equiv.subtypeEquivRight isN_iff), card_par, Nat.card_unique, one_mul]`.
-/
theorem card_isN (K : Type) [Field K] [Fintype K] (r k : ℕ) :
    Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsN x} =
      Fintype.card K ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight isN_iff), card_par, Nat.card_unique, one_mul]

/- English proof (translation)
Rewrite using `[Nat.card_congr (Equiv.subtypeEquivRight isS_iff), card_par]`.
-/
theorem card_isS (K : Type) [Field K] [Fintype K] (r k : ℕ) :
    Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsS x} =
      Nat.card {h : Matrix (Fin k) (Fin k) K // IsUnit h.det} *
        Fintype.card K ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight isS_iff), card_par]

/- English proof (translation)
Rewrite using `[Nat.card_congr (Equiv.subtypeEquivRight isNU_iff), card_par]`.
-/
theorem card_isNU (K : Type) [Field K] [Fintype K] (r k : ℕ) :
    Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsNU x} =
      Nat.card {h : Matrix (Fin k) (Fin k) K // IsUpUni h} *
        Fintype.card K ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight isNU_iff), card_par]

/- English proof (translation)
Rewrite using `[Fin.prod_univ_eq_prod_range (fun i => q ^ k - q ^ i) k, ← Finset.sum_range_id, ← Finset.prod_pow_eq_pow_sum]`. Establish `h1 : ∏ i ∈ Icc 1 k, (q ^ i - 1) = ∏ i ∈ range k, (q ^ (k - i) - 1)`. Use `Finset.prod_nbij' (fun i => k - i) (fun i => k - i) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a ha`. Simplify using `only [Finset.mem_Icc, Finset.mem_range] at ha ⊢`.

Use linear arithmetic over natural numbers and integers. Introduce `a ha`. Simplify using `only [Finset.mem_Icc, Finset.mem_range] at ha ⊢`. Use linear arithmetic over natural numbers and integers. Introduce `a ha`.

Simplify using `only [Finset.mem_Icc, Finset.mem_range] at ha ⊢`. Use linear arithmetic over natural numbers and integers. Introduce `a ha`. Simplify using `only [Finset.mem_Icc, Finset.mem_range] at ha ⊢`. Use linear arithmetic over natural numbers and integers.

Introduce `a ha`. Simplify using `only [Finset.mem_Icc] at ha`. Establish `: k - (k - a) = a` using `by omega`. Rewrite using `[this]`. Rewrite using `[h1, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i ≤ k` using `(Finset.mem_range.1 hi).le`. Rewrite using `[Nat.mul_sub, ← pow_add, Nat.add_sub_cancel' hi', mul_one]`.
-/
theorem prod_gl (q k : ℕ) : ∏ i : Fin k, (q ^ k - q ^ (i : ℕ)) =
    q ^ (k * (k - 1) / 2) * ∏ i ∈ Icc 1 k, (q ^ i - 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => q ^ k - q ^ i) k, ← Finset.sum_range_id,
    ← Finset.prod_pow_eq_pow_sum]
  have h1 : ∏ i ∈ Icc 1 k, (q ^ i - 1) = ∏ i ∈ range k, (q ^ (k - i) - 1) := by
    refine Finset.prod_nbij' (fun i => k - i) (fun i => k - i) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      have : k - (k - a) = a := by omega
      rw [this]
  rw [h1, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i ≤ k := (Finset.mem_range.1 hi).le
  rw [Nat.mul_sub, ← pow_add, Nat.add_sub_cancel' hi', mul_one]

end Count2

end Formalism.FourierDecayAlt.P.S3x1

open Formalism.FourierDecayAlt.P.S3x1 in
/- English proof (translation)
Introduce `K _ _ r k`. Conclude with `card_isN K r k`.
-/
theorem Formalism.FourierDecayAlt.P.card_unipotent_radical : Formalism.FourierDecayAlt.S3.CardN := by
  intro K _ _ r k
  exact card_isN K r k

open Formalism.FourierDecayAlt.P.S3x1 in
/- English proof (translation)
Introduce `K _ _ r k`. Rewrite using `[card_isS, card_isN, Nat.card_congr (glEquiv k)]`.
-/
theorem Formalism.FourierDecayAlt.P.card_frame_stabiliser : Formalism.FourierDecayAlt.S3.CardS := by
  intro K _ _ r k
  rw [card_isS, card_isN, Nat.card_congr (glEquiv k)]

open Formalism.FourierDecayAlt.P.S3x1 in
/- English proof (translation)
Introduce `K _ _ r k`. Rewrite using `[card_isNU, card_isN, Nat.card_congr (upUniGEquiv k), mul_comm]`.
-/
theorem Formalism.FourierDecayAlt.P.card_unipotent_levi_product : Formalism.FourierDecayAlt.S3.CardNU := by
  intro K _ _ r k
  rw [card_isNU, card_isN, Nat.card_congr (upUniGEquiv k), mul_comm]

open Formalism.FourierDecayAlt.P.S3x1 in
/- English proof (translation)
Introduce `K _ _ k`. Rewrite using `[Nat.card_congr (upUniGEquiv k), card_uni]`.
-/
theorem Formalism.FourierDecayAlt.P.card_unitary_levi : Formalism.FourierDecayAlt.S3.CardUk := by
  intro K _ _ k
  rw [Nat.card_congr (upUniGEquiv k), card_uni]

open Formalism.FourierDecayAlt.P.S3x1 in
/- English proof (translation)
Introduce `K _ _ k`. Rewrite using `[Matrix.card_GL_field, Nat.card_congr (upUniGEquiv k), card_uni, prod_gl]`.
-/
theorem Formalism.FourierDecayAlt.P.gamma_factor_product : Formalism.FourierDecayAlt.S3.GammaProduct := by
  intro K _ _ k
  rw [Matrix.card_GL_field, Nat.card_congr (upUniGEquiv k), card_uni, prod_gl]

open Formalism.FourierDecayAlt.P.S3x1 in
/- English proof (translation)
Introduce `K _ _ r k`. Rewrite using `[card_isS, nat_card_pointwise_stabiliser, Nat.mul_assoc (Nat.card _) (_ ^ _) (_ ^ _), ← pow_add]`. Use `congr 2`. Break down `r with _ | r` into its components or cases. Simplify using the standard rewrite rules.

Simplify using `only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Formalism.FourierDecayAlt.P.card_pointwise_stabiliser : Formalism.FourierDecayAlt.S3.StabiliserIndexFinite := by
  intro K _ _ r k
  rw [card_isS, nat_card_pointwise_stabiliser, Nat.mul_assoc (Nat.card _) (_ ^ _) (_ ^ _), ← pow_add]
  congr 2
  rcases r with _ | r
  · simp
  · simp only [Nat.add_sub_cancel]
    ring
