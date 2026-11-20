import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalRationalTranslate
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT cT_mul cT_one)

namespace GlobalTheory.EisCT

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r X Y hcm hJ hW w hw hwyx ν hν hS`. Establish `hxy : cT (σ : E →+* E) (col0 X) * J * col0 Y = 1`. Use extensionality with `i j`. Establish `h` using `congrFun (congrFun hW.xy 0) 0`. Use `fin_cases i`.

Use `fin_cases j`. Simplify `h` using `[col0, cT, Matrix.mul_apply]`. Use `set x := col0 X`. Use `set y := col0 Y`. Use `set M := (matHom _ σ J ν).1 with hMdef`.

Use `set S := sigR (AF F) σ`. Establish `c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT S (adMat F Z) = adMat F (cT (σ : E →+* E) Z)` using `fun Z => rfl`. Establish `hxyA : cT S (adMat F x) * adMat F J * adMat F y = 1`. Rewrite using `[c1]`. Simplify using `only [adMat, ← Matrix.map_mul, hxy]`.

Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Take `⟨hMx, B, hB⟩` from `(mem_unipRad_iff_dual hxy ν).1 hν`. Establish `hMx' : M * adMat F x = adMat F x`. Rewrite `hMx` using `[Matrix.sub_mul, Matrix.one_mul, sub_eq_zero]`. Conclude with `hMx`.

Establish `hU : cT S M * adMat F J * M = adMat F J` using `ν.2`. Take `⟨l, hl⟩` from `hS`. Use `set W := matHom _ σ J w`. Establish `hWi : (W⁻¹).1 * adMat F x = adMat F y`. Rewrite using `[← hwyx, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]`.

Establish `hMy : M * adMat F y = l.1 • adMat F y`. Rewrite `hl` using `[map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, hWi]`. Use `congrArg ((W⁻¹).1 * ·) hl` as an intermediate fact. Rewrite `this` using `[← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_smul, hWi]`. Conclude with `this`.

Establish `hxJM : cT S (adMat F x) * adMat F J * M = cT S (adMat F x) * adMat F J` using `by conv_lhs => rw [← hMx']`. Rewrite using `[cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT S M), hU]`. Establish `hl1 : l.1 = 1`. Establish `h1` using `congrArg (· * adMat F y) hxJM`. Rewrite `h1` using `[Matrix.mul_assoc _ M, hMy, Matrix.mul_smul, hxyA]`.

Use `congrFun (congrFun h1 0) 0` as an intermediate fact. Simplify using `using this`. Rewrite `hMy` using `[hl1, one_smul]`. Establish `hmy : (M - 1) * adMat F y = 0` using `by rw [Matrix.sub_mul, Matrix.one_mul, hMy, sub_self]`. Establish `e : adMat F (1 - y * (cT (σ : E →+* E) x * J)) = 1 - adMat F y * (cT S (adMat F x) * adMat F J)`.

Rewrite using `[c1]`. Simplify using `only [adMat]`. Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, Matrix.map_mul]`. Rewrite `hB` using `[e, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hmy, Matrix.zero_mul, sub_zero]`. Establish `hM1 : M = adMat F x * B + 1` using `sub_eq_iff_eq_add.1 hB`.

Establish `cadd : ∀ P Q : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), cT S (P + Q) = cT S P + cT S Q` using `fun P Q => by`. Use extensionality with `i j`. Simplify using `[cT]`. Establish `hUy` using `congrArg (· * adMat F y) hU`. Rewrite `hUy` using `[Matrix.mul_assoc _ M, hMy]`.

Use `conv_lhs at hUy => rw [hM1]`. Rewrite `hUy` using `[cadd, cT_one, cT_mul, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc (cT S B), Matrix.mul_assoc (cT S B), hxyA, Matrix.mul_one, add_eq_right]`. Establish `hss : ∀ a : AF F ⊗[F] E, S (S a) = a` using `fun a => by`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul a e => exact congrArg (a ⊗ₜ[F] ·) (GlobalTheory.SiegelSet.sigma_sigma hcm e)`. Establish `hB0 : B = 0`. Use extensionality with `i j`. Use `congrFun (congrFun hUy j) i` as an intermediate fact.

Simplify using `only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.zero_apply] at this`. Rewrite using `[Matrix.zero_apply, ← hss (B i j), this, map_zero]`. Rewrite `hM1` using `[hB0, Matrix.mul_zero, zero_add]`. Apply `matHom_injective (AF F) σ J` to reduce the goal to its premises. Rewrite using `[map_one]`.

Conclude with `Units.ext hM1`.
-/
theorem bigCell_uniq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ w ∈ ratPts σ J, (matHom _ σ J w).1 * adMat F (col0 Y) = adMat F (col0 X) →
    ∀ ν ∈ unipRad σ J (col0 X), GlobalTheory.EisCT.StabL σ J (col0 X) (w * ν * w⁻¹) → ν = 1 := by
  intro F E _ _ _ _ _ σ n J r X Y hcm hJ hW w hw hwyx ν hν hS
  have hxy : cT (σ : E →+* E) (col0 X) * J * col0 Y = 1 := by
    ext i j
    have h := congrFun (congrFun hW.xy 0) 0
    fin_cases i; fin_cases j
    simpa [col0, cT, Matrix.mul_apply] using h
  set x := col0 X
  set y := col0 Y
  set M := (matHom _ σ J ν).1 with hMdef
  set S := sigR (AF F) σ
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT S (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have hxyA : cT S (adMat F x) * adMat F J * adMat F y = 1 := by
    rw [c1]; simp only [adMat, ← Matrix.map_mul, hxy]; exact Matrix.map_one _ (map_zero _) (map_one _)
  obtain ⟨hMx, B, hB⟩ := (mem_unipRad_iff_dual hxy ν).1 hν
  have hMx' : M * adMat F x = adMat F x := by
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hMx; exact hMx
  have hU : cT S M * adMat F J * M = adMat F J := ν.2
  obtain ⟨l, hl⟩ := hS
  set W := matHom _ σ J w
  have hWi : (W⁻¹).1 * adMat F x = adMat F y := by
    rw [← hwyx, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have hMy : M * adMat F y = l.1 • adMat F y := by
    rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, hWi] at hl
    have := congrArg ((W⁻¹).1 * ·) hl
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_smul, hWi] at this
    exact this
  have hxJM : cT S (adMat F x) * adMat F J * M = cT S (adMat F x) * adMat F J := by
    conv_lhs => rw [← hMx']
    rw [cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT S M), hU]
  have hl1 : l.1 = 1 := by
    have h1 := congrArg (· * adMat F y) hxJM
    rw [Matrix.mul_assoc _ M, hMy, Matrix.mul_smul, hxyA] at h1
    have := congrFun (congrFun h1 0) 0
    simpa using this
  rw [hl1, one_smul] at hMy
  have hmy : (M - 1) * adMat F y = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hMy, sub_self]
  have e : adMat F (1 - y * (cT (σ : E →+* E) x * J)) = 1 - adMat F y * (cT S (adMat F x) * adMat F J) := by
    rw [c1]
    simp only [adMat]
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, Matrix.map_mul]
  rw [e, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hmy, Matrix.zero_mul, sub_zero] at hB
  have hM1 : M = adMat F x * B + 1 := sub_eq_iff_eq_add.1 hB
  have cadd : ∀ P Q : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), cT S (P + Q) = cT S P + cT S Q := fun P Q => by
    ext i j; simp [cT]
  have hUy := congrArg (· * adMat F y) hU
  rw [Matrix.mul_assoc _ M, hMy] at hUy
  conv_lhs at hUy => rw [hM1]
  rw [cadd, cT_one, cT_mul, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc (cT S B),
    Matrix.mul_assoc (cT S B), hxyA, Matrix.mul_one, add_eq_right] at hUy
  have hss : ∀ a : AF F ⊗[F] E, S (S a) = a := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a e => exact congrArg (a ⊗ₜ[F] ·) (GlobalTheory.SiegelSet.sigma_sigma hcm e)
  have hB0 : B = 0 := by
    ext i j
    have := congrFun (congrFun hUy j) i
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.zero_apply] at this
    rw [Matrix.zero_apply, ← hss (B i j), this, map_zero]
  rw [hB0, Matrix.mul_zero, zero_add] at hM1
  apply matHom_injective (AF F) σ J
  rw [map_one]
  exact Units.ext hM1

end GlobalTheory.EisCT
