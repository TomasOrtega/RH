import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTermOrigin
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

noncomputable section

namespace GlobalTheory.DualFormExists

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def riemannBil (ξ : E) : LinearMap.BilinForm ℚ E :=
  LinearMap.mk₂ ℚ (riemann ξ)
    (fun x x' y => by simp [riemann, mul_add, add_mul, map_add])
    (fun q x y => by
      simp only [riemann, smul_eq_mul]
      rw [show ξ * (q • x) * IsCMField.complexConj E y = q • (ξ * x * IsCMField.complexConj E y) by
        rw [mul_smul_comm, smul_mul_assoc], map_smul, smul_eq_mul])
    (fun x y y' => by simp [riemann, mul_add, map_add])
    (fun q x y => by
      have h : IsCMField.complexConj E (q • y) = q • IsCMField.complexConj E y := map_rat_smul _ q y
      simp only [riemann, smul_eq_mul, h]
      rw [mul_smul_comm, map_smul, smul_eq_mul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem riemannBil_apply (ξ x y : E) : riemannBil ξ x y = riemann ξ x y := rfl

/- English proof (translation)
Assume the negation of the conclusion as `h0`. Establish `h1` using `hx (IsCMField.complexConj E (ξ * x)⁻¹)`. Rewrite `h1` using `[riemann, IsCMField.complexConj_apply_apply, mul_inv_cancel₀ (mul_ne_zero hξ h0)]`. Rewrite `h1` using `[show (1 : E) = algebraMap ℚ E 1 by simp, Algebra.trace_algebraMap]`. Use `Module.finrank_pos (R := ℚ) (M := E)` as an intermediate fact.

Simplify using `at h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem riemann_left_nondeg (ξ : E) (hξ : ξ ≠ 0) (x : E) (hx : ∀ y, riemann ξ x y = 0) : x = 0 := by
  by_contra h0
  have h1 := hx (IsCMField.complexConj E (ξ * x)⁻¹)
  rw [riemann, IsCMField.complexConj_apply_apply,
    mul_inv_cancel₀ (mul_ne_zero hξ h0)] at h1
  rw [show (1 : E) = algebraMap ℚ E 1 by simp, Algebra.trace_algebraMap] at h1
  have := Module.finrank_pos (R := ℚ) (M := E)
  simp at h1
  omega

def riemannClL (ξ : E) : E →ₗ[ℚ] Coh E where
  toFun := riemannCl ξ
  map_add' x x' := by
    ext y; simp [riemannCl, riemann, mul_add, add_mul, map_add]
  map_smul' q x := by
    ext y
    show ((riemann ξ (q • x) y : ℚ) : ℂ) = q • ((riemann ξ x y : ℚ) : ℂ)
    rw [← riemannBil_apply, LinearMap.map_smul₂, riemannBil_apply, smul_eq_mul, Rat.cast_mul, Rat.smul_def]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem riemannClL_apply (ξ x : E) : riemannClL ξ x = riemannCl ξ x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem riemannCl_apply (ξ x y : E) : riemannCl ξ x y = (riemann ξ x y : ℂ) := rfl

def gram (ξ : E) : Matrix (Fin (Module.finrank ℚ E)) (Fin (Module.finrank ℚ E)) ℚ :=
  LinearMap.toMatrix₂ (Module.finBasis ℚ E) (Module.finBasis ℚ E) (riemannBil ξ)

/- English proof (translation)
Simplify using `[gram, LinearMap.toMatrix₂_apply, riemannBil_apply]`.
-/
theorem gram_apply (ξ : E) (i j) : gram ξ i j = riemann ξ (Module.finBasis ℚ E i) (Module.finBasis ℚ E j) := by
  simp [gram, LinearMap.toMatrix₂_apply, riemannBil_apply]

/- English proof (translation)
Introduce `hd`. Take `⟨v, hv, hv0⟩` from `Matrix.exists_vecMul_eq_zero_iff.mpr hd`. Apply `hv` to reduce the goal to its premises. Use `set b := Module.finBasis ℚ E`. Establish `hx : (∑ i, v i • b i) = 0`.

Apply `riemann_left_nondeg ξ hξ` to reduce the goal to its premises. Introduce `y`. Rewrite using `[← riemannBil_apply, ← b.sum_repr y]`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `j _`. Use `congrFun hv0 j` as an intermediate fact. Simplify using `only [Matrix.vecMul, dotProduct, gram_apply, Pi.zero_apply] at this`. Conclude with `mul_eq_zero_of_right _ this`. Use `b.linearIndependent` as an intermediate fact.

Conclude with `Fintype.linearIndependent_iff.mp this v hx |> funext`.
-/
theorem gram_det_ne_zero (ξ : E) (hξ : ξ ≠ 0) : (gram ξ).det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
  apply hv
  set b := Module.finBasis ℚ E
  have hx : (∑ i, v i • b i) = 0 := by
    apply riemann_left_nondeg ξ hξ
    intro y
    rw [← riemannBil_apply, ← b.sum_repr y]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro j _
    have := congrFun hv0 j
    simp only [Matrix.vecMul, dotProduct, gram_apply, Pi.zero_apply] at this
    exact mul_eq_zero_of_right _ this
  have := b.linearIndependent
  exact Fintype.linearIndependent_iff.mp this v hx |> funext

end GlobalTheory.DualFormExists

namespace GlobalTheory.DualFormExists
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Rewrite using `[← ((Module.finBasis ℚ E).constr ℂ).finrank_eq, Module.finrank_fin_fun]`.
-/
theorem finrank_coh : Module.finrank ℂ (Coh E) = Module.finrank ℚ E := by
  rw [← ((Module.finBasis ℚ E).constr ℂ).finrank_eq, Module.finrank_fin_fun]

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Use `set Gc := (gram ξ).map (Rat.castHom ℂ)`. Establish `hdet : Gc.det ≠ 0`. Rewrite using `[show Gc = (Rat.castHom ℂ).mapMatrix (gram ξ) from rfl, ← RingHom.map_det]`.

Simplify using `using gram_det_ne_zero ξ hξ`. Establish `hv : Matrix.vecMul c Gc = 0`. Use function extensionality and compare the values at `j`. Use `LinearMap.congr_fun hc (Module.finBasis ℚ E j)` as an intermediate fact. Simplify `this` using `[Matrix.vecMul, dotProduct, Gc, gram_apply, riemannCl_apply]`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Take `⟨i, hi⟩` from `h`. Conclude with `hdet (Matrix.exists_vecMul_eq_zero_iff.mp ⟨c, fun h0 => hi (by simp [h0]), hv⟩)`.
-/
theorem riemannCl_linInd (ξ : E) (hξ : ξ ≠ 0) :
    LinearIndependent ℂ (fun i => riemannCl ξ (Module.finBasis ℚ E i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  set Gc := (gram ξ).map (Rat.castHom ℂ)
  have hdet : Gc.det ≠ 0 := by
    rw [show Gc = (Rat.castHom ℂ).mapMatrix (gram ξ) from rfl, ← RingHom.map_det]
    simpa using gram_det_ne_zero ξ hξ
  have hv : Matrix.vecMul c Gc = 0 := by
    funext j
    have := LinearMap.congr_fun hc (Module.finBasis ℚ E j)
    simpa [Matrix.vecMul, dotProduct, Gc, gram_apply, riemannCl_apply] using this
  by_contra h
  push_neg at h
  obtain ⟨i, hi⟩ := h
  exact hdet (Matrix.exists_vecMul_eq_zero_iff.mp ⟨c, fun h0 => hi (by simp [h0]), hv⟩)

def clBasis (ξ : E) (hξ : ξ ≠ 0) : Module.Basis (Fin (Module.finrank ℚ E)) ℂ (Coh E) :=
  haveI : Nonempty (Fin (Module.finrank ℚ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
  basisOfLinearIndependentOfCardEqFinrank (riemannCl_linInd ξ hξ) (by simp [finrank_coh])

/- English proof (translation)
Simplify using `[clBasis]`.
-/
theorem clBasis_apply (ξ : E) (hξ : ξ ≠ 0) (i) : clBasis ξ hξ i = riemannCl ξ (Module.finBasis ℚ E i) := by
  simp [clBasis]

/- English proof (translation)
Establish `h : riemannCl ξ x = (clBasis ξ hξ).equivFun.symm (fun i => (((Module.finBasis ℚ E).repr x i : ℚ) : ℂ))`. Rewrite using `[Module.Basis.equivFun_symm_apply]`. Use `conv_lhs => rw [← riemannClL_apply, ← (Module.finBasis ℚ E).sum_repr x]`. Simplify using `only [map_sum, map_smul, clBasis_apply, riemannClL_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use extensionality with `y`. Simplify using `[Rat.smul_def]`. Rewrite using `[h, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`.
-/
theorem clBasis_repr (ξ : E) (hξ : ξ ≠ 0) (x : E) (i) :
    (clBasis ξ hξ).repr (riemannCl ξ x) i = (((Module.finBasis ℚ E).repr x i : ℚ) : ℂ) := by
  have h : riemannCl ξ x = (clBasis ξ hξ).equivFun.symm (fun i => (((Module.finBasis ℚ E).repr x i : ℚ) : ℂ)) := by
    rw [Module.Basis.equivFun_symm_apply]
    conv_lhs => rw [← riemannClL_apply, ← (Module.finBasis ℚ E).sum_repr x]
    simp only [map_sum, map_smul, clBasis_apply, riemannClL_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext y
    simp [Rat.smul_def]
  rw [h, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.DualFormExists

namespace GlobalTheory.DualFormExists

/- English proof (translation)
Introduce `E _ _ _ ξ hξ`. Use `set b := Module.finBasis ℚ E`. Use `set cb := clBasis ξ hξ`. Use `set Gc : Matrix (Fin (Module.finrank ℚ E)) (Fin (Module.finrank ℚ E)) ℂ := fun i j => ((gram ξ i j : ℚ) : ℂ)`. Use `⟨Matrix.toLinearMap₂ cb cb Gc, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x y`. Rewrite using `[Matrix.toLinearMap₂_apply]`. Simplify using `only [cb, clBasis_repr]`. Rewrite using `[← riemannBil_apply, ← Matrix.toLinearMap₂_toMatrix₂ b b (riemannBil ξ), Matrix.toLinearMap₂_apply]`. Use `push_cast`.

Simplify using `[Gc, gram, b]`. Introduce `B' hB'`. Apply `LinearMap.ext_basis cb cb` to reduce the goal to its premises. Introduce `i j`. Rewrite using `[Matrix.toLinearMap₂_apply_basis, clBasis_apply, clBasis_apply, hB']`.

Simplify using `[Gc, gram_apply, b]`.
-/
theorem dualForm_existsUnique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ξ : E), ξ ≠ 0 →
    ∃! B : LinearMap.BilinForm ℂ (Coh E), IsDualForm ξ B := by
  intro E _ _ _ ξ hξ
  set b := Module.finBasis ℚ E
  set cb := clBasis ξ hξ
  set Gc : Matrix (Fin (Module.finrank ℚ E)) (Fin (Module.finrank ℚ E)) ℂ := fun i j => ((gram ξ i j : ℚ) : ℂ)
  refine ⟨Matrix.toLinearMap₂ cb cb Gc, ?_, ?_⟩
  · intro x y
    rw [Matrix.toLinearMap₂_apply]
    simp only [cb, clBasis_repr]
    rw [← riemannBil_apply, ← Matrix.toLinearMap₂_toMatrix₂ b b (riemannBil ξ), Matrix.toLinearMap₂_apply]
    push_cast
    simp [Gc, gram, b]
  · intro B' hB'
    apply LinearMap.ext_basis cb cb
    intro i j
    rw [Matrix.toLinearMap₂_apply_basis, clBasis_apply, clBasis_apply, hB']
    simp [Gc, gram_apply, b]

end GlobalTheory.DualFormExists
