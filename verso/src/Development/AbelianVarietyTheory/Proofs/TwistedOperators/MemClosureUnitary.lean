import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryTranspose
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique

noncomputable section

namespace GlobalTheory.RealApprox

open scoped TensorProduct Matrix

/- English proof (translation)
Use `Module.Free.of_basis b` as an intermediate fact. Use `Module.Finite.of_basis b` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 (hx.map (Algebra.leftMulMatrix b))`.

Introduce `hd`. Rewrite `hd` using `[Algebra.leftMulMatrix_apply, LinearMap.det_toMatrix, ← LinearMap.isUnit_iff_isUnit_det]`. Take `⟨y, hy⟩ : ∃ y, Algebra.lmul A R x y = 1` from `((Module.End.isUnit_iff _).1 hd).2 1`. Establish `hxy : x * y = 1` using `by simpa using hy`. Conclude with `⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩`.
-/
private lemma isUnit_iff_isUnit_det_leftMulMatrix {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A R) (x : R) :
    IsUnit x ↔ IsUnit (Algebra.leftMulMatrix b x).det := by
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  constructor
  · intro hx
    exact (Matrix.isUnit_iff_isUnit_det _).1 (hx.map (Algebra.leftMulMatrix b))
  · intro hd
    rw [Algebra.leftMulMatrix_apply, LinearMap.det_toMatrix, ← LinearMap.isUnit_iff_isUnit_det] at hd
    obtain ⟨y, hy⟩ : ∃ y, Algebra.lmul A R x y = 1 := ((Module.End.isUnit_iff _).1 hd).2 1
    have hxy : x * y = 1 := by simpa using hy
    exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩

/- English proof (translation)
Rewrite using `[Algebra.leftMulMatrix_mulVec_repr, mul_one]`. Conclude with `b.sum_repr y`.
-/
private lemma sum_leftMulMatrix_mulVec_repr_one_smul_eq {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A R) (y : R) :
    ∑ i, (Algebra.leftMulMatrix b y *ᵥ ⇑(b.repr 1)) i • b i = y := by
  rw [Algebra.leftMulMatrix_mulVec_repr, mul_one]
  exact b.sum_repr y

/- English proof (translation)
Use `set M := Algebra.leftMulMatrix b with hM`. Establish `hMc : Continuous M` using `IsModuleTopology.continuous_of_linearMap M.toLinearMap`. Establish `hdet : Continuous (fun x : R => (M x).det)` using `hMc.matrix_det`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hset : {x : R | IsUnit x} = (fun x => (M x).det) ⁻¹' {a : A | IsUnit a}`.

Use extensionality with `x`. Conclude with `isUnit_iff_isUnit_det_leftMulMatrix b x`. Rewrite using `[hset]`. Conclude with `h1.preimage hdet`. Introduce `x hx`.

Use `IsModuleTopology.toContinuousSMul A R` as an intermediate fact. Use `IsModuleTopology.toContinuousAdd A R` as an intermediate fact. Set `L : Matrix ι ι A → R` to `fun N => ∑ i, (N *ᵥ ⇑(b.repr 1)) i • b i`. Establish `hL : Continuous L`. Use `continuous_finsetSum _ fun i _ => ?_` and prove the remaining obligations.

Conclude with `((continuous_apply i).comp (continuous_id.matrix_mulVec continuous_const)).smul continuous_const`. Establish `heq : (Ring.inverse : R → R) = fun y => L ((M y)⁻¹)`. Use function extensionality and compare the values at `y`. Use `show Ring.inverse y = L ((M y)⁻¹)`. Distinguish the cases in `hy : IsUnit y`.

Establish `hinv : (M y)⁻¹ = M (Ring.inverse y)`. Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations. Rewrite using `[← map_mul, Ring.inverse_mul_cancel y hy, map_one]`. Rewrite using `[hinv]`. Conclude with `(sum_leftMulMatrix_mulVec_repr_one_smul_eq b _).symm`.

Establish `hd : ¬ IsUnit (M y).det` using `fun h => hy ((isUnit_iff_isUnit_det_leftMulMatrix b y).2 h)`. Rewrite using `[Ring.inverse_non_unit y hy, Matrix.nonsing_inv_apply_not_isUnit _ hd]`. Simplify using `[L]`. Establish `hu : IsUnit (M x).det` using `(isUnit_iff_isUnit_det_leftMulMatrix b x).1 hx`. Establish `hinvc : ContinuousAt (fun N : Matrix ι ι A => N⁻¹) (M x)`.

Establish `hform : (fun N : Matrix ι ι A => N⁻¹) = fun N => Ring.inverse N.det • N.adjugate`. Use function extensionality and compare the values at `N`. Conclude with `Matrix.inv_def N`. Rewrite using `[hform]`. Conclude with `((h2 _ hu).comp (continuous_id.matrix_det.continuousAt)).smul continuous_id.matrix_adjugate.continuousAt`.

Rewrite using `[heq]`. Conclude with `hL.continuousAt.comp (hinvc.comp hMc.continuousAt)`.
-/
theorem units_of_free {A R : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [CommRing R]
    [Algebra A R] [TopologicalSpace R] [IsModuleTopology A R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A R) (h1 : IsOpen {x : A | IsUnit x})
    (h2 : ∀ x : A, IsUnit x → ContinuousAt Ring.inverse x) :
    IsOpen {x : R | IsUnit x} ∧ ∀ x : R, IsUnit x → ContinuousAt Ring.inverse x := by
  set M := Algebra.leftMulMatrix b with hM
  have hMc : Continuous M := IsModuleTopology.continuous_of_linearMap M.toLinearMap
  have hdet : Continuous (fun x : R => (M x).det) := hMc.matrix_det
  refine ⟨?_, ?_⟩
  · have hset : {x : R | IsUnit x} = (fun x => (M x).det) ⁻¹' {a : A | IsUnit a} := by
      ext x
      exact isUnit_iff_isUnit_det_leftMulMatrix b x
    rw [hset]
    exact h1.preimage hdet
  · intro x hx
    have := IsModuleTopology.toContinuousSMul A R
    have := IsModuleTopology.toContinuousAdd A R
    let L : Matrix ι ι A → R := fun N => ∑ i, (N *ᵥ ⇑(b.repr 1)) i • b i
    have hL : Continuous L := by
      refine continuous_finsetSum _ fun i _ => ?_
      exact ((continuous_apply i).comp (continuous_id.matrix_mulVec continuous_const)).smul continuous_const
    have heq : (Ring.inverse : R → R) = fun y => L ((M y)⁻¹) := by
      funext y
      show Ring.inverse y = L ((M y)⁻¹)
      by_cases hy : IsUnit y
      · have hinv : (M y)⁻¹ = M (Ring.inverse y) := by
          refine Matrix.inv_eq_left_inv ?_
          rw [← map_mul, Ring.inverse_mul_cancel y hy, map_one]
        rw [hinv]
        exact (sum_leftMulMatrix_mulVec_repr_one_smul_eq b _).symm
      · have hd : ¬ IsUnit (M y).det := fun h => hy ((isUnit_iff_isUnit_det_leftMulMatrix b y).2 h)
        rw [Ring.inverse_non_unit y hy, Matrix.nonsing_inv_apply_not_isUnit _ hd]
        simp [L]
    have hu : IsUnit (M x).det := (isUnit_iff_isUnit_det_leftMulMatrix b x).1 hx
    have hinvc : ContinuousAt (fun N : Matrix ι ι A => N⁻¹) (M x) := by
      have hform : (fun N : Matrix ι ι A => N⁻¹) = fun N => Ring.inverse N.det • N.adjugate := by
        funext N
        exact Matrix.inv_def N
      rw [hform]
      exact ((h2 _ hu).comp (continuous_id.matrix_det.continuousAt)).smul
        continuous_id.matrix_adjugate.continuousAt
    rw [heq]
    exact hL.continuousAt.comp (hinvc.comp hMc.continuousAt)

/- English proof (translation)
Use `set φ : Matrix (Fin n) (Fin n) A →+* Matrix (Fin n) (Fin n) A := σ.mapMatrix with hφdef`. Establish `hφ : ∀ M : Matrix (Fin n) (Fin n) A, M.map σ = φ M` using `fun _ => rfl`. Simplify using `only [hφ] at hS ⊢`. Establish `hS' : Sᵀ * G = -(G * φ S)` using `eq_neg_of_add_eq_zero_left hS`. Establish `e1 : (1 - S)ᵀ * G = G * φ (1 + S)`.

Rewrite using `[Matrix.transpose_sub, Matrix.transpose_one, sub_mul, hS', map_add, map_one]`. Use `noncomm_ring`. Establish `e2 : (1 + S)ᵀ * G = G * φ (1 - S)`. Rewrite using `[Matrix.transpose_add, Matrix.transpose_one, add_mul, hS', map_sub, map_one]`. Use `noncomm_ring`.

Establish `e3 : (1 + S) * ((1 - S) * V) = 1 - S`. Rewrite using `[← mul_assoc, show (1 + S) * (1 - S) = (1 - S) * (1 + S) by noncomm_ring, mul_assoc, hV', mul_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.transpose_mul]`. Simplify using `only [mul_assoc]`.

Use `_ = Vᵀ * G * φ ((1 + S) * ((1 - S) * V)) := by rw [e1, map_mul φ (1 + S)]; simp only [mul_assoc]`. Use `_ = Vᵀ * G * φ (1 - S) := by rw [e3]`. Use `_ = Vᵀ * ((1 + S)ᵀ * G) := by rw [e2]; simp only [mul_assoc]`. Use `_ = ((1 + S) * V)ᵀ * G := by rw [Matrix.transpose_mul]; simp only [mul_assoc]`. Use `_ = G := by rw [hV', Matrix.transpose_one, one_mul]`.
-/
private theorem cayley_preserves_form_of_skew {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (G S V : Matrix (Fin n) (Fin n) A)
    (hS : Sᵀ * G + G * S.map σ = 0) (hV' : (1 + S) * V = 1) :
    ((1 - S) * V)ᵀ * G * ((1 - S) * V).map σ = G := by
  set φ : Matrix (Fin n) (Fin n) A →+* Matrix (Fin n) (Fin n) A := σ.mapMatrix with hφdef
  have hφ : ∀ M : Matrix (Fin n) (Fin n) A, M.map σ = φ M := fun _ => rfl
  simp only [hφ] at hS ⊢
  have hS' : Sᵀ * G = -(G * φ S) := eq_neg_of_add_eq_zero_left hS
  have e1 : (1 - S)ᵀ * G = G * φ (1 + S) := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, sub_mul, hS', map_add, map_one]; noncomm_ring
  have e2 : (1 + S)ᵀ * G = G * φ (1 - S) := by
    rw [Matrix.transpose_add, Matrix.transpose_one, add_mul, hS', map_sub, map_one]; noncomm_ring
  have e3 : (1 + S) * ((1 - S) * V) = 1 - S := by
    rw [← mul_assoc, show (1 + S) * (1 - S) = (1 - S) * (1 + S) by noncomm_ring, mul_assoc, hV', mul_one]
  calc ((1 - S) * V)ᵀ * G * φ ((1 - S) * V) = Vᵀ * ((1 - S)ᵀ * G) * φ ((1 - S) * V) := by
        rw [Matrix.transpose_mul]; simp only [mul_assoc]
    _ = Vᵀ * G * φ ((1 + S) * ((1 - S) * V)) := by rw [e1, map_mul φ (1 + S)]; simp only [mul_assoc]
    _ = Vᵀ * G * φ (1 - S) := by rw [e3]
    _ = Vᵀ * ((1 + S)ᵀ * G) := by rw [e2]; simp only [mul_assoc]
    _ = ((1 + S) * V)ᵀ * G := by rw [Matrix.transpose_mul]; simp only [mul_assoc]
    _ = G := by rw [hV', Matrix.transpose_one, one_mul]

/- English proof (translation)
Use `set φ : Matrix (Fin n) (Fin n) A →+* Matrix (Fin n) (Fin n) A := σ.mapMatrix with hφdef`. Establish `hφ : ∀ M : Matrix (Fin n) (Fin n) A, M.map σ = φ M` using `fun _ => rfl`. Simplify using `only [hφ] at hh ⊢`. Take `⟨S, hSdef⟩ : ∃ S, S = (1 - h) * V` from `⟨_, rfl⟩`. Rewrite using `[← hSdef]`.

Establish `hS1 : S * (1 + h) = 1 - h` using `by rw [hSdef, mul_assoc, hV, mul_one]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hX : (1 + h)ᵀ * (Sᵀ * G + G * φ S) * φ (1 + h) = 0`. Establish `e0 : (1 + h)ᵀ * (Sᵀ * G + G * φ S) * φ (1 + h) = (S * (1 + h))ᵀ * G * φ (1 + h) + (1 + h)ᵀ * G * φ (S * (1 + h))`. Rewrite using `[Matrix.transpose_mul, map_mul]`.

Use `noncomm_ring`. Rewrite using `[e0, hS1, Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one, map_add, map_sub, map_one]`. Establish `e : (1 - hᵀ) * G * (1 + φ h) + (1 + hᵀ) * G * (1 - φ h) = G + G - (hᵀ * G * φ h + hᵀ * G * φ h)` using `by noncomm_ring`. Rewrite using `[e, hh, sub_self]`. Establish `a : Vᵀ * (1 + h)ᵀ = 1` using `by rw [← Matrix.transpose_mul, hV', Matrix.transpose_one]`.

Establish `b : φ (1 + h) * φ V = 1` using `by rw [← map_mul, hV', map_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[a, b, one_mul, mul_one]`. Use `_ = Vᵀ * ((1 + h)ᵀ * (Sᵀ * G + G * φ S) * φ (1 + h)) * φ V := by simp only [mul_assoc]`. Use `_ = 0 := by rw [hX, mul_zero, zero_mul]`.

Rewrite using `[Matrix.mul_smul]`. Establish `e : (1 + S) * (1 + h) = 1 + 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e, smul_add, ← add_smul, ← two_mul, ht, one_smul]`. Rewrite using `[Matrix.mul_smul]`.

Establish `e : (1 - S) * (1 + h) = h + h`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e, smul_add, ← add_smul, ← two_mul, ht, one_smul]`.
-/
private theorem cayley_skew_and_inverse_of_preserves_form {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (G h V : Matrix (Fin n) (Fin n) A)
    (t : A) (ht : 2 * t = 1) (hh : hᵀ * G * h.map σ = G) (hV : V * (1 + h) = 1) (hV' : (1 + h) * V = 1) :
    ((1 - h) * V)ᵀ * G + G * ((1 - h) * V).map σ = 0 ∧
    (1 + (1 - h) * V) * (t • (1 + h)) = 1 ∧
    (1 - (1 - h) * V) * (t • (1 + h)) = h := by
  set φ : Matrix (Fin n) (Fin n) A →+* Matrix (Fin n) (Fin n) A := σ.mapMatrix with hφdef
  have hφ : ∀ M : Matrix (Fin n) (Fin n) A, M.map σ = φ M := fun _ => rfl
  simp only [hφ] at hh ⊢
  obtain ⟨S, hSdef⟩ : ∃ S, S = (1 - h) * V := ⟨_, rfl⟩
  rw [← hSdef]
  have hS1 : S * (1 + h) = 1 - h := by rw [hSdef, mul_assoc, hV, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · have hX : (1 + h)ᵀ * (Sᵀ * G + G * φ S) * φ (1 + h) = 0 := by
      have e0 : (1 + h)ᵀ * (Sᵀ * G + G * φ S) * φ (1 + h) =
          (S * (1 + h))ᵀ * G * φ (1 + h) + (1 + h)ᵀ * G * φ (S * (1 + h)) := by
        rw [Matrix.transpose_mul, map_mul]; noncomm_ring
      rw [e0, hS1, Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one, map_add, map_sub, map_one]
      have e : (1 - hᵀ) * G * (1 + φ h) + (1 + hᵀ) * G * (1 - φ h) =
          G + G - (hᵀ * G * φ h + hᵀ * G * φ h) := by noncomm_ring
      rw [e, hh, sub_self]
    have a : Vᵀ * (1 + h)ᵀ = 1 := by rw [← Matrix.transpose_mul, hV', Matrix.transpose_one]
    have b : φ (1 + h) * φ V = 1 := by rw [← map_mul, hV', map_one]
    calc Sᵀ * G + G * φ S = (Vᵀ * (1 + h)ᵀ) * (Sᵀ * G + G * φ S) * (φ (1 + h) * φ V) := by
          rw [a, b, one_mul, mul_one]
      _ = Vᵀ * ((1 + h)ᵀ * (Sᵀ * G + G * φ S) * φ (1 + h)) * φ V := by simp only [mul_assoc]
      _ = 0 := by rw [hX, mul_zero, zero_mul]
  · rw [Matrix.mul_smul]
    have e : (1 + S) * (1 + h) = 1 + 1 := by
      calc (1 + S) * (1 + h) = (1 + h) + S * (1 + h) := by noncomm_ring
        _ = 1 + 1 := by rw [hS1]; noncomm_ring
    rw [e, smul_add, ← add_smul, ← two_mul, ht, one_smul]
  · rw [Matrix.mul_smul]
    have e : (1 - S) * (1 + h) = h + h := by
      calc (1 - S) * (1 + h) = (1 + h) - S * (1 + h) := by noncomm_ring
        _ = h + h := by rw [hS1]; noncomm_ring
    rw [e, smul_add, ← add_smul, ← two_mul, ht, one_smul]

/- English proof (translation)
Establish `hP : GlobalTheory.UnRep.WeakApprox.skewPart σ G X = X - (G * X.map σ * G⁻¹)ᵀ` using `rfl`. Establish `hinv : G⁻¹.map σ = (G.map σ)⁻¹` using `(GlobalTheory.UnRep.WeakApprox.map_inv' σ G hGu).symm`. Establish `hinvol : (X.map σ).map σ = X` using `by ext i j; simp [hσ]`. Establish `hGG : G⁻¹ * G = 1` using `Matrix.nonsing_inv_mul G hGu`. Establish `hGG' : G * G⁻¹ = 1` using `Matrix.mul_nonsing_inv G hGu`.

Use `set φ : Matrix (Fin n) (Fin n) A →+* Matrix (Fin n) (Fin n) A := σ.mapMatrix with hφdef`. Establish `hφ : ∀ M : Matrix (Fin n) (Fin n) A, M.map σ = φ M` using `fun _ => rfl`. Establish `hT : ∀ M : Matrix (Fin n) (Fin n) A, φ Mᵀ = (φ M)ᵀ` using `fun M => by`. Simplify using `only [← hφ]`. Conclude with `Matrix.transpose_map`.

Rewrite using `[hP]`. Simplify using `only [hφ] at hinv hinvol hG ⊢`. Establish `hGinvT : (φ G⁻¹)ᵀ = G⁻¹` using `by rw [hinv, Matrix.transpose_nonsing_inv, hG]`. Rewrite using `[Matrix.transpose_sub, Matrix.transpose_transpose, map_sub, hT, map_mul, map_mul, hinvol, Matrix.transpose_mul, Matrix.transpose_mul, hG, hGinvT]`. Establish `e1 : (Xᵀ - G * φ X * G⁻¹) * G + G * (φ X - G⁻¹ * (Xᵀ * G)) = Xᵀ * G - G * φ X * (G⁻¹ * G) + G * φ X - (G * G⁻¹) * (Xᵀ * G)` using `by noncomm_ring`.

Rewrite using `[e1, hGG, hGG']`. Use `noncomm_ring`.
-/
private theorem skew_component_is_skew {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) A) (hG : (G.map σ)ᵀ = G) (hGu : IsUnit G.det) (X : Matrix (Fin n) (Fin n) A) :
    (GlobalTheory.UnRep.WeakApprox.skewPart σ G X)ᵀ * G + G * (GlobalTheory.UnRep.WeakApprox.skewPart σ G X).map σ = 0 := by
  have hP : GlobalTheory.UnRep.WeakApprox.skewPart σ G X = X - (G * X.map σ * G⁻¹)ᵀ := rfl
  have hinv : G⁻¹.map σ = (G.map σ)⁻¹ := (GlobalTheory.UnRep.WeakApprox.map_inv' σ G hGu).symm
  have hinvol : (X.map σ).map σ = X := by ext i j; simp [hσ]
  have hGG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hGu
  have hGG' : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hGu
  set φ : Matrix (Fin n) (Fin n) A →+* Matrix (Fin n) (Fin n) A := σ.mapMatrix with hφdef
  have hφ : ∀ M : Matrix (Fin n) (Fin n) A, M.map σ = φ M := fun _ => rfl
  have hT : ∀ M : Matrix (Fin n) (Fin n) A, φ Mᵀ = (φ M)ᵀ := fun M => by
    simp only [← hφ]; exact Matrix.transpose_map
  rw [hP]
  simp only [hφ] at hinv hinvol hG ⊢
  have hGinvT : (φ G⁻¹)ᵀ = G⁻¹ := by rw [hinv, Matrix.transpose_nonsing_inv, hG]
  rw [Matrix.transpose_sub, Matrix.transpose_transpose, map_sub, hT, map_mul, map_mul, hinvol,
    Matrix.transpose_mul, Matrix.transpose_mul, hG, hGinvT]
  have e1 : (Xᵀ - G * φ X * G⁻¹) * G + G * (φ X - G⁻¹ * (Xᵀ * G)) =
      Xᵀ * G - G * φ X * (G⁻¹ * G) + G * φ X - (G * G⁻¹) * (Xᵀ * G) := by noncomm_ring
  rw [e1, hGG, hGG']; noncomm_ring

/- English proof (translation)
Establish `h1 : G * S.map σ = -(Sᵀ * G)` using `eq_neg_of_add_eq_zero_right hS`. Use `show S - (G * S.map σ * G⁻¹)ᵀ = S + S`. Rewrite using `[h1, neg_mul, mul_assoc, Matrix.mul_nonsing_inv _ hGu, mul_one, Matrix.transpose_neg, Matrix.transpose_transpose, sub_neg_eq_add]`.
-/
private theorem skew_component_eq_add_self_of_skew {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (G S : Matrix (Fin n) (Fin n) A)
    (hS : Sᵀ * G + G * S.map σ = 0) (hGu : IsUnit G.det) :
    GlobalTheory.UnRep.WeakApprox.skewPart σ G S = S + S := by
  have h1 : G * S.map σ = -(Sᵀ * G) := eq_neg_of_add_eq_zero_right hS
  show S - (G * S.map σ * G⁻¹)ᵀ = S + S
  rw [h1, neg_mul, mul_assoc, Matrix.mul_nonsing_inv _ hGu, mul_one, Matrix.transpose_neg,
    Matrix.transpose_transpose, sub_neg_eq_add]

/- English proof (translation)
Rewrite using `[Matrix.transpose_smul, GlobalTheory.UnRep.WeakApprox.map_smul'' σ μ X, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, hX, hμ, one_smul]`.
-/
private theorem smul_preserves_form_of_mul_conj_eq_one {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (G : Matrix (Fin n) (Fin n) A)
    (μ : A) (hμ : μ * σ μ = 1) (X : Matrix (Fin n) (Fin n) A) (hX : Xᵀ * G * X.map σ = G) :
    (μ • X)ᵀ * G * (μ • X).map σ = G := by
  rw [Matrix.transpose_smul, GlobalTheory.UnRep.WeakApprox.map_smul'' σ μ X, smul_mul_assoc, smul_mul_assoc,
    mul_smul_comm, smul_smul, hX, hμ, one_smul]

/- English proof (translation)
Take `⟨z, hz⟩` from `hne`. Establish `hw : ∀ k : ℕ, (k : K) + z ≠ 0`. Introduce `k h`. Apply `hz` to reduce the goal to its premises. Establish `hz' : z = -(k : K)` using `by linear_combination h`.

Rewrite using `[hz', map_neg, map_natCast]`. Establish `hcw : ∀ k : ℕ, c ((k : K) + z) ≠ 0`. Introduce `k h`. Apply `hw k` to reduce the goal to its premises. Use `congrArg c h` as an intermediate fact.

Rewrite `this` using `[hc, map_zero]`. Then use the resulting hypothesis. Use `set lam : ℕ → K := fun k => ((k : K) + z) / c ((k : K) + z) with hlamdef`. Establish `hlam : ∀ k, lam k * c (lam k) = 1`. Introduce `k`. Simplify using `only [hlamdef, map_div₀, hc]`.

Rewrite using `[div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (hcw k) (hw k)), mul_comm]`. Establish `hinj : Function.Injective lam`. Introduce `a b hab`. Simplify using `only [hlamdef] at hab`. Rewrite `hab` using `[div_eq_div_iff (hcw a) (hcw b)]`.

Simplify using `only [map_add, map_natCast] at hab`. Establish `h0 : ((a : K) - b) * (c z - z) = 0` using `by linear_combination hab`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `sub_eq_zero.1 h` after adjusting the coercions. Conclude with `absurd (sub_eq_zero.1 h) hz`.

Establish `hfin` using `IsArtinianRing.setOfPred_isMaximal_finite R`. Establish `hbad : ∀ I ∈ {I : Ideal R | I.IsMaximal}, {k : ℕ | (1 + ι (lam k) • g).det ∈ I}.Finite`. Introduce `I hI`. Use `haveI : I.IsMaximal := hI`. Use `letI := Ideal.Quotient.field I`.

Use `set π := Ideal.Quotient.mk I with hπ`. Use `set p : Polynomial (R ⧸ I) := (1 + (Polynomial.X : Polynomial (R ⧸ I)) • (g.map π).map Polynomial.C).det with hpdef`. Establish `hev : ∀ r : R, p.eval (π r) = π (1 + r • g).det`. Introduce `r`. Rewrite using `[hpdef, ← Polynomial.coe_evalRingHom, RingHom.map_det, RingHom.map_det]`.

Use `congr 1`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [hij] <;> ring`. Establish `hp : p ≠ 0`. Introduce `h0`.

Use `hev 0` as an intermediate fact. Rewrite `this` using `[h0, Polynomial.eval_zero, zero_smul, add_zero, Matrix.det_one, map_one]`. Conclude with `zero_ne_one this`. Establish `hroots` using `Polynomial.finite_setOfPred_isRoot hp`. Establish `hinj' : Function.Injective (fun k => π (ι (lam k)))` using `(RingHom.injective (π.comp ι)).comp hinj`.

Use `(Set.Finite.preimage hinj'.injOn hroots).subset ?_` and prove the remaining obligations. Introduce `k hk`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_preimage] at hk ⊢`. Use `show p.eval (π (ι (lam k))) = 0`. Rewrite using `[hev]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 hk`. Establish `hB` using `hfin.biUnion hbad`. Take `⟨N, hN⟩` from `hB.bddAbove`. Use `⟨lam (N + 1), hlam _, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hu`.

Take `⟨I, hI, hmem⟩` from `exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hu)`. Establish `hm : N + 1 ∈ ⋃ I ∈ {I : Ideal R | I.IsMaximal}, {k : ℕ | (1 + ι (lam k) • g).det ∈ I}` using `Set.mem_biUnion hI hmem`. Conclude with `Nat.not_succ_le_self N (hN hm)`.
-/
private theorem exists_norm_one_isUnit_det_one_add_smul {K R : Type} [Field K] [CharZero K] [CommRing R] [IsArtinianRing R]
    (ι : K →+* R) (c : K →+* K) (hc : ∀ x, c (c x) = x) (hne : ∃ z, c z ≠ z) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) R) : ∃ lam : K, lam * c lam = 1 ∧ IsUnit (1 + ι lam • g).det := by
  obtain ⟨z, hz⟩ := hne
  have hw : ∀ k : ℕ, (k : K) + z ≠ 0 := by
    intro k h
    apply hz
    have hz' : z = -(k : K) := by linear_combination h
    rw [hz', map_neg, map_natCast]
  have hcw : ∀ k : ℕ, c ((k : K) + z) ≠ 0 := by
    intro k h
    apply hw k
    have := congrArg c h
    rwa [hc, map_zero] at this
  set lam : ℕ → K := fun k => ((k : K) + z) / c ((k : K) + z) with hlamdef
  have hlam : ∀ k, lam k * c (lam k) = 1 := by
    intro k
    simp only [hlamdef, map_div₀, hc]
    rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (hcw k) (hw k)), mul_comm]
  have hinj : Function.Injective lam := by
    intro a b hab
    simp only [hlamdef] at hab
    rw [div_eq_div_iff (hcw a) (hcw b)] at hab
    simp only [map_add, map_natCast] at hab
    have h0 : ((a : K) - b) * (c z - z) = 0 := by linear_combination hab
    rcases mul_eq_zero.1 h0 with h | h
    · exact_mod_cast sub_eq_zero.1 h
    · exact absurd (sub_eq_zero.1 h) hz
  have hfin := IsArtinianRing.setOfPred_isMaximal_finite R
  have hbad : ∀ I ∈ {I : Ideal R | I.IsMaximal}, {k : ℕ | (1 + ι (lam k) • g).det ∈ I}.Finite := by
    intro I hI
    haveI : I.IsMaximal := hI
    letI := Ideal.Quotient.field I
    set π := Ideal.Quotient.mk I with hπ
    set p : Polynomial (R ⧸ I) := (1 + (Polynomial.X : Polynomial (R ⧸ I)) • (g.map π).map Polynomial.C).det
      with hpdef
    have hev : ∀ r : R, p.eval (π r) = π (1 + r • g).det := by
      intro r
      rw [hpdef, ← Polynomial.coe_evalRingHom, RingHom.map_det, RingHom.map_det]
      congr 1
      ext i j
      by_cases hij : i = j <;> simp [hij] <;> ring
    have hp : p ≠ 0 := by
      intro h0
      have := hev 0
      rw [h0, Polynomial.eval_zero, zero_smul, add_zero, Matrix.det_one, map_one] at this
      exact zero_ne_one this
    have hroots := Polynomial.finite_setOfPred_isRoot hp
    have hinj' : Function.Injective (fun k => π (ι (lam k))) := (RingHom.injective (π.comp ι)).comp hinj
    refine (Set.Finite.preimage hinj'.injOn hroots).subset ?_
    intro k hk
    simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hk ⊢
    show p.eval (π (ι (lam k))) = 0
    rw [hev]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hk
  have hB := hfin.biUnion hbad
  obtain ⟨N, hN⟩ := hB.bddAbove
  refine ⟨lam (N + 1), hlam _, ?_⟩
  by_contra hu
  obtain ⟨I, hI, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hu)
  have hm : N + 1 ∈ ⋃ I ∈ {I : Ideal R | I.IsMaximal}, {k : ℕ | (1 + ι (lam k) • g).det ∈ I} :=
    Set.mem_biUnion hI hmem
  exact Nat.not_succ_le_self N (hN hm)

open GlobalTheory.UnRep.WeakApprox in

/- English proof (translation)
Establish `hGu : IsUnit G.det` using `isUnit_iff_ne_zero.2 hdet`. Establish `hdetmap : ∀ M : Matrix (Fin n) (Fin n) K, (M.map ι).det = ι M.det` using `fun M => (RingHom.map_det ι M).symm`. Establish `hG'u : IsUnit (G.map ι).det` using `by rw [hdetmap]; exact hGu.map ι`. Establish `hmapc : ∀ M : Matrix (Fin n) (Fin n) K, (M.map ι).map σ = (M.map c).map ι`. Introduce `M`.

Use extensionality with `i j`. Simplify using `[hσι]`. Take `⟨lam, hlam, hu⟩` from `exists_norm_one_isUnit_det_one_add_smul ι c hc hne g`. Establish `hlam' : ι lam * σ (ι lam) = 1` using `by rw [hσι, ← map_mul, hlam, map_one]`. Establish `hh : (ι lam • g)ᵀ * G.map ι * (ι lam • g).map σ = G.map ι` using `smul_preserves_form_of_mul_conj_eq_one σ (G.map ι) (ι lam) hlam' g hg`.

Establish `hV : (1 + ι lam • g)⁻¹ * (1 + ι lam • g) = 1` using `Matrix.nonsing_inv_mul _ hu`. Establish `hV' : (1 + ι lam • g) * (1 + ι lam • g)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hu`. Establish `h2K : (2 : K) ≠ 0` using `two_ne_zero`. Establish `ht : 2 * ι (2⁻¹ : K) = 1` using `by rw [← map_ofNat ι 2, ← map_mul, mul_inv_cancel₀ h2K, map_one]`. Establish `hσt : σ (ι (2⁻¹ : K)) = ι (2⁻¹ : K)` using `by rw [hσι, map_inv₀, map_ofNat]`.

Take `⟨hskew, hinvS, hcay⟩` from `cayley_skew_and_inverse_of_preserves_form σ (G.map ι) (ι lam • g) _ (ι (2⁻¹ : K)) ht hh hV hV'`. Use `set S := (1 - ι lam • g) * (1 + ι lam • g)⁻¹ with hSdef`. Use `set t : R := ι (2⁻¹ : K) with htdef`. Establish `hSu : IsUnit (1 + S).det` using `Matrix.isUnit_det_of_right_inverse hinvS`. Establish `hSinv : (1 + S)⁻¹ = t • (1 + ι lam • g)` using `Matrix.inv_eq_right_inv hinvS`.

Establish `hPS : skewPart σ (G.map ι) (t • S) = S`. Rewrite using `[skewPart_smul σ (G.map ι) t hσt S, skew_component_eq_add_self_of_skew σ (G.map ι) S hskew hG'u, smul_add, ← add_smul, ← two_mul, ht, one_smul]`. Use `set Ψ : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R := fun A => ι (c lam) • ((1 - skewPart σ (G.map ι) A) * (1 + skewPart σ (G.map ι) A)⁻¹) with hΨ`. Establish `hΨA : Ψ (t • S) = g` using `by show ι (c lam) • ((1 - skewPart σ (G.map ι) (t • S)) * (1 + skewPart σ (G.map ι) (t • S))⁻¹) = g`. Rewrite using `[hPS, hSinv, hcay, smul_smul, ← map_mul, mul_comm, hlam, map_one, one_smul]`.

Establish `hPc : Continuous (fun A : Matrix (Fin n) (Fin n) R => skewPart σ (G.map ι) A)` using `by show Continuous (fun A : Matrix (Fin n) (Fin n) R => A - (G.map ι * A.map σ * (G.map ι)⁻¹)ᵀ)`. Conclude with `continuous_id.sub (((continuous_const.matrix_mul (continuous_id.matrix_map hσc)).matrix_mul continuous_const).matrix_transpose)`. Establish `hdetc : Continuous (fun A : Matrix (Fin n) (Fin n) R => (1 + skewPart σ (G.map ι) A).det)` using `(continuous_const.add hPc).matrix_det`. Use `set U := {A : Matrix (Fin n) (Fin n) R | IsUnit (1 + skewPart σ (G.map ι) A).det} with hUdef`. Establish `hU : IsOpen U` using `hdetc.isOpen_preimage _ h1`.

Establish `hAU : t • S ∈ U` using `by show IsUnit (1 + skewPart σ (G.map ι) (t • S)).det`. Rewrite using `[hPS]`. Conclude with `hSu`. Establish `hdense : DenseRange (fun A : Matrix (Fin n) (Fin n) K => A.map ι)` using `DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hd))`. Establish `hcl : t • S ∈ closure (U ∩ Set.range (fun A : Matrix (Fin n) (Fin n) K => A.map ι))` using `Dense.open_subset_closure_inter hdense hU hAU`.

Establish `hΨc : ContinuousAt Ψ (t • S)`. Establish `hinvc : ContinuousAt (fun A : Matrix (Fin n) (Fin n) R => Ring.inverse (1 + skewPart σ (G.map ι) A).det) (t • S)` using `ContinuousAt.comp (f := fun A : Matrix (Fin n) (Fin n) R => (1 + skewPart σ (G.map ι) A).det) (h2 _ hAU) hdetc.continuousAt`. Establish `hic : ContinuousAt (fun A : Matrix (Fin n) (Fin n) R => (1 + skewPart σ (G.map ι) A)⁻¹) (t • S)`. Simplify using `only [Matrix.inv_def]`. Conclude with `hinvc.smul ((continuous_const.add hPc).matrix_adjugate.continuousAt)`.

Conclude with `ContinuousAt.const_smul ((continuous_const.sub hPc).continuousAt.mul hic) (ι (c lam))`. Establish `hmem` using `mem_closure_image hΨc hcl`. Rewrite `hmem` using `[hΨA]`. Use `closure_mono ?_ hmem` and prove the remaining obligations. Introduce and unpack `_ ⟨A, ⟨hAU', A₀, rfl⟩, rfl⟩`.

Establish `hPmap : skewPart σ (G.map ι) (A₀.map ι) = (skewPart c G A₀).map ι` using `by show A₀.map ι - (G.map ι * (A₀.map ι).map σ * (G.map ι)⁻¹)ᵀ = (A₀ - (G * A₀.map c * G⁻¹)ᵀ).map ι`. Rewrite using `[hmapc, map_inv' ι G hGu, ← Matrix.map_mul, ← Matrix.map_mul]`. Use extensionality with `i j`. Simplify using `only [Matrix.sub_apply, Matrix.map_apply, Matrix.transpose_apply, map_sub]`. Establish `eadd : ∀ M : Matrix (Fin n) (Fin n) K, (1 + M).map ι = 1 + M.map ι` using `fun M => by`.

Rewrite using `[Matrix.map_add ι (map_add ι), Matrix.map_one ι (map_zero ι) (map_one ι)]`. Establish `esub : ∀ M : Matrix (Fin n) (Fin n) K, (1 - M).map ι = 1 - M.map ι` using `fun M => by`. Rewrite using `[Matrix.map_sub ι (map_sub ι), Matrix.map_one ι (map_zero ι) (map_one ι)]`. Establish `hS₀u : IsUnit (1 + skewPart c G A₀).det`. Use `isUnit_iff_ne_zero.2 fun h0 => ?_` and prove the remaining obligations.

Establish `hU0 : IsUnit (1 + skewPart σ (G.map ι) (A₀.map ι)).det` using `hAU'`. Rewrite `hU0` using `[hPmap, ← eadd, hdetmap, h0, map_zero]`. Conclude with `not_isUnit_zero hU0`. Use `⟨c lam • ((1 - skewPart c G A₀) * (1 + skewPart c G A₀)⁻¹), ?_, ?_⟩` and prove the remaining obligations. Use `smul_preserves_form_of_mul_conj_eq_one c G (c lam) (by rw [hc, mul_comm, hlam]) _ ?_` and prove the remaining obligations.

Conclude with `cayley_preserves_form_of_skew c G (skewPart c G A₀) _ (skew_component_is_skew c hc G hG hGu A₀) (Matrix.mul_nonsing_inv _ hS₀u)`. Use `show ι (c lam) • ((1 - skewPart σ (G.map ι) (A₀.map ι)) * (1 + skewPart σ (G.map ι) (A₀.map ι))⁻¹) = (c lam • ((1 - skewPart c G A₀) * (1 + skewPart c G A₀)⁻¹)).map ι`. Rewrite using `[hPmap, map_smul'' ι (c lam), Matrix.map_mul, ← map_inv' ι _ hS₀u, esub, eadd]`.
-/
theorem mem_closure_unitary {K R : Type} [Field K] [CharZero K] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsArtinianRing R] [Nontrivial R] (ι : K →+* R) (c : K →+* K) (σ : R →+* R)
    (hσι : ∀ x, σ (ι x) = ι (c x)) (hc : ∀ x, c (c x) = x) (hne : ∃ z, c z ≠ z) (hσ : ∀ x, σ (σ x) = x)
    (hσc : Continuous σ) (hd : DenseRange ι) (h1 : IsOpen {x : R | IsUnit x})
    (h2 : ∀ x : R, IsUnit x → ContinuousAt Ring.inverse x) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) (hG : (G.map c)ᵀ = G) (hdet : G.det ≠ 0)
    (g : Matrix (Fin n) (Fin n) R) (hg : gᵀ * G.map ι * g.map σ = G.map ι) :
    g ∈ closure {m | ∃ γ : Matrix (Fin n) (Fin n) K, γᵀ * G * γ.map c = G ∧ m = γ.map ι} := by
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.2 hdet
  have hdetmap : ∀ M : Matrix (Fin n) (Fin n) K, (M.map ι).det = ι M.det := fun M => (RingHom.map_det ι M).symm
  have hG'u : IsUnit (G.map ι).det := by rw [hdetmap]; exact hGu.map ι
  have hmapc : ∀ M : Matrix (Fin n) (Fin n) K, (M.map ι).map σ = (M.map c).map ι := by
    intro M; ext i j; simp [hσι]
  obtain ⟨lam, hlam, hu⟩ := exists_norm_one_isUnit_det_one_add_smul ι c hc hne g
  have hlam' : ι lam * σ (ι lam) = 1 := by rw [hσι, ← map_mul, hlam, map_one]
  have hh : (ι lam • g)ᵀ * G.map ι * (ι lam • g).map σ = G.map ι := smul_preserves_form_of_mul_conj_eq_one σ (G.map ι) (ι lam) hlam' g hg
  have hV : (1 + ι lam • g)⁻¹ * (1 + ι lam • g) = 1 := Matrix.nonsing_inv_mul _ hu
  have hV' : (1 + ι lam • g) * (1 + ι lam • g)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h2K : (2 : K) ≠ 0 := two_ne_zero
  have ht : 2 * ι (2⁻¹ : K) = 1 := by rw [← map_ofNat ι 2, ← map_mul, mul_inv_cancel₀ h2K, map_one]
  have hσt : σ (ι (2⁻¹ : K)) = ι (2⁻¹ : K) := by rw [hσι, map_inv₀, map_ofNat]
  obtain ⟨hskew, hinvS, hcay⟩ := cayley_skew_and_inverse_of_preserves_form σ (G.map ι) (ι lam • g) _ (ι (2⁻¹ : K)) ht hh hV hV'
  set S := (1 - ι lam • g) * (1 + ι lam • g)⁻¹ with hSdef
  set t : R := ι (2⁻¹ : K) with htdef
  have hSu : IsUnit (1 + S).det := Matrix.isUnit_det_of_right_inverse hinvS
  have hSinv : (1 + S)⁻¹ = t • (1 + ι lam • g) := Matrix.inv_eq_right_inv hinvS
  have hPS : skewPart σ (G.map ι) (t • S) = S := by
    rw [skewPart_smul σ (G.map ι) t hσt S, skew_component_eq_add_self_of_skew σ (G.map ι) S hskew hG'u, smul_add, ← add_smul,
      ← two_mul, ht, one_smul]
  set Ψ : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R := fun A =>
    ι (c lam) • ((1 - skewPart σ (G.map ι) A) * (1 + skewPart σ (G.map ι) A)⁻¹) with hΨ
  have hΨA : Ψ (t • S) = g := by
    show ι (c lam) • ((1 - skewPart σ (G.map ι) (t • S)) * (1 + skewPart σ (G.map ι) (t • S))⁻¹) = g
    rw [hPS, hSinv, hcay, smul_smul, ← map_mul, mul_comm, hlam, map_one, one_smul]
  have hPc : Continuous (fun A : Matrix (Fin n) (Fin n) R => skewPart σ (G.map ι) A) := by
    show Continuous (fun A : Matrix (Fin n) (Fin n) R => A - (G.map ι * A.map σ * (G.map ι)⁻¹)ᵀ)
    exact continuous_id.sub (((continuous_const.matrix_mul (continuous_id.matrix_map hσc)).matrix_mul
      continuous_const).matrix_transpose)
  have hdetc : Continuous (fun A : Matrix (Fin n) (Fin n) R => (1 + skewPart σ (G.map ι) A).det) :=
    (continuous_const.add hPc).matrix_det
  set U := {A : Matrix (Fin n) (Fin n) R | IsUnit (1 + skewPart σ (G.map ι) A).det} with hUdef
  have hU : IsOpen U := hdetc.isOpen_preimage _ h1
  have hAU : t • S ∈ U := by
    show IsUnit (1 + skewPart σ (G.map ι) (t • S)).det
    rw [hPS]; exact hSu
  have hdense : DenseRange (fun A : Matrix (Fin n) (Fin n) K => A.map ι) :=
    DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hd))
  have hcl : t • S ∈ closure (U ∩ Set.range (fun A : Matrix (Fin n) (Fin n) K => A.map ι)) :=
    Dense.open_subset_closure_inter hdense hU hAU
  have hΨc : ContinuousAt Ψ (t • S) := by
    have hinvc : ContinuousAt (fun A : Matrix (Fin n) (Fin n) R =>
        Ring.inverse (1 + skewPart σ (G.map ι) A).det) (t • S) :=
      ContinuousAt.comp (f := fun A : Matrix (Fin n) (Fin n) R => (1 + skewPart σ (G.map ι) A).det)
        (h2 _ hAU) hdetc.continuousAt
    have hic : ContinuousAt (fun A : Matrix (Fin n) (Fin n) R => (1 + skewPart σ (G.map ι) A)⁻¹) (t • S) := by
      simp only [Matrix.inv_def]
      exact hinvc.smul ((continuous_const.add hPc).matrix_adjugate.continuousAt)
    exact ContinuousAt.const_smul ((continuous_const.sub hPc).continuousAt.mul hic) (ι (c lam))
  have hmem := mem_closure_image hΨc hcl
  rw [hΨA] at hmem
  refine closure_mono ?_ hmem
  rintro _ ⟨A, ⟨hAU', A₀, rfl⟩, rfl⟩
  have hPmap : skewPart σ (G.map ι) (A₀.map ι) = (skewPart c G A₀).map ι := by
    show A₀.map ι - (G.map ι * (A₀.map ι).map σ * (G.map ι)⁻¹)ᵀ = (A₀ - (G * A₀.map c * G⁻¹)ᵀ).map ι
    rw [hmapc, map_inv' ι G hGu, ← Matrix.map_mul, ← Matrix.map_mul]
    ext i j
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.transpose_apply, map_sub]
  have eadd : ∀ M : Matrix (Fin n) (Fin n) K, (1 + M).map ι = 1 + M.map ι := fun M => by
    rw [Matrix.map_add ι (map_add ι), Matrix.map_one ι (map_zero ι) (map_one ι)]
  have esub : ∀ M : Matrix (Fin n) (Fin n) K, (1 - M).map ι = 1 - M.map ι := fun M => by
    rw [Matrix.map_sub ι (map_sub ι), Matrix.map_one ι (map_zero ι) (map_one ι)]
  have hS₀u : IsUnit (1 + skewPart c G A₀).det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have hU0 : IsUnit (1 + skewPart σ (G.map ι) (A₀.map ι)).det := hAU'
    rw [hPmap, ← eadd, hdetmap, h0, map_zero] at hU0
    exact not_isUnit_zero hU0
  refine ⟨c lam • ((1 - skewPart c G A₀) * (1 + skewPart c G A₀)⁻¹), ?_, ?_⟩
  · refine smul_preserves_form_of_mul_conj_eq_one c G (c lam) (by rw [hc, mul_comm, hlam]) _ ?_
    exact cayley_preserves_form_of_skew c G (skewPart c G A₀) _ (skew_component_is_skew c hc G hG hGu A₀) (Matrix.mul_nonsing_inv _ hS₀u)
  · show ι (c lam) • ((1 - skewPart σ (G.map ι) (A₀.map ι)) * (1 + skewPart σ (G.map ι) (A₀.map ι))⁻¹) =
      (c lam • ((1 - skewPart c G A₀) * (1 + skewPart c G A₀)⁻¹)).map ι
    rw [hPmap, map_smul'' ι (c lam), Matrix.map_mul, ← map_inv' ι _ hS₀u, esub, eadd]

open Formalism.UG in

/- English proof (translation)
Establish `hJu : IsUnit J.det` using `isUnit_iff_ne_zero.2 hdet`. Establish `hcT : ∀ {A : Type} [CommRing A] (τ : A →+* A) (M : Matrix (Fin n) (Fin n) A), cT τ M = (M.map τ)ᵀ` using `fun _ _ => rfl`. Establish `hJ2 : (J.map c)ᵀ = J` using `by rw [← hcT]; exact hJ`. Establish `hJ'u : IsUnit (J.map ι).det`. Establish `e : (J.map ι).det = ι J.det` using `(RingHom.map_det ι J).symm`.

Rewrite using `[e]`. Conclude with `hJu.map ι`. Establish `hmapc : ∀ M : Matrix (Fin n) (Fin n) K, (M.map ι).map σ = (M.map c).map ι`. Introduce `M`. Use extensionality with `i j`.

Simplify using `[hσι]`. Establish `hinv : ∀ u : GL (Fin n) R, cT σ (u : Matrix (Fin n) (Fin n) R) * J.map ι * u = J.map ι → ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = (J.map ι)⁻¹ * ((u : Matrix (Fin n) (Fin n) R).map σ)ᵀ * J.map ι`. Introduce `u hu`. Apply `Units.inv_eq_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← hcT]`.

Combine the equalities or inequalities in the displayed calculation. Set `F : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R × (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ` to `fun M => (M, MulOpposite.op ((J.map ι)⁻¹ * (M.map σ)ᵀ * J.map ι))`. Establish `hFc : Continuous F` using `continuous_id.prodMk (MulOpposite.continuous_op.comp ((continuous_const.matrix_mul (continuous_id.matrix_map hσc).matrix_transpose).matrix_mul continuous_const))`. Set `ψ : UJ σ (J.map ι) → Matrix (Fin n) (Fin n) R × (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ` to `fun x => Units.embedProduct _ x.1`. Establish `hψ : Topology.IsInducing ψ` using `Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal`.

Establish `hψF : ∀ x : UJ σ (J.map ι), ψ x = F ((x.1 : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)`. Introduce `x`. Establish `hx : cT σ ((x.1 : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * J.map ι * x.1 = J.map ι` using `x.2`. Use `show ((x.1 : Matrix (Fin n) (Fin n) R), MulOpposite.op ((x.1⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) = ((x.1 : Matrix (Fin n) (Fin n) R), MulOpposite.op ((J.map ι)⁻¹ * ((x.1 : Matrix (Fin n) (Fin n) R).map σ)ᵀ * J.map ι))`. Rewrite using `[hinv x.1 hx]`.

Rewrite using `[hψ.dense_iff]`. Introduce `x`. Rewrite using `[hψF]`. Establish `hx : cT σ ((x.1 : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * J.map ι * x.1 = J.map ι` using `x.2`. Rewrite `hx` using `[hcT]`.

Establish `eT : (Jᵀ).map ι = (J.map ι)ᵀ` using `Matrix.transpose_map`. Establish `hg : ((x.1 : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ * (Jᵀ).map ι * ((x.1 : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map σ = (Jᵀ).map ι`. Use `congrArg Matrix.transpose hx` as an intermediate fact. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose] at this`. Rewrite using `[eT]`.

Simplify `this` using `only [mul_assoc]`. Establish `hG : ((Jᵀ).map c)ᵀ = Jᵀ` using `by rw [Matrix.transpose_map, hJ2]`. Establish `hdetT : (Jᵀ).det ≠ 0` using `by rwa [Matrix.det_transpose]`. Establish `hcl` using `mem_closure_unitary ι c σ hσι hc hne hσ hσc hd h1 h2 Jᵀ hG hdetT _ hg`. Use `closure_mono ?_ (mem_closure_image hFc.continuousAt hcl)` and prove the remaining obligations.

Introduce and unpack `_ ⟨m, ⟨γ, hγ, rfl⟩, rfl⟩`. Establish `hγ' : cT c γ * J * γ = J`. Rewrite using `[hcT]`. Use `congrArg Matrix.transpose hγ` as an intermediate fact. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose] at this`.

Simplify `this` using `only [mul_assoc]`. Establish `hγl : (J⁻¹ * cT c γ * J) * γ = 1`. Combine the equalities or inequalities in the displayed calculation. Set `γu : GL (Fin n) K` to `⟨γ, J⁻¹ * cT c γ * J, mul_eq_one_comm.1 hγl, hγl⟩`. Establish `hγmem : γu ∈ UJ c J` using `hγ'`.

Establish `hv : ((bc ι γu : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = γ.map ι` using `rfl`. Establish `hbmem : bc ι γu ∈ UJ σ (J.map ι)` using `by show cT σ ((bc ι γu : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * J.map ι * (bc ι γu : GL (Fin n) R) = J.map ι`. Rewrite using `[hv, hcT, hmapc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← hcT, hγ']`. Use `⟨⟨bc ι γu, hbmem⟩, Subgroup.mem_map_of_mem _ hγmem, ?_⟩` and prove the remaining obligations. Rewrite using `[hψF]`.

Both sides reduce to the same expression.
-/
theorem dense_unitary {K R : Type} [Field K] [CharZero K] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsArtinianRing R] [Nontrivial R] (ι : K →+* R) (c : K →+* K) (σ : R →+* R)
    (hσι : ∀ x, σ (ι x) = ι (c x)) (hc : ∀ x, c (c x) = x) (hne : ∃ z, c z ≠ z) (hσ : ∀ x, σ (σ x) = x)
    (hσc : Continuous σ) (hd : DenseRange ι) (h1 : IsOpen {x : R | IsUnit x})
    (h2 : ∀ x : R, IsUnit x → ContinuousAt Ring.inverse x) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) K) (hJ : cT c J = J) (hdet : J.det ≠ 0) :
    Dense {h : UJ σ (J.map ι) | h.1 ∈ (UJ c J).map (bc ι)} := by
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.2 hdet
  have hcT : ∀ {A : Type} [CommRing A] (τ : A →+* A) (M : Matrix (Fin n) (Fin n) A), cT τ M = (M.map τ)ᵀ :=
    fun _ _ => rfl
  have hJ2 : (J.map c)ᵀ = J := by rw [← hcT]; exact hJ
  have hJ'u : IsUnit (J.map ι).det := by
    have e : (J.map ι).det = ι J.det := (RingHom.map_det ι J).symm
    rw [e]; exact hJu.map ι
  have hmapc : ∀ M : Matrix (Fin n) (Fin n) K, (M.map ι).map σ = (M.map c).map ι := by
    intro M; ext i j; simp [hσι]
  have hinv : ∀ u : GL (Fin n) R, cT σ (u : Matrix (Fin n) (Fin n) R) * J.map ι * u = J.map ι →
      ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = (J.map ι)⁻¹ * ((u : Matrix (Fin n) (Fin n) R).map σ)ᵀ * J.map ι := by
    intro u hu
    apply Units.inv_eq_of_mul_eq_one_left
    rw [← hcT]
    calc (J.map ι)⁻¹ * cT σ (u : Matrix (Fin n) (Fin n) R) * J.map ι * u
        = (J.map ι)⁻¹ * (cT σ (u : Matrix (Fin n) (Fin n) R) * J.map ι * u) := by simp only [mul_assoc]
      _ = 1 := by rw [hu, Matrix.nonsing_inv_mul _ hJ'u]
  let F : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R × (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    fun M => (M, MulOpposite.op ((J.map ι)⁻¹ * (M.map σ)ᵀ * J.map ι))
  have hFc : Continuous F := continuous_id.prodMk (MulOpposite.continuous_op.comp
    ((continuous_const.matrix_mul (continuous_id.matrix_map hσc).matrix_transpose).matrix_mul continuous_const))
  let ψ : UJ σ (J.map ι) → Matrix (Fin n) (Fin n) R × (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    fun x => Units.embedProduct _ x.1
  have hψ : Topology.IsInducing ψ :=
    Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal
  have hψF : ∀ x : UJ σ (J.map ι), ψ x = F ((x.1 : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
    intro x
    have hx : cT σ ((x.1 : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * J.map ι * x.1 = J.map ι := x.2
    show ((x.1 : Matrix (Fin n) (Fin n) R), MulOpposite.op ((x.1⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) =
      ((x.1 : Matrix (Fin n) (Fin n) R), MulOpposite.op ((J.map ι)⁻¹ * ((x.1 : Matrix (Fin n) (Fin n) R).map σ)ᵀ * J.map ι))
    rw [hinv x.1 hx]
  rw [hψ.dense_iff]
  intro x
  rw [hψF]
  have hx : cT σ ((x.1 : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * J.map ι * x.1 = J.map ι := x.2
  rw [hcT] at hx
  have eT : (Jᵀ).map ι = (J.map ι)ᵀ := Matrix.transpose_map
  have hg : ((x.1 : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ * (Jᵀ).map ι *
      ((x.1 : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map σ = (Jᵀ).map ι := by
    have := congrArg Matrix.transpose hx
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at this
    rw [eT]; simpa only [mul_assoc] using this
  have hG : ((Jᵀ).map c)ᵀ = Jᵀ := by rw [Matrix.transpose_map, hJ2]
  have hdetT : (Jᵀ).det ≠ 0 := by rwa [Matrix.det_transpose]
  have hcl := mem_closure_unitary ι c σ hσι hc hne hσ hσc hd h1 h2 Jᵀ hG hdetT _ hg
  refine closure_mono ?_ (mem_closure_image hFc.continuousAt hcl)
  rintro _ ⟨m, ⟨γ, hγ, rfl⟩, rfl⟩
  have hγ' : cT c γ * J * γ = J := by
    rw [hcT]
    have := congrArg Matrix.transpose hγ
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at this
    simpa only [mul_assoc] using this
  have hγl : (J⁻¹ * cT c γ * J) * γ = 1 := by
    calc (J⁻¹ * cT c γ * J) * γ = J⁻¹ * (cT c γ * J * γ) := by simp only [mul_assoc]
      _ = 1 := by rw [hγ', Matrix.nonsing_inv_mul _ hJu]
  let γu : GL (Fin n) K := ⟨γ, J⁻¹ * cT c γ * J, mul_eq_one_comm.1 hγl, hγl⟩
  have hγmem : γu ∈ UJ c J := hγ'
  have hv : ((bc ι γu : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = γ.map ι := rfl
  have hbmem : bc ι γu ∈ UJ σ (J.map ι) := by
    show cT σ ((bc ι γu : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * J.map ι * (bc ι γu : GL (Fin n) R) = J.map ι
    rw [hv, hcT, hmapc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← hcT, hγ']
  refine ⟨⟨bc ι γu, hbmem⟩, Subgroup.mem_map_of_mem _ hγmem, ?_⟩
  rw [hψF]
  rfl

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in

/- English proof (translation)
Establish `: Module.Finite F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `: IsModuleTopology (Ainf F) (Ainf F ⊗[F] E)` using `⟨rfl⟩`. Establish `: IsTopologicalRing (Ainf F ⊗[F] E)` using `IsModuleTopology.isTopologicalRing (Ainf F) _`. Establish `: IsArtinianRing (Ainf F)` using `inferInstanceAs (IsArtinianRing ((v : InfinitePlace F) → v.Completion))`. Establish `: IsArtinianRing (Ainf F ⊗[F] E)` using `IsArtinianRing.of_finite (Ainf F) _`.

Set `b` to `Module.finBasis F E`. Set `bb` to `Algebra.TensorProduct.basis (Ainf F) b`. Establish `: Nonempty (Fin (Module.finrank F E))` using `⟨⟨0, Module.finrank_pos⟩⟩`. Establish `: Nontrivial (Ainf F ⊗[F] E)` using `bb.repr.toEquiv.nontrivial`. Establish `hunit : ∀ x : (v : InfinitePlace F) → v.Completion, IsUnit x ↔ ∀ v, x v ≠ 0` using `fun x => Pi.isUnit_iff.trans (forall_congr' fun v => isUnit_iff_ne_zero)`.

Establish `h1P : IsOpen {x : (v : InfinitePlace F) → v.Completion | IsUnit x}`. Establish `: {x : (v : InfinitePlace F) → v.Completion | IsUnit x} = ⋂ v, (fun x : (w : InfinitePlace F) → w.Completion => x v) ⁻¹' {0}ᶜ`. Use extensionality with `x`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, hunit]`. Rewrite using `[this]`.

Conclude with `isOpen_iInter_of_finite fun v => isOpen_compl_singleton.preimage (continuous_apply v)`. Establish `h2P : ∀ x : (v : InfinitePlace F) → v.Completion, IsUnit x → ContinuousAt Ring.inverse x`. Introduce `x hx`. Establish `hx'` using `(hunit x).1 hx`. Establish `heq : (fun y : (v : InfinitePlace F) → v.Completion => fun v => (y v)⁻¹) =ᶠ[nhds x] Ring.inverse` using `by filter_upwards [h1P.mem_nhds hx] with y hy`.

Establish `hy'` using `(hunit y).1 hy`. Establish `hm : y * (fun v => (y v)⁻¹) = 1`. Use function extensionality and compare the values at `v`. Conclude with `mul_inv_cancel₀ (hy' v)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Ring.inverse_mul_cancel y hy, one_mul]`. Use `_ = Ring.inverse y := by rw [mul_assoc, hm, mul_one]`. Use `ContinuousAt.congr ?_ heq` and prove the remaining obligations. Conclude with `continuousAt_pi.2 fun v => ((continuous_apply v).continuousAt).inv₀ (hx' v)`. Establish `h1A : IsOpen {x : Ainf F | IsUnit x}` using `h1P`.

Establish `h2A : ∀ x : Ainf F, IsUnit x → ContinuousAt Ring.inverse x` using `h2P`. Take `⟨h1, h2⟩` from `units_of_free (A := Ainf F) (R := Ainf F ⊗[F] E) bb h1A h2A`. Establish `hσι : ∀ x, sigR (Ainf F) σ (inclR (Ainf F) x) = inclR (Ainf F) ((σ : E →+* E) x)`. Introduce `x`. Simplify using `[sigR, inclR]`.

Establish `hσσ : ∀ x : Ainf F ⊗[F] E, sigR (Ainf F) σ (sigR (Ainf F) σ x) = x`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [sigR, hc]`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `hσc : Continuous (sigR (Ainf F) σ)`. Establish `hL` using `IsModuleTopology.continuous_of_linearMap (R := Ainf F) (TensorProduct.AlgebraTensorModule.map (LinearMap.id : Ainf F →ₗ[Ainf F] Ainf F) σ.toLinearMap : Ainf F ⊗[F] E →ₗ[Ainf F] Ainf F ⊗[F] E)`. Use `hL using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [sigR]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `hd : DenseRange (inclR (F` using `F) (E := E) (Ainf F)) := by`.

Establish `hg : DenseRange (fun c : Fin (Module.finrank F E) → F => fun i => algebraMap F (Ainf F) (c i))` using `DenseRange.piMap fun _ => InfiniteAdeleRing.denseRange_algebraMap F`. Establish `hf : DenseRange (fun c : Fin (Module.finrank F E) → Ainf F => ∑ i, c i • bb i)`. Use `Function.Surjective.denseRange fun y => ⟨bb.equivFun y, ?_⟩` and prove the remaining obligations. Conclude with `bb.sum_equivFun y`. Establish `hfc : Continuous (fun c : Fin (Module.finrank F E) → Ainf F => ∑ i, c i • bb i)` using `continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const`.

Use `(hf.comp hg hfc).mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, rfl⟩`. Use `⟨∑ i, c i • b i, ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp_apply, map_sum, algebraMap_smul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `[inclR, bb, Algebra.TensorProduct.basis_apply]`. Conclude with `dense_unitary (K := E) (R := Ainf F ⊗[F] E) (inclR (Ainf F)) (σ : E →+* E) (sigR (Ainf F) σ) hσι (fun x => hc x) hne hσσ hσc hd h1 h2 J hJ hdet`.
-/
theorem dense_inf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hc : ∀ x, σ (σ x) = x) (hne : ∃ z, σ z ≠ z) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : Formalism.UG.cT (σ : E →+* E) J = J) (hdet : J.det ≠ 0) :
    Dense {h : HA (Ainf F) σ J | HA.mat (Ainf F) σ J h ∈ HFin (Ainf F) σ J} := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _
  have : IsArtinianRing (Ainf F) :=
    inferInstanceAs (IsArtinianRing ((v : InfinitePlace F) → v.Completion))
  have : IsArtinianRing (Ainf F ⊗[F] E) := IsArtinianRing.of_finite (Ainf F) _

  let b := Module.finBasis F E
  let bb := Algebra.TensorProduct.basis (Ainf F) b
  have : Nonempty (Fin (Module.finrank F E)) := ⟨⟨0, Module.finrank_pos⟩⟩
  have : Nontrivial (Ainf F ⊗[F] E) := bb.repr.toEquiv.nontrivial

  have hunit : ∀ x : (v : InfinitePlace F) → v.Completion, IsUnit x ↔ ∀ v, x v ≠ 0 := fun x =>
    Pi.isUnit_iff.trans (forall_congr' fun v => isUnit_iff_ne_zero)
  have h1P : IsOpen {x : (v : InfinitePlace F) → v.Completion | IsUnit x} := by
    have : {x : (v : InfinitePlace F) → v.Completion | IsUnit x} =
        ⋂ v, (fun x : (w : InfinitePlace F) → w.Completion => x v) ⁻¹' {0}ᶜ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff, hunit]
    rw [this]
    exact isOpen_iInter_of_finite fun v => isOpen_compl_singleton.preimage (continuous_apply v)
  have h2P : ∀ x : (v : InfinitePlace F) → v.Completion, IsUnit x → ContinuousAt Ring.inverse x := by
    intro x hx
    have hx' := (hunit x).1 hx
    have heq : (fun y : (v : InfinitePlace F) → v.Completion => fun v => (y v)⁻¹) =ᶠ[nhds x]
        Ring.inverse := by
      filter_upwards [h1P.mem_nhds hx] with y hy
      have hy' := (hunit y).1 hy
      have hm : y * (fun v => (y v)⁻¹) = 1 := by
        funext v; exact mul_inv_cancel₀ (hy' v)
      calc (fun v => (y v)⁻¹) = (Ring.inverse y * y) * (fun v => (y v)⁻¹) := by
            rw [Ring.inverse_mul_cancel y hy, one_mul]
        _ = Ring.inverse y := by rw [mul_assoc, hm, mul_one]
    refine ContinuousAt.congr ?_ heq
    exact continuousAt_pi.2 fun v => ((continuous_apply v).continuousAt).inv₀ (hx' v)
  have h1A : IsOpen {x : Ainf F | IsUnit x} := h1P
  have h2A : ∀ x : Ainf F, IsUnit x → ContinuousAt Ring.inverse x := h2P
  obtain ⟨h1, h2⟩ := units_of_free (A := Ainf F) (R := Ainf F ⊗[F] E) bb h1A h2A

  have hσι : ∀ x, sigR (Ainf F) σ (inclR (Ainf F) x) = inclR (Ainf F) ((σ : E →+* E) x) := by
    intro x; simp [sigR, inclR]
  have hσσ : ∀ x : Ainf F ⊗[F] E, sigR (Ainf F) σ (sigR (Ainf F) σ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR, hc]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hσc : Continuous (sigR (Ainf F) σ) := by
    have hL := IsModuleTopology.continuous_of_linearMap (R := Ainf F)
      (TensorProduct.AlgebraTensorModule.map (LinearMap.id : Ainf F →ₗ[Ainf F] Ainf F) σ.toLinearMap :
        Ainf F ⊗[F] E →ₗ[Ainf F] Ainf F ⊗[F] E)
    convert hL using 1
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hd : DenseRange (inclR (F := F) (E := E) (Ainf F)) := by
    have hg : DenseRange (fun c : Fin (Module.finrank F E) → F => fun i => algebraMap F (Ainf F) (c i)) :=
      DenseRange.piMap fun _ => InfiniteAdeleRing.denseRange_algebraMap F
    have hf : DenseRange (fun c : Fin (Module.finrank F E) → Ainf F => ∑ i, c i • bb i) := by
      refine Function.Surjective.denseRange fun y => ⟨bb.equivFun y, ?_⟩
      exact bb.sum_equivFun y
    have hfc : Continuous (fun c : Fin (Module.finrank F E) → Ainf F => ∑ i, c i • bb i) :=
      continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
    refine (hf.comp hg hfc).mono ?_
    rintro _ ⟨c, rfl⟩
    refine ⟨∑ i, c i • b i, ?_⟩
    simp only [Function.comp_apply, map_sum, algebraMap_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [inclR, bb, Algebra.TensorProduct.basis_apply]
  exact dense_unitary (K := E) (R := Ainf F ⊗[F] E) (inclR (Ainf F)) (σ : E →+* E) (sigR (Ainf F) σ)
    hσι (fun x => hc x) hne hσσ hσc hd h1 h2 J hJ hdet

/- English proof (translation)
Use `⟨(Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) E).trans ((Algebra.TensorProduct.prodRight F F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)).tr …` and prove the remaining obligations. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero, map_zero]`. Both sides reduce to the same expression.

Consider the case `tmul a e`. Simplify using `only [Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => simp only [map_add, hx, hy, Prod.mk_add_mk]`.
-/
private theorem exists_tensor_fst_snd_decomposition (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    ∃ Φ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E ≃ₐ[F] (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E) × (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E),
      ∀ z, Φ z = ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)) z, (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E)) z) := by
  refine ⟨(Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) E).trans
    ((Algebra.TensorProduct.prodRight F F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)).trans
      (AlgEquiv.prodCongr (Algebra.TensorProduct.comm F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F))
        (Algebra.TensorProduct.comm F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)))), ?_⟩
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | tmul a e =>
    simp only [Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy, Prod.mk_add_mk]

/- English proof (translation)
Apply the tactic sequence `constructor <;> simp [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]`.
-/
private theorem weak_approx_real_lemma_2 (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E) :
    (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)) (a • z) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F a • (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)) z ∧ (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E)) (a • z) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F a • (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E)) z := by
  constructor <;> simp [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]

/- English proof (translation)
Take `⟨Φ, hΦ⟩` from `exists_tensor_fst_snd_decomposition F E`. Use extensionality with `i j`. Apply `Φ.injective` to reduce the goal to its premises. Rewrite using `[hΦ, hΦ]`. Conclude with `Prod.ext (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)`.
-/
private theorem eq_of_map_fstA_eq_of_map_sndA_eq (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E)) (h1 : M.map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)) = N.map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)))
    (h2 : M.map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E)) = N.map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E))) : M = N := by
  obtain ⟨Φ, hΦ⟩ := exists_tensor_fst_snd_decomposition F E
  ext i j
  apply Φ.injective
  rw [hΦ, hΦ]
  exact Prod.ext (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

/- English proof (translation)
Establish `hfin : Module.Finite F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Use `IsModuleTopology.toContinuousSMul (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E)` as an intermediate fact. Use `IsModuleTopology.toContinuousAdd (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E)` as an intermediate fact. Set `bQ` to `Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) (Module.finBasis F E)`. Set `emb : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F` to `fun y => (y, 0)`.

Establish `hemb : Continuous emb` using `continuous_id.prodMk continuous_const`. Establish `key : ∀ x, Φ.symm (x, c) = (∑ i, emb (bQ.equivFun x i) • Φ.symm (bQ i, 0)) + Φ.symm (0, c)`. Introduce `x`. Apply `Φ.injective` to reduce the goal to its premises. Establish `hw : ∀ i, Φ (emb (bQ.equivFun x i) • Φ.symm (bQ i, 0)) = (bQ.equivFun x i • bQ i, 0)`.

Introduce `i`. Establish `h0` using `hΦ (Φ.symm (bQ i, 0))`. Rewrite `h0` using `[AlgEquiv.apply_symm_apply]`. Rewrite using `[hΦ, (weak_approx_real_lemma_2 F E _ _).1, (weak_approx_real_lemma_2 F E _ _).2, ← (Prod.mk.inj h0).1, ← (Prod.mk.inj h0).2]`. Conclude with `Prod.ext rfl (smul_zero _)`.

Rewrite using `[AlgEquiv.apply_symm_apply, map_add, map_sum, AlgEquiv.apply_symm_apply]`. Simplify using `only [hw]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `[Prod.fst_sum]`. Simplify using `[Prod.snd_sum]`.

Rewrite using `[show (fun x => Φ.symm (x, c)) = fun x => (∑ i, emb (bQ.equivFun x i) • Φ.symm (bQ i, 0)) + Φ.symm (0, c) from funext key]`. Establish `hcoord : Continuous fun x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E => bQ.equivFun x` using `IsModuleTopology.continuous_of_linearMap bQ.equivFun.toLinearMap`. Use `Continuous.add (continuous_finsetSum _ fun i _ => ?_) continuous_const` and prove the remaining obligations. Conclude with `Continuous.smul (f := fun x => emb (bQ.equivFun x i)) (g := fun _ => Φ.symm (bQ i, 0)) (hemb.comp ((continuous_apply i).comp hcoord)) continuous_const`.
-/
private theorem weak_approx_real_lemma_3 (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [TopologicalSpace (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E)] [IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E)]
    [TopologicalSpace (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E)] [IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E)]
    (Φ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E ≃ₐ[F] (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E) × (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E))
    (hΦ : ∀ z, Φ z = ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)) z, (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E)) z)) (c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :
    Continuous (fun x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E => Φ.symm (x, c)) := by
  have hfin : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have := IsModuleTopology.toContinuousSMul (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E)
  have := IsModuleTopology.toContinuousAdd (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E)
  let bQ := Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) (Module.finBasis F E)
  let emb : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F := fun y => (y, 0)
  have hemb : Continuous emb := continuous_id.prodMk continuous_const
  have key : ∀ x, Φ.symm (x, c) = (∑ i, emb (bQ.equivFun x i) • Φ.symm (bQ i, 0)) + Φ.symm (0, c) := by
    intro x
    apply Φ.injective
    have hw : ∀ i, Φ (emb (bQ.equivFun x i) • Φ.symm (bQ i, 0)) = (bQ.equivFun x i • bQ i, 0) := by
      intro i
      have h0 := hΦ (Φ.symm (bQ i, 0))
      rw [AlgEquiv.apply_symm_apply] at h0
      rw [hΦ, (weak_approx_real_lemma_2 F E _ _).1, (weak_approx_real_lemma_2 F E _ _).2,
        ← (Prod.mk.inj h0).1, ← (Prod.mk.inj h0).2]
      exact Prod.ext rfl (smul_zero _)
    rw [AlgEquiv.apply_symm_apply, map_add, map_sum, AlgEquiv.apply_symm_apply]
    simp only [hw]
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum]
  rw [show (fun x => Φ.symm (x, c)) = fun x => (∑ i, emb (bQ.equivFun x i) • Φ.symm (bQ i, 0)) +
      Φ.symm (0, c) from funext key]
  have hcoord : Continuous fun x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E => bQ.equivFun x :=
    IsModuleTopology.continuous_of_linearMap bQ.equivFun.toLinearMap
  refine Continuous.add (continuous_finsetSum _ fun i _ => ?_) continuous_const
  exact Continuous.smul (f := fun x => emb (bQ.equivFun x i)) (g := fun _ => Φ.symm (bQ i, 0))
    (hemb.comp ((continuous_apply i).comp hcoord)) continuous_const

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem sigR_transpose_mul_JR_mul_eq_JR (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x : GL (Fin n) (R ⊗[F] E)) :
    x ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR R σ J ↔
      Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) (x : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR R J *
        (x : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR R J := Iff.rfl

/- English proof (translation)
Establish `hsI : ∀ z, (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ z) = Formalism.MainNotions. …`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `hsF : ∀ z, (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E)) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ z) = Formalism.MainNotions. …`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, hsI]`.

Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, hsF]`. Use extensionality with `i j`. Simplify using `[Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]`. Use extensionality with `i j`.

Simplify using `[Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]`.
-/
private theorem weak_approx_real_lemma_7 (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (M : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E)) :
    ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)).toRingHom).mapMatrix (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ) M) = Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ) (((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)).toRingHom).mapMatrix M) ∧
    ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E)).toRingHom).mapMatrix (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ) M) = Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ) (((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E)).toRingHom).mapMatrix M) ∧
    ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)).toRingHom).mapMatrix (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) J) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) J ∧ ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E)).toRingHom).mapMatrix (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) J) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) J := by
  have hsI : ∀ z, (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ z) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hsF : ∀ z, (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E)) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ z) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E)) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j; simp [Formalism.UG.cT, hsI]
  · ext i j; simp [Formalism.UG.cT, hsF]
  · ext i j; simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
  · ext i j; simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

/- English proof (translation)
Establish `hg : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF …` using `(sigR_transpose_mul_JR_mul_eq_JR F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J _).1 (show (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J) from g).2`. Take `⟨h1, -, h3, -⟩` from `weak_approx_real_lemma_7 F E σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J g : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E))`. Establish `hmem : Units.map ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)).toRingHom).mapMatrix.toMonoidHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassV …`. Rewrite using `[sigR_transpose_mul_JR_mul_eq_JR]`. Use `show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ) (((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)).toRingHom).m …`.

Rewrite using `[← h1, ← h3, ← map_mul, ← map_mul, hg]`. Conclude with `⟨(⟨_, hmem⟩ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J), rfl⟩`.
-/
private theorem weak_approx_real_lemma_8 (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (g : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J) :
    ∃ p : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J, (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J p : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E)) = ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)).toRingHom).mapMatrix (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J g : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E)) := by
  have hg : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J g : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E)) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) J * (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J g : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E)) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) J :=
    (sigR_transpose_mul_JR_mul_eq_JR F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J _).1 (show (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J) from g).2
  obtain ⟨h1, -, h3, -⟩ := weak_approx_real_lemma_7 F E σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J g : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E))
  have hmem : Units.map ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)).toRingHom).mapMatrix.toMonoidHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J g) ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J := by
    rw [sigR_transpose_mul_JR_mul_eq_JR]
    show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ) (((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)).toRingHom).mapMatrix (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J g : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E))) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) J *
      ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)).toRingHom).mapMatrix (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J g : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E)) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) J
    rw [← h1, ← h3, ← map_mul, ← map_mul, hg]
  exact ⟨(⟨_, hmem⟩ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J), rfl⟩

/- English proof (translation)
Use `letI tQ : TopologicalSpace (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E) := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.topTens (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F)`. Use `letI tP : TopologicalSpace (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E) := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.topTens (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)`. Establish `iA : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E)` using `⟨rfl⟩`. Establish `iF : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E)` using `⟨rfl⟩`. Take `⟨Φ, hΦ⟩` from `exists_tensor_fst_snd_decomposition F E`.

Establish `hcont : ∀ c, Continuous fun x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E => Φ.symm (x, c)` using `fun c => weak_approx_real_lemma_3 F E Φ hΦ c`. Establish `hΦs : ∀ x y, ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)).toRingHom) (Φ.symm (x, y)) = x ∧ ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E)).toRingHom) …`. Introduce `x y`. Establish `h` using `hΦ (Φ.symm (x, y))`. Rewrite `h` using `[AlgEquiv.apply_symm_apply]`.

Conclude with `⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩`. Establish `hinj : ∀ M N : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E), ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)).toRingHom).mapMatrix M = ((Algebra.TensorProduct.map (For …` using `fun M N h1 h2 => eq_of_map_fstA_eq_of_map_sndA_eq F E M N h1 h2`. Establish `hcTI` using `fun M => (weak_approx_real_lemma_7 F E σ J M).1`. Establish `hcTF` using `fun M => (weak_approx_real_lemma_7 F E σ J M).2.1`. Establish `hJI` using `(weak_approx_real_lemma_7 F E σ J 0).2.2.1`.

Establish `hJF` using `(weak_approx_real_lemma_7 F E σ J 0).2.2.2`. Set `sec : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E) → Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) → Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolu …` to `fun X Y i j => Φ.symm (X i j, Y i j)`. Establish `hsecI : ∀ X Y, ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)).toRingHom).mapMatrix (sec X Y) = X`. Introduce `X Y`. Use extensionality with `i j`.

Conclude with `(hΦs _ _).1`. Establish `hsecF : ∀ X Y, ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E)).toRingHom).mapMatrix (sec X Y) = Y`. Introduce `X Y`. Use extensionality with `i j`. Conclude with `(hΦs _ _).2`.

Establish `hsecmul : ∀ X Y X' Y', sec X Y * sec X' Y' = sec (X * X') (Y * Y')`. Introduce `X Y X' Y'`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, hsecI, hsecI, hsecI]`. Rewrite using `[map_mul, hsecF, hsecF, hsecF]`.

Establish `hsec1 : sec 1 1 = 1`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_one, hsecI]`. Rewrite using `[map_one, hsecF]`. Establish `hone : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ) (1 : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) * Formalism.MainNotions. …`.

Simplify using `[Formalism.UG.cT]`. Establish `hsecmem : ∀ X : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E), Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ) X * Formalism.Ma …`. Introduce `X hX`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, (hcTI _), hJI, hsecI]`.

Conclude with `hX`. Rewrite using `[map_mul, map_mul, (hcTF _), hJF, hsecF]`. Conclude with `hone`. Establish `hmemI : ∀ x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J, Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVo …` using `fun x => (sigR_transpose_mul_JR_mul_eq_JR F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J _).1 (show (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J) from x).2`. Set `S : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J` to `fun x => (⟨⟨sec (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J x : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E)) 1, sec (↑(Formalism.MainN …`.

Establish `hmatc : Continuous fun x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J => (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassV …` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hmatc' : Continuous fun x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J => (↑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMa …` using `Units.continuous_coe_inv.comp continuous_subtype_val`. Establish `hS : Continuous S`. Use `Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _` and prove the remaining obligations. Conclude with `continuous_pi fun i => continuous_pi fun j => (hcont _).comp ((continuous_apply j).comp ((continuous_apply i).comp hmatc))`.

Conclude with `continuous_pi fun i => continuous_pi fun j => (hcont _).comp ((continuous_apply j).comp ((continuous_apply i).comp hmatc'))`. Conclude with `⟨S, hS, fun x => ⟨hsecI _ _, hsecF _ _⟩⟩`.
-/
private theorem weak_approx_real_lemma_9 (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) :
    ∃ S : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J, Continuous S ∧ ∀ x,
      ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)).toRingHom).mapMatrix (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J (S x) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E)) = (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J x : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E)) ∧ ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E)).toRingHom).mapMatrix (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J (S x) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E)) = 1 := by
  letI tQ : TopologicalSpace (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E) := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.topTens (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F)
  letI tP : TopologicalSpace (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E) := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.topTens (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)
  have iA : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E) := ⟨rfl⟩
  have iF : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨Φ, hΦ⟩ := exists_tensor_fst_snd_decomposition F E
  have hcont : ∀ c, Continuous fun x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E => Φ.symm (x, c) := fun c => weak_approx_real_lemma_3 F E Φ hΦ c
  have hΦs : ∀ x y, ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)).toRingHom) (Φ.symm (x, y)) = x ∧ ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E)).toRingHom) (Φ.symm (x, y)) = y := by
    intro x y
    have h := hΦ (Φ.symm (x, y))
    rw [AlgEquiv.apply_symm_apply] at h
    exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩
  have hinj : ∀ M N : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E), ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)).toRingHom).mapMatrix M = ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)).toRingHom).mapMatrix N →
      ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E)).toRingHom).mapMatrix M = ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E)).toRingHom).mapMatrix N → M = N :=
    fun M N h1 h2 => eq_of_map_fstA_eq_of_map_sndA_eq F E M N h1 h2
  have hcTI := fun M => (weak_approx_real_lemma_7 F E σ J M).1
  have hcTF := fun M => (weak_approx_real_lemma_7 F E σ J M).2.1
  have hJI := (weak_approx_real_lemma_7 F E σ J 0).2.2.1
  have hJF := (weak_approx_real_lemma_7 F E σ J 0).2.2.2
  let sec : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E) → Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) → Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E) := fun X Y i j => Φ.symm (X i j, Y i j)
  have hsecI : ∀ X Y, ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)).toRingHom).mapMatrix (sec X Y) = X := by
    intro X Y; ext i j; exact (hΦs _ _).1
  have hsecF : ∀ X Y, ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E)).toRingHom).mapMatrix (sec X Y) = Y := by
    intro X Y; ext i j; exact (hΦs _ _).2
  have hsecmul : ∀ X Y X' Y', sec X Y * sec X' Y' = sec (X * X') (Y * Y') := by
    intro X Y X' Y'
    apply hinj
    · rw [map_mul, hsecI, hsecI, hsecI]
    · rw [map_mul, hsecF, hsecF, hsecF]
  have hsec1 : sec 1 1 = 1 := by
    apply hinj
    · rw [map_one, hsecI]
    · rw [map_one, hsecF]
  have hone : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ) (1 : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) J * 1 = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) J := by
    simp [Formalism.UG.cT]
  have hsecmem : ∀ X : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E),
      Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ) X * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) J * X = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) J →
      Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ) (sec X 1) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) J * sec X 1 = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) J := by
    intro X hX
    apply hinj
    · rw [map_mul, map_mul, (hcTI _), hJI, hsecI]
      exact hX
    · rw [map_mul, map_mul, (hcTF _), hJF, hsecF]
      exact hone
  have hmemI : ∀ x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J,
      Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J x : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E)) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) J * (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J x : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E)) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) J :=
    fun x => (sigR_transpose_mul_JR_mul_eq_JR F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J _).1 (show (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J) from x).2
  let S : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J := fun x =>
    (⟨⟨sec (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J x : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E)) 1, sec (↑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J x)⁻¹) 1,
        by rw [hsecmul, Units.mul_inv, mul_one, hsec1], by rw [hsecmul, Units.inv_mul, mul_one, hsec1]⟩,
      (sigR_transpose_mul_JR_mul_eq_JR F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J _).2 (hsecmem _ (hmemI x))⟩ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J)
  have hmatc : Continuous fun x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J => (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J x : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  have hmatc' : Continuous fun x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J => (↑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) σ J x)⁻¹ : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E)) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  have hS : Continuous S := by
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · exact continuous_pi fun i => continuous_pi fun j =>
        (hcont _).comp ((continuous_apply j).comp ((continuous_apply i).comp hmatc))
    · exact continuous_pi fun i => continuous_pi fun j =>
        (hcont _).comp ((continuous_apply j).comp ((continuous_apply i).comp hmatc'))
  exact ⟨S, hS, fun x => ⟨hsecI _ _, hsecF _ _⟩⟩

/- English proof (translation)
Use `letI := D.host.cmStar`. Use `⟨fun x => star_star x, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `htop : (⊥ : Subalgebra D.host.F D.host.E) = ⊤`.

Use `eq_top_iff.2 fun a _ => ?_` and prove the remaining obligations. Take `⟨b, hb⟩` from `(D.sp.cm.fixed a).1 (hcon a)`. Conclude with `hb ▸ Subalgebra.algebraMap_mem _ b`. Establish `h1` using `Subalgebra.bot_eq_top_iff_finrank_eq_one.1 htop`. Rewrite `h1` using `[D.sp.cm.deg2]`.

Conclude with `absurd h1 (by norm_num)`.
-/
private theorem sig_involutive_and_nontrivial (D : Formalism.BasicNotions.D7) :
    (∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x) ∧ ∃ z, D.sp.cm.sig z ≠ z := by
  letI := D.host.cmStar
  refine ⟨fun x => star_star x, ?_⟩
  by_contra hcon
  push_neg at hcon
  have htop : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ := by
    refine eq_top_iff.2 fun a _ => ?_
    obtain ⟨b, hb⟩ := (D.sp.cm.fixed a).1 (hcon a)
    exact hb ▸ Subalgebra.algebraMap_mem _ b
  have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 htop
  rw [D.sp.cm.deg2] at h1
  exact absurd h1 (by norm_num)

/- English proof (translation)
Establish `h0 : Formalism.UG.cT (σ : E →+* E) (γ0 : Matrix (Fin n) (Fin n) E) * J * (γ0 : Matrix (Fin n) (Fin n) E) = J` using `hγ0`. Establish `hc : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F` using `F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)).mapMatrix (Formalism.UG.cT (σ : E →+* E) (γ0 : Matrix (Fin n) (Fin n) E)) = Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolu …`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]`. Establish `hmem : Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ0 ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.A …`.

Rewrite using `[sigR_transpose_mul_JR_mul_eq_JR]`. Use `show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ) ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassV …`. Rewrite using `[← hc, ← map_mul, ← map_mul, h0]`. Use `⟨(⟨_, hmem⟩ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J), ?_, ?_⟩` and prove the remaining obligations. Use `show Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ0 ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFin (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.A …`.

Conclude with `Subgroup.mem_map.2 ⟨γ0, hγ0, rfl⟩`. Use extensionality with `i j show (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)) ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ⊗ₜ[F] (γ0 : Matrix (Fin n) (Fin n) E) i j) = _`. Simplify using `[Formalism.UG.bc, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]`.
-/
private theorem exists_adelic_point_of_mem_unitaryGroup (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (γ0 : GL (Fin n) E) (hγ0 : γ0 ∈ Formalism.UG.UJ (σ : E →+* E) J) :
    ∃ γ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J, γ ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J ∧
      ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)).toRingHom).mapMatrix (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J γ : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E)) = ((Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F)) γ0 : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F ⊗[F] E)) := by
  have h0 : Formalism.UG.cT (σ : E →+* E) (γ0 : Matrix (Fin n) (Fin n) E) * J * (γ0 : Matrix (Fin n) (Fin n) E) = J := hγ0
  have hc : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)).mapMatrix (Formalism.UG.cT (σ : E →+* E) (γ0 : Matrix (Fin n) (Fin n) E)) =
      Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ) ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)).mapMatrix (γ0 : Matrix (Fin n) (Fin n) E)) := by
    ext i j; simp [Formalism.UG.cT, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
  have hmem : Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ0 ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J := by
    rw [sigR_transpose_mul_JR_mul_eq_JR]
    show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ) ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)).mapMatrix (γ0 : Matrix (Fin n) (Fin n) E)) *
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)).mapMatrix J * (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)).mapMatrix (γ0 : Matrix (Fin n) (Fin n) E) =
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)).mapMatrix J
    rw [← hc, ← map_mul, ← map_mul, h0]
  refine ⟨(⟨_, hmem⟩ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J), ?_, ?_⟩
  · show Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ0 ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFin (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J
    exact Subgroup.mem_map.2 ⟨γ0, hγ0, rfl⟩
  · ext i j
    show (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E)) ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ⊗ₜ[F] (γ0 : Matrix (Fin n) (Fin n) E) i j) = _
    simp [Formalism.UG.bc, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D V u hu U hU huU`. Take `⟨hinv, hne⟩` from `sig_involutive_and_nontrivial D`. Take `⟨S, hS, hSI⟩` from `weak_approx_real_lemma_9 D.host.F D.host.E D.sp.cm.sig V.gram`. Take `⟨p, hp⟩` from `weak_approx_real_lemma_8 D.host.F D.host.E D.sp.cm.sig V.gram u`. Establish `huF : ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom).mapMatrix (HA.mat (AF D.host.F) D.sp.cm.sig V.gram u : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) = 1`.

Establish `h` using `congrArg (fun y : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => (y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))) (MonoidHom.mem_ke …`. Conclude with `h`. Establish `hSp : S p = u` using `GlobalTheory.AutFunCounterexample.GA_ext V (eq_of_map_fstA_eq_of_map_sndA_eq _ _ _ _ ((hSI p).1.trans hp) ((hSI p).2.trans huF.symm))`. Establish `hdense` using `dense_inf D.host.F D.host.E D.sp.cm.sig hinv hne V.gram (GlobalTheory.AutFunCounterexample.gram_herm V) (GlobalTheory.AutFunCounterexample.gram_det_ne V)`. Take `⟨h, hhD, hhO⟩` from `hdense.exists_mem_open (hU.preimage hS) ⟨p, show S p ∈ U by rw [hSp]; exact huU⟩`.

Take `⟨γ0, hγ0, hγ0h⟩` from `Subgroup.mem_map.1 hhD`. Take `⟨γ, hγQ, hγI⟩` from `exists_adelic_point_of_mem_unitaryGroup D.host.F D.host.E D.sp.cm.sig V.gram γ0 hγ0`. Use `⟨γ, hγQ, γ⁻¹ * S h, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `MonoidHom.mem_ker.2` to reduce the goal to its premises. Rewrite using `[map_mul, map_inv, inv_mul_eq_one]`.

Apply `Units.ext` to reduce the goal to its premises. Use `show ((Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom).mapMatrix (HA.mat (AF D.host.F) D.sp.cm.sig V.gram γ : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) = ((Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F …`. Rewrite using `[hγI, hγ0h, (hSI h).1]`. Rewrite using `[mul_inv_cancel_left]`. Conclude with `hhO`.

Rewrite using `[mul_inv_cancel_left]`. Apply `MonoidHom.mem_ker.2` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `(hSI h).2`.
-/
theorem weak_approx_real : ∀ {D : D7} (V : HSp D) (u : GA D V), u ∈ GinfC V → ∀ U : Set (GA D V), IsOpen U → u ∈ U → ∃ γ ∈ GQ V, ∃ k ∈ GfC V, γ * k ∈ U ∧ γ * k ∈ GinfC V := by
  intro D V u hu U hU huU
  obtain ⟨hinv, hne⟩ := sig_involutive_and_nontrivial D
  obtain ⟨S, hS, hSI⟩ := weak_approx_real_lemma_9 D.host.F D.host.E D.sp.cm.sig V.gram
  obtain ⟨p, hp⟩ := weak_approx_real_lemma_8 D.host.F D.host.E D.sp.cm.sig V.gram u
  have huF : ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom).mapMatrix (HA.mat (AF D.host.F) D.sp.cm.sig V.gram u : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) = 1 := by
    have h := congrArg (fun y : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) =>
      (y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))) (MonoidHom.mem_ker.1 hu)
    exact h
  have hSp : S p = u := GlobalTheory.AutFunCounterexample.GA_ext V
    (eq_of_map_fstA_eq_of_map_sndA_eq _ _ _ _ ((hSI p).1.trans hp) ((hSI p).2.trans huF.symm))
  have hdense := dense_inf D.host.F D.host.E D.sp.cm.sig hinv hne V.gram (GlobalTheory.AutFunCounterexample.gram_herm V)
    (GlobalTheory.AutFunCounterexample.gram_det_ne V)
  obtain ⟨h, hhD, hhO⟩ := hdense.exists_mem_open (hU.preimage hS) ⟨p, show S p ∈ U by rw [hSp]; exact huU⟩
  obtain ⟨γ0, hγ0, hγ0h⟩ := Subgroup.mem_map.1 hhD
  obtain ⟨γ, hγQ, hγI⟩ := exists_adelic_point_of_mem_unitaryGroup D.host.F D.host.E D.sp.cm.sig V.gram γ0 hγ0
  refine ⟨γ, hγQ, γ⁻¹ * S h, ?_, ?_, ?_⟩
  · apply MonoidHom.mem_ker.2
    rw [map_mul, map_inv, inv_mul_eq_one]
    apply Units.ext
    show ((Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom).mapMatrix (HA.mat (AF D.host.F) D.sp.cm.sig V.gram γ : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) =
      ((Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom).mapMatrix (HA.mat (AF D.host.F) D.sp.cm.sig V.gram (S h) : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E))
    rw [hγI, hγ0h, (hSI h).1]
  · rw [mul_inv_cancel_left]
    exact hhO
  · rw [mul_inv_cancel_left]
    apply MonoidHom.mem_ker.2
    apply Units.ext
    exact (hSI h).2

end GlobalTheory.RealApprox
