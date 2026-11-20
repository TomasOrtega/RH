import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVecModel

section Conj

variable {n : ℕ} {J P G : Matrix (Fin n) (Fin n) ℂ}

/- English proof (translation)
Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem conj_cancel (hP : IsUnit P) (g : Matrix (Fin n) (Fin n) ℂ) : P * (P⁻¹ * g * P) * P⁻¹ = g := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h1]; simp

/- English proof (translation)
Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hG]`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]`. Use `_ = 0 := by rw [hX]; simp`.
-/
theorem lie_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * G + G * X = 0) :
    (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹)
      = (P * X * P⁻¹)ᴴ * J * (P * P⁻¹) + (P * P⁻¹)ᴴ * J * (P * X * P⁻¹) := by rw [h1]; simp
    _ = (P⁻¹)ᴴ * (Xᴴ * G + G * X) * P⁻¹ := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hX]; simp

/- English proof (translation)
Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hG]`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]`. Use `_ = 0 := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hX]; simp`.
-/
theorem lie_conj_inv (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * J + J * X = 0) :
    (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P)
      = Pᴴ * (Xᴴ * ((P * P⁻¹)ᴴ * J) + J * (P * P⁻¹) * X) * P := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hX]; simp

/- English proof (translation)
Rewrite using `[← Matrix.exp_conj _ _ hP, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem exp_smul_conj (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P * X * P⁻¹)) = P * NormedSpace.exp (t • X) * P⁻¹ := by
  rw [← Matrix.exp_conj _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Rewrite using `[← Matrix.exp_conj' _ _ hP, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem exp_smul_conj_inv (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P⁻¹ * X * P)) = P⁻¹ * NormedSpace.exp (t • X) * P := by
  rw [← Matrix.exp_conj' _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)`. Establish `h2 : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)`. Proceed by induction on `l with`. Consider the case `nil => simp [h2]`. Consider the case `cons a l ih`.

Rewrite using `[List.map_cons, List.prod_cons, List.prod_cons, ih]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem prod_conj_inv (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun g => P⁻¹ * g * P).prod = P⁻¹ * l.prod * P := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  induction l with
  | nil => simp [h2]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc P⁻¹ * a * P * (P⁻¹ * l.prod * P) = P⁻¹ * a * (P * P⁻¹) * l.prod * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]

/- English proof (translation)
Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)`. Proceed by induction on `l with`. Consider the case `nil => simp [h1]`. Consider the case `cons a l ih`. Rewrite using `[List.map_cons, List.prod_cons, List.prod_cons, ih]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)]`. Simplify using `only [Matrix.mul_assoc, Matrix.one_mul]`.
-/
theorem prod_conj (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun g => P * g * P⁻¹).prod = P * l.prod * P⁻¹ := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  induction l with
  | nil => simp [h1]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc P * a * P⁻¹ * (P * l.prod * P⁻¹) = P * a * (P⁻¹ * P) * l.prod * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)]
        simp only [Matrix.mul_assoc, Matrix.one_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

/- English proof (translation)
Introduce `k Xs hXs`. Establish `h` using `hw k (fun i => P⁻¹ * Xs i * P) fun i => lie_conj_inv hP hG (hXs i)`. Establish `e : ∀ t : Fin k → ℝ, P * (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))).prod * P⁻¹ = (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod`. Introduce `t`. Establish `: (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))) = (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P⁻¹ * g * P`.

Rewrite using `[List.map_ofFn]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `exp_smul_conj_inv hP _ _`. Rewrite using `[this, prod_conj_inv hP, conj_cancel hP]`.

Simplify `h` using `only [e]`.
-/
theorem smoothVec_of_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {w : H}
    (hw : SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w) :
    SmoothVec {X | Xᴴ * J + J * X = 0} σ w := by
  intro k Xs hXs
  have h := hw k (fun i => P⁻¹ * Xs i * P) fun i => lie_conj_inv hP hG (hXs i)
  have e : ∀ t : Fin k → ℝ, P * (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))).prod * P⁻¹ =
      (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod := by
    intro t
    have : (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))) =
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P⁻¹ * g * P := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact exp_smul_conj_inv hP _ _
    rw [this, prod_conj_inv hP, conj_cancel hP]
  simpa only [e] using h

/- English proof (translation)
Introduce `k Xs hXs`. Establish `h` using `hw k (fun i => P * Xs i * P⁻¹) fun i => lie_conj hP hG (hXs i)`. Establish `e : ∀ t : Fin k → ℝ, (List.ofFn fun i => NormedSpace.exp (t i • (P * Xs i * P⁻¹))).prod = P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹`. Introduce `t`. Establish `: (List.ofFn fun i => NormedSpace.exp (t i • (P * Xs i * P⁻¹))) = (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P * g * P⁻¹`.

Rewrite using `[List.map_ofFn]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `exp_smul_conj hP _ _`. Rewrite using `[this, prod_conj hP]`.

Simplify `h` using `only [e]`.
-/
theorem smoothVec_to_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {w : H}
    (hw : SmoothVec {X | Xᴴ * J + J * X = 0} σ w) :
    SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w := by
  intro k Xs hXs
  have h := hw k (fun i => P * Xs i * P⁻¹) fun i => lie_conj hP hG (hXs i)
  have e : ∀ t : Fin k → ℝ, (List.ofFn fun i => NormedSpace.exp (t i • (P * Xs i * P⁻¹))).prod =
      P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹ := by
    intro t
    have : (List.ofFn fun i => NormedSpace.exp (t i • (P * Xs i * P⁻¹))) =
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P * g * P⁻¹ := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact exp_smul_conj hP _ _
    rw [this, prod_conj hP]
  simpa only [e] using h

end Conj

/- English proof (translation)
Introduce `D V S M τ w`. Rewrite using `[GlobalTheory.SmVec.sm_eq M τ, GlobalTheory.SmVec.mem_smSub]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `smoothVec_of_conj (M.fr_unit τ) (M.fr_gram τ) h`.

Introduce `h`. Conclude with `smoothVec_to_conj (M.fr_unit τ) (M.fr_gram τ) h`.
-/
theorem mem_sm_iff : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (w : M.H τ),
    w ∈ M.sm τ ↔ SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w := by
  intro D V S M τ w
  rw [GlobalTheory.SmVec.sm_eq M τ, GlobalTheory.SmVec.mem_smSub]
  constructor
  · intro h
    exact smoothVec_of_conj (M.fr_unit τ) (M.fr_gram τ) h
  · intro h
    exact smoothVec_to_conj (M.fr_unit τ) (M.fr_gram τ) h

end GlobalTheory.SmVecModel
