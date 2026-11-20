import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopTermLem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists

noncomputable section

open scoped Classical
open MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.LocJEq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

/- English proof (translation)
Take `⟨-, h2, h3, -⟩` from `C.isT τ`. Establish `hm' : mᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS` using `hm`. Use `show (C.Q τ * m * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * m * C.Qi τ) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ))`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ := by`. Rewrite using `[h3, hm']`. Use `_ = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) := by`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by`.

Rewrite using `[h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem transp_mem (τ : D.what₂.Tau) {m : MatKR D.R.k D.R.rS} (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    C.Q τ * m * C.Qi τ ∈ UJset (X.B.I.ε (vOf X τ)) := by
  obtain ⟨-, h2, h3, -⟩ := C.isT τ
  have hm' : mᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm
  show (C.Q τ * m * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * m * C.Qi τ) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ))
  calc (C.Q τ * m * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * m * C.Qi τ)
      = (C.Qi τ)ᴴ * (mᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * m) * C.Qi τ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ := by
        rw [h3, hm']
    _ = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
        rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

def Smap (τ : D.what₂.Tau) (γ z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  Matrix.of.symm (C.Qi τ * umat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹)

/- English proof (translation)
Establish `hc : Continuous fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => umat (γ⁻¹ * z)` using `(Units.continuous_val.comp continuous_subtype_val).comp (continuous_const.mul continuous_id)`. Establish `h2 : Continuous fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => C.Qi τ * umat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹` using `((continuous_const.matrix_mul hc).matrix_mul continuous_const).matrix_mul continuous_const`. Conclude with `h2`.
-/
theorem smap_cont (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : Continuous (Smap C τ γ) := by
  have hc : Continuous fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => umat (γ⁻¹ * z) :=
    (Units.continuous_val.comp continuous_subtype_val).comp (continuous_const.mul continuous_id)
  have h2 : Continuous fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      C.Qi τ * umat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹ :=
    ((continuous_const.matrix_mul hc).matrix_mul continuous_const).matrix_mul continuous_const
  exact h2

/- English proof (translation)
Rewrite using `[(X.ds (vOf X τ)).2.2.1.1.2 a ha b hb]`. Both sides reduce to the same expression.
-/
theorem sig_mul (τ : D.what₂.Tau) {a b : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ} (ha : a ∈ UJset (X.B.I.ε (vOf X τ)))
    (hb : b ∈ UJset (X.B.I.ε (vOf X τ))) (x : X.B.H (vOf X τ)) :
    X.B.σ (vOf X τ) (a * b) x = X.B.σ (vOf X τ) a (X.B.σ (vOf X τ) b x) := by
  rw [(X.ds (vOf X τ)).2.2.1.1.2 a ha b hb]
  rfl

/- English proof (translation)
Rewrite using `[(X.ds (vOf X τ)).2.2.1.1.1]`. Both sides reduce to the same expression.
-/
theorem sig_one (τ : D.what₂.Tau) (x : X.B.H (vOf X τ)) : X.B.σ (vOf X τ) 1 x = x := by
  rw [(X.ds (vOf X τ)).2.2.1.1.1]
  rfl

/- English proof (translation)
The claim follows from `z.2`.
-/
theorem umat_mem (τ : D.what₂.Tau) (z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : umat z ∈ UJset (X.B.I.ε (vOf X τ)) := z.2

/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, (C.isT τ).2.1, Matrix.one_mul]`.
-/
theorem QQi_left (τ : D.what₂.Tau) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) : C.Q τ * (C.Qi τ * M) = M := by
  rw [← Matrix.mul_assoc, (C.isT τ).2.1, Matrix.one_mul]

variable (hB : WuBessel C)

/- English proof (translation)
The claim follows from `(hB u τ).choose_spec.2 z`.
-/
theorem wloc_eq (u : D.what₂.Word) (τ : D.what₂.Tau) (z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    X.Wloc u (vOf X τ) z = bOf hB u τ (X.B.σ (vOf X τ) (umat z) (X.B.w (vOf X τ))) :=
  (hB u τ).choose_spec.2 z

/- English proof (translation)
Take `⟨h1, h2, h3, -⟩` from `C.isT τ`. Use `set J := Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) with hJdef`. Establish `hy : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS` using `C.y_mem τ`. Establish `hJ : J * J = 1` using `by rw [hJdef, Formalism.REAL.Jm_mul_self]`. Establish `hK : (C.Qi τ * J * (C.Qi τ)ᴴ) * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS = 1`.

Rewrite using `[← h3]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = 1 := by`. Rewrite using `[h2, Matrix.conjTranspose_one, Matrix.one_mul, ← Matrix.mul_assoc J J, hJ, Matrix.one_mul, h1]`.

Use `Matrix.isUnit_det_of_left_inverse (B := C.Qi τ * J * (C.Qi τ)ᴴ * (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hy, hK]`.
-/
private theorem isUnit_det_y (τ : D.what₂.Tau) : IsUnit (C.y τ).det := by
  obtain ⟨h1, h2, h3, -⟩ := C.isT τ
  set J := Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) with hJdef
  have hy : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
  have hJ : J * J = 1 := by rw [hJdef, Formalism.REAL.Jm_mul_self]
  have hK : (C.Qi τ * J * (C.Qi τ)ᴴ) * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS = 1 := by
    rw [← h3]
    calc C.Qi τ * J * (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * J * C.Q τ)
        = C.Qi τ * (J * ((C.Q τ * C.Qi τ)ᴴ * (J * C.Q τ))) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, ← Matrix.mul_assoc J J, hJ, Matrix.one_mul, h1]
  refine Matrix.isUnit_det_of_left_inverse (B := C.Qi τ * J * (C.Qi τ)ᴴ * (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) ?_
  calc C.Qi τ * J * (C.Qi τ)ᴴ * (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ
      = (C.Qi τ * J * (C.Qi τ)ᴴ) * ((C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hy, hK]

/- English proof (translation)
Establish `hu` using `isUnit_det_y C τ`. Establish `hyi : (C.y τ)⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)`. Establish `hy : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS` using `C.y_mem τ`. Establish `e1 : C.y τ * (C.y τ)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hu`. Use `show ((C.y τ)⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ)⁻¹ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by`. Rewrite using `[e1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`. Use `⟨transp_mem C τ hyi, transp_mem C τ (C.y_mem τ), ?_⟩` and prove the remaining obligations.

Take `⟨h1, h2, -, -⟩` from `C.isT τ`. Establish `e2 : (C.y τ)⁻¹ * C.y τ = 1` using `Matrix.nonsing_inv_mul _ hu`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by`.

Rewrite using `[h1, Matrix.one_mul, ← Matrix.mul_assoc (C.y τ)⁻¹ (C.y τ), e2, Matrix.one_mul, h2]`.
-/
theorem y_facts (τ : D.what₂.Tau) :
    C.Q τ * (C.y τ)⁻¹ * C.Qi τ ∈ UJset (X.B.I.ε (vOf X τ)) ∧ C.Q τ * C.y τ * C.Qi τ ∈ UJset (X.B.I.ε (vOf X τ)) ∧
      (C.Q τ * (C.y τ)⁻¹ * C.Qi τ) * (C.Q τ * C.y τ * C.Qi τ) = 1 := by
  have hu := isUnit_det_y C τ
  have hyi : (C.y τ)⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
    have hy : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
    have e1 : C.y τ * (C.y τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    show ((C.y τ)⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ)⁻¹ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
    calc ((C.y τ)⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ)⁻¹
        = ((C.y τ)⁻¹)ᴴ * ((C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ) * (C.y τ)⁻¹ := by rw [hy]
      _ = (C.y τ * (C.y τ)⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ * (C.y τ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by
          rw [e1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  refine ⟨transp_mem C τ hyi, transp_mem C τ (C.y_mem τ), ?_⟩
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  have e2 : (C.y τ)⁻¹ * C.y τ = 1 := Matrix.nonsing_inv_mul _ hu
  calc C.Q τ * (C.y τ)⁻¹ * C.Qi τ * (C.Q τ * C.y τ * C.Qi τ)
      = C.Q τ * ((C.y τ)⁻¹ * ((C.Qi τ * C.Q τ) * (C.y τ * C.Qi τ))) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [h1, Matrix.one_mul, ← Matrix.mul_assoc (C.y τ)⁻¹ (C.y τ), e2, Matrix.one_mul, h2]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phi_def (u u' : D.what₂.Word) (τ : D.what₂.Tau) (m : MatKR D.R.k D.R.rS) :
    (locS hB u u' τ).Φ m = bOf hB u τ (X.B.σ (vOf X τ) (C.Q τ * m * C.Qi τ)
      (X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ)))) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phi'_def (u u' : D.what₂.Word) (τ : D.what₂.Tau) (m : MatKR D.R.k D.R.rS) :
    (locS hB u u' τ).Φ' m = sclOf hB u u' τ • bOf hB u' τ (X.B.σ (vOf X τ) (C.Q τ * m * C.Qi τ)
      (X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ)))) := rfl

/- English proof (translation)
Take `⟨hy1, hy2, hy3⟩` from `y_facts C τ`. Establish `hg : uMat γ * umat γ⁻¹ = 1` using `Units.mul_inv (γ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ)`. Establish `hg' : ∀ M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, uMat γ * (umat γ⁻¹ * M) = M` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, hg, Matrix.one_mul]`. Establish `hM : C.Q τ * (trG (C.Q τ) (C.Qi τ) γ * Matrix.of (Smap C τ γ z)) * C.Qi τ = umat z * (C.Q τ * (C.y τ)⁻¹ * C.Qi τ)`.

Rewrite using `[show Matrix.of (Smap C τ γ z) = C.Qi τ * (umat γ⁻¹ * umat z) * C.Q τ * (C.y τ)⁻¹ from rfl]`. Simplify using `only [trG, Matrix.mul_assoc, QQi_left C τ, hg']`. Establish `key : X.B.σ (vOf X τ) (C.Q τ * (trG (C.Q τ) (C.Qi τ) γ * Matrix.of (Smap C τ γ z)) * C.Qi τ) (X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ))) = X.B.σ (vOf X τ) (umat z) (X.B.w (vOf X τ))`. Rewrite using `[hM, sig_mul τ (umat_mem τ z) hy1, ← sig_mul τ hy1 hy2, hy3, sig_one τ]`. Rewrite using `[phi_def C hB u u' τ, wloc_eq C hB u τ z, key]`.
-/
theorem phi_S (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of (Smap C τ γ z)) = X.Wloc u (vOf X τ) z := by
  obtain ⟨hy1, hy2, hy3⟩ := y_facts C τ
  have hg : uMat γ * umat γ⁻¹ = 1 := Units.mul_inv (γ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ)
  have hg' : ∀ M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, uMat γ * (umat γ⁻¹ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hg, Matrix.one_mul]
  have hM : C.Q τ * (trG (C.Q τ) (C.Qi τ) γ * Matrix.of (Smap C τ γ z)) * C.Qi τ =
      umat z * (C.Q τ * (C.y τ)⁻¹ * C.Qi τ) := by
    rw [show Matrix.of (Smap C τ γ z) = C.Qi τ * (umat γ⁻¹ * umat z) * C.Q τ * (C.y τ)⁻¹ from rfl]
    simp only [trG, Matrix.mul_assoc, QQi_left C τ, hg']
  have key : X.B.σ (vOf X τ) (C.Q τ * (trG (C.Q τ) (C.Qi τ) γ * Matrix.of (Smap C τ γ z)) * C.Qi τ)
      (X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ))) =
      X.B.σ (vOf X τ) (umat z) (X.B.w (vOf X τ)) := by
    rw [hM, sig_mul τ (umat_mem τ z) hy1, ← sig_mul τ hy1 hy2, hy3, sig_one τ]
  rw [phi_def C hB u u' τ, wloc_eq C hB u τ z, key]

/- English proof (translation)
Take `⟨hy1, hy2, hy3⟩` from `y_facts C τ`. Establish `hM : C.Q τ * Matrix.of (Smap C τ γ z) * C.Qi τ = umat (γ⁻¹ * z) * (C.Q τ * (C.y τ)⁻¹ * C.Qi τ)`. Rewrite using `[show Matrix.of (Smap C τ γ z) = C.Qi τ * (umat γ⁻¹ * umat z) * C.Q τ * (C.y τ)⁻¹ from rfl]`. Use `show _ = (umat γ⁻¹ * umat z) * _`. Simplify using `only [Matrix.mul_assoc, QQi_left C τ]`.

Establish `key : X.B.σ (vOf X τ) (C.Q τ * Matrix.of (Smap C τ γ z) * C.Qi τ) (X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ))) = X.B.σ (vOf X τ) (umat (γ⁻¹ * z)) (X.B.w (vOf X τ))`. Rewrite using `[hM, sig_mul τ (umat_mem τ (γ⁻¹ * z)) hy1, ← sig_mul τ hy1 hy2, hy3, sig_one τ]`. Rewrite using `[phi'_def C hB u u' τ, wloc_eq C hB u' τ (γ⁻¹ * z), key]`.
-/
theorem phi'_S (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (locS hB u u' τ).Φ' (Matrix.of (Smap C τ γ z)) = sclOf hB u u' τ • X.Wloc u' (vOf X τ) (γ⁻¹ * z) := by
  obtain ⟨hy1, hy2, hy3⟩ := y_facts C τ
  have hM : C.Q τ * Matrix.of (Smap C τ γ z) * C.Qi τ = umat (γ⁻¹ * z) * (C.Q τ * (C.y τ)⁻¹ * C.Qi τ) := by
    rw [show Matrix.of (Smap C τ γ z) = C.Qi τ * (umat γ⁻¹ * umat z) * C.Q τ * (C.y τ)⁻¹ from rfl]
    show _ = (umat γ⁻¹ * umat z) * _
    simp only [Matrix.mul_assoc, QQi_left C τ]
  have key : X.B.σ (vOf X τ) (C.Q τ * Matrix.of (Smap C τ γ z) * C.Qi τ)
      (X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ))) =
      X.B.σ (vOf X τ) (umat (γ⁻¹ * z)) (X.B.w (vOf X τ)) := by
    rw [hM, sig_mul τ (umat_mem τ (γ⁻¹ * z)) hy1, ← sig_mul τ hy1 hy2, hy3, sig_one τ]
  rw [phi'_def C hB u u' τ, wloc_eq C hB u' τ (γ⁻¹ * z), key]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[Formalism.L2.SG.TermOp.rk1, inner_smul_left, hc, smul_smul]`.
-/
theorem smulRight_smul {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] (a : V) (b : V') (c : ℂ) (hc : (starRingEnd ℂ) c = c) :
    (innerSL ℂ (c • b)).smulRight a = c • Formalism.L2.SG.TermOp.rk1 a b := by
  ext x
  simp [Formalism.L2.SG.TermOp.rk1, inner_smul_left, hc, smul_smul]

/- English proof (translation)
Establish `hc : (starRingEnd ℂ) (sclOf hB u u' τ) = sclOf hB u u' τ`. Unfold `sclOf`. Conclude with `Complex.conj_ofReal _`. Establish `hpt : ∀ z, (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of (Smap C τ γ z)))).smulRight ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of (Smap C τ γ z))) = sclOf hB u u' τ • Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) z) (X.Wloc u' (vOf X τ) (γ⁻¹ * z))`. Introduce `z`.

Rewrite using `[phi_S C hB, phi'_S C hB]`. Conclude with `smulRight_smul _ _ _ hc`. Unfold `LocS.J ampJ Jv Formalism.L2.SG.TermOp.OO`. Rewrite using `[Measure.restrict_univ, integral_map (smap_cont C τ γ).measurable.aemeasurable hG, integral_congr_ae (ae_of_all _ hpt)]`. Use `erw [integral_smul, smul_smul]`.

Both sides reduce to the same expression.
-/
theorem locJ_map_eq (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))))
    (hG : AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of x))) (ν.map (Smap C τ γ))) :
    (locS hB u u' τ).J (ν.map (Smap C τ γ)) (trG (C.Q τ) (C.Qi τ) γ) =
      ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) •
        (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ)); Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) γ) := by
  have hc : (starRingEnd ℂ) (sclOf hB u u' τ) = sclOf hB u u' τ := by
    unfold sclOf; exact Complex.conj_ofReal _
  have hpt : ∀ z, (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of (Smap C τ γ z)))).smulRight
      ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of (Smap C τ γ z))) =
      sclOf hB u u' τ • Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) z) (X.Wloc u' (vOf X τ) (γ⁻¹ * z)) := by
    intro z
    rw [phi_S C hB, phi'_S C hB]
    exact smulRight_smul _ _ _ hc
  unfold LocS.J ampJ Jv Formalism.L2.SG.TermOp.OO
  rw [Measure.restrict_univ, integral_map (smap_cont C τ γ).measurable.aemeasurable hG,
    integral_congr_ae (ae_of_all _ hpt)]
  erw [integral_smul, smul_smul]
  rfl

def ujOf' {n : ℕ} {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M ∈ UJset ε) : Formalism.REAL.UJ ε :=
  ⟨⟨M, Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε, by
      have h : Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε * M = 1 := by
        have hM' : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε := hM
        rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM', Formalism.REAL.Jm_mul_self]
      rw [← Matrix.inv_eq_left_inv h]
      exact Matrix.mul_nonsing_inv M (Matrix.isUnit_det_of_left_inverse h), by
      have hM' : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε := hM
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM', Formalism.REAL.Jm_mul_self]⟩, hM⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem umat_ujOf' {n : ℕ} {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M ∈ UJset ε) :
    umat (ujOf' M hM) = M := rfl

/- English proof (translation)
The claim follows from `isUnit_det_y C τ`.
-/
theorem unit_det_y (τ : D.what₂.Tau) : IsUnit (C.y τ).det := isUnit_det_y C τ

/- English proof (translation)
Establish `hy : (C.y τ)⁻¹ * C.y τ = 1` using `Matrix.nonsing_inv_mul _ (unit_det_y C τ)`. Take `⟨-, h2, -, -⟩` from `C.isT τ`. Establish `hg : umat γ * umat γ⁻¹ = 1` using `Units.mul_inv (γ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = A := by`. Rewrite using `[h2, hy, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc (umat γ⁻¹ * A) (C.Q τ) (C.Qi τ), h2, Matrix.mul_one, ← Matrix.mul_assoc, hg, Matrix.one_mul]`.
-/
theorem back_smap (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) :
    umat γ * (C.Q τ * (C.Qi τ * (umat γ⁻¹ * A) * C.Q τ * (C.y τ)⁻¹) * C.y τ * C.Qi τ) = A := by
  have hy : (C.y τ)⁻¹ * C.y τ = 1 := Matrix.nonsing_inv_mul _ (unit_det_y C τ)
  obtain ⟨-, h2, -, -⟩ := C.isT τ
  have hg : umat γ * umat γ⁻¹ = 1 := Units.mul_inv (γ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ)
  calc umat γ * (C.Q τ * (C.Qi τ * (umat γ⁻¹ * A) * C.Q τ * (C.y τ)⁻¹) * C.y τ * C.Qi τ)
      = umat γ * ((C.Q τ * C.Qi τ) * (umat γ⁻¹ * A) * C.Q τ * ((C.y τ)⁻¹ * C.y τ) * C.Qi τ) := by
        simp only [Matrix.mul_assoc]
    _ = A := by
        rw [h2, hy, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc (umat γ⁻¹ * A) (C.Q τ) (C.Qi τ), h2,
          Matrix.mul_one, ← Matrix.mul_assoc, hg, Matrix.one_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem smap_val (τ : D.what₂.Tau) (γ z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix.of (Smap C τ γ z) = C.Qi τ * (umat γ⁻¹ * umat z) * C.Q τ * (C.y τ)⁻¹ := by
  rfl

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩ show umat γ * (C.Q τ * Matrix.of (Smap C τ γ z) * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ))`. Rewrite using `[smap_val C τ γ z, back_smap C τ γ (umat z)]`. Conclude with `umat_mem τ z`.

Introduce `hx`. Establish `hx' : umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ))` using `hx`. Use `⟨ujOf' _ hx', ?_⟩` and prove the remaining obligations. Apply `Matrix.of.injective` to reduce the goal to its premises. Rewrite using `[smap_val C τ γ (ujOf' _ hx'), umat_ujOf' _ hx']`.

Establish `hg : umat γ⁻¹ * umat γ = 1` using `Units.inv_mul (γ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ)`. Take `⟨h1, -, -, -⟩` from `C.isT τ`. Establish `hy : C.y τ * (C.y τ)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (unit_det_y C τ)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc (umat γ⁻¹) (umat γ), hg, Matrix.one_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Matrix.of x := by`. Rewrite using `[h1, Matrix.one_mul, Matrix.one_mul, hy, Matrix.mul_one]`.
-/
theorem range_smap (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Set.range (Smap C τ γ) =
      {x | umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ))} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    show umat γ * (C.Q τ * Matrix.of (Smap C τ γ z) * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ))
    rw [smap_val C τ γ z, back_smap C τ γ (umat z)]
    exact umat_mem τ z
  · intro hx
    have hx' : umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ)) := hx
    refine ⟨ujOf' _ hx', ?_⟩
    apply Matrix.of.injective
    rw [smap_val C τ γ (ujOf' _ hx'), umat_ujOf' _ hx']
    have hg : umat γ⁻¹ * umat γ = 1 := Units.inv_mul (γ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ)
    obtain ⟨h1, -, -, -⟩ := C.isT τ
    have hy : C.y τ * (C.y τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (unit_det_y C τ)
    calc C.Qi τ * (umat γ⁻¹ * (umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ))) * C.Q τ * (C.y τ)⁻¹
        = (C.Qi τ * C.Q τ) * Matrix.of x * (C.y τ * ((C.Qi τ * C.Q τ) * (C.y τ)⁻¹)) := by
          rw [← Matrix.mul_assoc (umat γ⁻¹) (umat γ), hg, Matrix.one_mul]
          simp only [Matrix.mul_assoc]
      _ = Matrix.of x := by
          rw [h1, Matrix.one_mul, Matrix.one_mul, hy, Matrix.mul_one]

end Formalism.L2.SG.Pf.LocJEq
