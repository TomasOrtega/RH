import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MeasMulF

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open Formalism.L2.SG.RealObj.EnergyIntTor Formalism.L2.SG.RealObj.EnergyIntLoc
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.EnergyConvJ

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

def Tm (C : Choice X θ) (τ : D.what₂.Tau) (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x)

/- English proof (translation)
Establish `hrd : 0 < D.host.rdE`. Unfold `Formalism.BasicNotions.Host.rdE`. Conclude with `Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero _))) _`. Establish `hka : 0 < D.host.ka`. Unfold `Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v`.

Conclude with `div_pos Real.pi_pos (half_pos hrd)`. Establish `hg : (D.host.g 0 * D.host.g 1 : ℕ) ≠ 0` using `Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero`. Establish `hfr : Formalism.L2.SG.LocWSOf.frS D ≠ 0`. Unfold `Formalism.L2.SG.LocWSOf.frS`. Conclude with `Complex.ofReal_ne_zero.mpr (div_pos hka (by positivity : (0:ℝ) < 2 * Real.pi)).ne'`.

Establish `hcf : Formalism.L2.SG.LocWSOf.cfS D ≠ 0`. Unfold `Formalism.L2.SG.LocWSOf.cfS`. Establish `hpi : (2 * (Real.pi : ℂ)) ≠ 0` using `mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)`. Use `div_ne_zero (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero ?_)) hpi` and prove the remaining obligations. Conclude with `Complex.ofReal_ne_zero.mpr (Nat.cast_ne_zero.mpr hg)`.

Unfold `Formalism.L2.SG.LocWSOf.muT`. Conclude with `div_ne_zero hcf hfr`.
-/
private theorem muT_ne_zero (D : D7) : Formalism.L2.SG.LocWSOf.muT D ≠ 0 := by
  have hrd : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero _))) _
  have hka : 0 < D.host.ka := by
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    exact div_pos Real.pi_pos (half_pos hrd)
  have hg : (D.host.g 0 * D.host.g 1 : ℕ) ≠ 0 :=
    Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hfr : Formalism.L2.SG.LocWSOf.frS D ≠ 0 := by
    unfold Formalism.L2.SG.LocWSOf.frS
    exact Complex.ofReal_ne_zero.mpr (div_pos hka (by positivity : (0:ℝ) < 2 * Real.pi)).ne'
  have hcf : Formalism.L2.SG.LocWSOf.cfS D ≠ 0 := by
    unfold Formalism.L2.SG.LocWSOf.cfS
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    refine div_ne_zero (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero ?_)) hpi
    exact Complex.ofReal_ne_zero.mpr (Nat.cast_ne_zero.mpr hg)
  unfold Formalism.L2.SG.LocWSOf.muT
  exact div_ne_zero hcf hfr

/- English proof (translation)
Unfold `Formalism.L2.SG.LocWSOf.torS`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `split_ifs <;> first | (simp [hμ]; done) | (field_simp; done) | (simp [hμ, inv_pow, star_inv']; done)`.
-/
private theorem torS_mul_torS_inv_eq_one {μ : ℂ} (hμ : μ ≠ 0) (k r : ℕ) :
    Formalism.L2.SG.LocWSOf.torS μ k r * Formalism.L2.SG.LocWSOf.torS μ⁻¹ k r = 1 := by
  unfold Formalism.L2.SG.LocWSOf.torS
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> first | (simp [hμ]; done) | (field_simp; done) | (simp [hμ, inv_pow, star_inv']; done)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Formalism.L2.SG.LocWSOf.torS, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply, Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]`. Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Apply the tactic sequence `split_ifs <;> first`.

Consider the case `omega`. Consider the case `(simp; done)`. Consider the case `(rw [show 2 * r + k - (j : ℕ) = (i : ℕ) by omega]; simp [hμ]; done)`. Consider the case `(rw [show 2 * r + k - (i : ℕ) = (j : ℕ) by omega]; simp [hμ]; done)`. Consider the case `(simp [hμ]; done)`.
-/
private theorem torS_conjTranspose_mul_Hpk_mul_torS_eq_Hpk {μ : ℂ} (hμ : μ ≠ 0) (k r : ℕ) :
    (Formalism.L2.SG.LocWSOf.torS μ k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Formalism.L2.SG.LocWSOf.torS μ k r =
      Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  simp only [Formalism.L2.SG.LocWSOf.torS, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Pi.star_apply, Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  have hi := i.isLt
  have hj := j.isLt
  split_ifs <;> first
    | omega
    | (simp; done)
    | (rw [show 2 * r + k - (j : ℕ) = (i : ℕ) by omega]; simp [hμ]; done)
    | (rw [show 2 * r + k - (i : ℕ) = (j : ℕ) by omega]; simp [hμ]; done)
    | (simp [hμ]; done)

/- English proof (translation)
Establish `hT` using `C.isT τ`. Unfold `Formalism.L2.SG.LocWSOf.IsTranspC at hT`. Take `⟨h1, -, -, -⟩` from `hT`. Establish `ht` using `torS_mul_torS_inv_eq_one (inv_ne_zero (muT_ne_zero D)) D.R.k D.R.rS`. Rewrite `ht` using `[inv_inv]`.

Unfold `Formalism.L2.SG.LocWSOf.Qics Formalism.L2.SG.LocWSOf.Qcs`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (C.Qi τ), h1, Matrix.one_mul, ht]`.
-/
private theorem Qics_mul_Qcs_eq_one (C : Choice X θ) (τ : D.what₂.Tau) : Qics C τ * Qcs C τ = 1 := by
  have hT := C.isT τ
  unfold Formalism.L2.SG.LocWSOf.IsTranspC at hT
  obtain ⟨h1, -, -, -⟩ := hT
  have ht := torS_mul_torS_inv_eq_one (inv_ne_zero (muT_ne_zero D)) D.R.k D.R.rS
  rw [inv_inv] at ht
  unfold Formalism.L2.SG.LocWSOf.Qics Formalism.L2.SG.LocWSOf.Qcs
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (C.Qi τ), h1, Matrix.one_mul, ht]

/- English proof (translation)
Establish `hT` using `C.isT τ`. Unfold `Formalism.L2.SG.LocWSOf.IsTranspC at hT`. Take `⟨-, h2, -, -⟩` from `hT`. Unfold `Formalism.L2.SG.LocWSOf.Qics Formalism.L2.SG.LocWSOf.Qcs`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D) D.R.k D.R.rS), torS_mul_torS_inv_eq_one (muT_ne_zero D), Matrix.one_mul, h2]`.
-/
private theorem Qcs_mul_Qics_eq_one (C : Choice X θ) (τ : D.what₂.Tau) : Qcs C τ * Qics C τ = 1 := by
  have hT := C.isT τ
  unfold Formalism.L2.SG.LocWSOf.IsTranspC at hT
  obtain ⟨-, h2, -, -⟩ := hT
  unfold Formalism.L2.SG.LocWSOf.Qics Formalism.L2.SG.LocWSOf.Qcs
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D) D.R.k D.R.rS),
    torS_mul_torS_inv_eq_one (muT_ne_zero D), Matrix.one_mul, h2]

/- English proof (translation)
Establish `hT` using `C.isT τ`. Unfold `Formalism.L2.SG.LocWSOf.IsTranspC at hT`. Take `⟨-, -, h3, -⟩` from `hT`. Unfold `Formalism.L2.SG.LocWSOf.Qcs`. Rewrite using `[Matrix.conjTranspose_mul]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [h3, torS_conjTranspose_mul_Hpk_mul_torS_eq_Hpk (muT_ne_zero D)]`.
-/
private theorem Qcs_conjTranspose_mul_Jm_mul_Qcs_eq_Hpk (C : Choice X θ) (τ : D.what₂.Tau) :
    (Qcs C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * Qcs C τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by
  have hT := C.isT τ
  unfold Formalism.L2.SG.LocWSOf.IsTranspC at hT
  obtain ⟨-, -, h3, -⟩ := hT
  unfold Formalism.L2.SG.LocWSOf.Qcs
  rw [Matrix.conjTranspose_mul]
  calc _ = (Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D) D.R.k D.R.rS)ᴴ *
        ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) *
        Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D) D.R.k D.R.rS := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h3, torS_conjTranspose_mul_Hpk_mul_torS_eq_Hpk (muT_ne_zero D)]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem of_Tm_eq_Qics_mul_mul_Qcs (C : Choice X θ) (τ : D.what₂.Tau) (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix.of (Tm C τ x) = Qics C τ * ((x : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * Qcs C τ := rfl

/- English proof (translation)
Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (Qcs C τ) (Qics C τ), Qcs_mul_Qics_eq_one, Matrix.one_mul]`.
-/
private theorem Qics_mul_Qcs_conj_mul_conj_eq_conj_mul (C : Choice X θ) (τ : D.what₂.Tau) (U V : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) :
    Qics C τ * U * Qcs C τ * (Qics C τ * V * Qcs C τ) = Qics C τ * (U * V) * Qcs C τ := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Qcs C τ) (Qics C τ), Qcs_mul_Qics_eq_one, Matrix.one_mul]

/- English proof (translation)
Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
private theorem Jm_mul_self_eq_one {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

/- English proof (translation)
Establish `hm' : (Matrix.of m)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS` using `hm`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (Qics C τ)ᴴ * ((Qcs C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * Qcs C τ) * Qics C τ := by rw [Qcs_conjTranspose_mul_Jm_mul_Qcs_eq_Hpk C τ, hm']`. Use `_ = (Qcs C τ * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Qics C τ) := by`.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by rw [Qcs_mul_Qics_eq_one C τ, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`.
-/
private theorem Qcs_conj_conjTranspose_Jm_eq_Jm_of_mem_UH (C : Choice X θ) (τ : D.what₂.Tau) (m : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)
    (hm : Matrix.of m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    (Qcs C τ * Matrix.of m * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m * Qics C τ) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
  have hm' : (Matrix.of m)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm
  calc (Qcs C τ * Matrix.of m * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m * Qics C τ)
      = (Qics C τ)ᴴ * ((Matrix.of m)ᴴ * ((Qcs C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * Qcs C τ) * Matrix.of m) * Qics C τ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (Qics C τ)ᴴ * ((Qcs C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * Qcs C τ) * Qics C τ := by rw [Qcs_conjTranspose_mul_Jm_mul_Qcs_eq_Hpk C τ, hm']
    _ = (Qcs C τ * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Qics C τ) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by rw [Qcs_mul_Qics_eq_one C τ, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [Qcs_mul_Qics_eq_one C τ, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`.
-/
private theorem Qics_conj_conjTranspose_mul_form_mul_conj_eq (C : Choice X θ) (τ : D.what₂.Tau) (U : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) :
    (Qics C τ * U * Qcs C τ)ᴴ * ((Qcs C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * Qcs C τ) * (Qics C τ * U * Qcs C τ) =
      (Qcs C τ)ᴴ * (Uᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * U) * Qcs C τ := by
  calc _ = (Qcs C τ)ᴴ * (Uᴴ * ((Qcs C τ * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Qics C τ)) * U) * Qcs C τ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [Qcs_mul_Qics_eq_one C τ, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Establish `hU : ((x : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * ((x : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ))` using `x.2`. Use `show (Matrix.of (Tm C τ x))ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of (Tm C τ x) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS`. Rewrite using `[of_Tm_eq_Qics_mul_mul_Qcs]`. Use `conv_lhs => rw [← Qcs_conjTranspose_mul_Jm_mul_Qcs_eq_Hpk C τ]`. Rewrite using `[Qics_conj_conjTranspose_mul_form_mul_conj_eq C τ, hU, Qcs_conjTranspose_mul_Jm_mul_Qcs_eq_Hpk C τ]`.
-/
private theorem of_Tm_mem_UH_Hpk (C : Choice X θ) (τ : D.what₂.Tau) (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix.of (Tm C τ x) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  have hU : ((x : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * ((x : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := x.2
  show (Matrix.of (Tm C τ x))ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of (Tm C τ x) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
  rw [of_Tm_eq_Qics_mul_mul_Qcs]
  conv_lhs => rw [← Qcs_conjTranspose_mul_Jm_mul_Qcs_eq_Hpk C τ]
  rw [Qics_conj_conjTranspose_mul_form_mul_conj_eq C τ, hU, Qcs_conjTranspose_mul_Jm_mul_Qcs_eq_Hpk C τ]

/- English proof (translation)
Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Qcs_mul_Qics_eq_one, Matrix.mul_one, ← Matrix.mul_assoc, Qcs_mul_Qics_eq_one, Matrix.one_mul]`.
-/
private theorem Qcs_mul_Qics_conj_mul_Qics_eq_self (C : Choice X θ) (τ : D.what₂.Tau) (A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) :
    Qcs C τ * (Qics C τ * A * Qcs C τ) * Qics C τ = A := by
  simp only [Matrix.mul_assoc]
  rw [Qcs_mul_Qics_eq_one, Matrix.mul_one, ← Matrix.mul_assoc, Qcs_mul_Qics_eq_one, Matrix.one_mul]

/- English proof (translation)
Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Qics_mul_Qcs_eq_one, Matrix.mul_one, ← Matrix.mul_assoc, Qics_mul_Qcs_eq_one, Matrix.one_mul]`.
-/
private theorem Qics_mul_Qcs_conj_mul_Qcs_eq_self (C : Choice X θ) (τ : D.what₂.Tau)
    (A : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) :
    Qics C τ * (Qcs C τ * A * Qics C τ) * Qcs C τ = A := by
  simp only [Matrix.mul_assoc]
  rw [Qics_mul_Qcs_eq_one, Matrix.mul_one, ← Matrix.mul_assoc, Qics_mul_Qcs_eq_one, Matrix.one_mul]

/- English proof (translation)
Establish `hU` using `Qcs_conj_conjTranspose_Jm_eq_Jm_of_mem_UH C τ m hm`. Establish `hl : Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m * Qics C τ) = 1`. Rewrite using `[show ∀ A B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, A * Bᴴ * A * B = A * (Bᴴ * A * B) from fun A B => by`. Simplify using `only [Matrix.mul_assoc], hU, Jm_mul_self_eq_one]`. Apply the tactic sequence `refine ⟨⟨⟨Qcs C τ * Matrix.of m * Qics C τ, Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)), (by first | exact Matrix.mul_eq_one_comm.mp (hl) | exact mul_eq_one_comm.mp (hl) | exact Matrix.mul_eq_one_symm (hl) | …`.

Apply `Matrix.of.injective` to reduce the goal to its premises. Rewrite using `[of_Tm_eq_Qics_mul_mul_Qcs]`. Conclude with `Qics_mul_Qcs_conj_mul_Qcs_eq_self C τ (Matrix.of m)`.
-/
private theorem mem_range_Tm_of_of_mem_UH (C : Choice X θ) (τ : D.what₂.Tau) {m : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS}
    (hm : Matrix.of m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) : m ∈ Set.range (Tm C τ) := by
  have hU := Qcs_conj_conjTranspose_Jm_eq_Jm_of_mem_UH C τ m hm
  have hl : Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m * Qics C τ) = 1 := by
    rw [show ∀ A B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, A * Bᴴ * A * B = A * (Bᴴ * A * B) from fun A B => by
      simp only [Matrix.mul_assoc], hU, Jm_mul_self_eq_one]
  refine ⟨⟨⟨Qcs C τ * Matrix.of m * Qics C τ, Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)),
    (by first | exact Matrix.mul_eq_one_comm.mp (hl) | exact mul_eq_one_comm.mp (hl) | exact Matrix.mul_eq_one_symm (hl) | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp (hl)), hl⟩, hU⟩, ?_⟩
  apply Matrix.of.injective
  rw [of_Tm_eq_Qics_mul_mul_Qcs]
  exact Qics_mul_Qcs_conj_mul_Qcs_eq_self C τ (Matrix.of m)

/- English proof (translation)
Establish `hc : Continuous fun m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => mᴴ * Formalism.QuantumDeterminants.Hpk k r * m` using `(continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id`. Conclude with `isClosed_eq hc continuous_const`.
-/
private theorem isClosed_setOf_of_mem_UH_Hpk (k r : ℕ) :
    IsClosed {m : Formalism.QuantumDeterminants.Mt k r | Matrix.of m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
  have hc : Continuous fun m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
      mᴴ * Formalism.QuantumDeterminants.Hpk k r * m :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  exact isClosed_eq hc continuous_const

/- English proof (translation)
Use `haveI : BorelSpace (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) := ⟨rfl⟩`. Establish `hcont : Continuous (Tm C τ)`. Establish `h : Continuous fun x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => Qics C τ * ((x : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * Qcs C τ` using `(continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul continuous_const`. Conclude with `h`. Establish `hrange : Set.range (Tm C τ) = {m | Matrix.of m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)}`.

Use extensionality with `m`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Conclude with `of_Tm_mem_UH_Hpk C τ x`. Introduce `hm`.

Conclude with `mem_range_Tm_of_of_mem_UH C τ hm`. Establish `hUJ : ∀ m : Set.range (Tm C τ), (Qcs C τ * Matrix.of m.1 * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m.1 * Qics C τ) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ))`. Introduce `m`. Apply `Qcs_conj_conjTranspose_Jm_eq_Jm_of_mem_UH C τ` to reduce the goal to its premises. Take `⟨x, hx⟩` from `m.2`.

Rewrite using `[← hx]`. Conclude with `of_Tm_mem_UH_Hpk C τ x`. Establish `hl : ∀ m : Set.range (Tm C τ), Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m.1 * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m.1 * Qics C τ) = 1`. Introduce `m`. Rewrite using `[show ∀ A B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, A * Bᴴ * A * B = A * (Bᴴ * A * B) from fun A B => by`.

Simplify using `only [Matrix.mul_assoc], hUJ m, Jm_mul_self_eq_one]`. Apply the tactic sequence `let g : Set.range (Tm C τ) → Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) := fun m => ⟨⟨Qcs C τ * Matrix.of m.1 * Qics C τ, Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m.1 * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)), (by first | exact Matrix.mul_eq_one_comm.mp …`. Establish `hv : Continuous fun m : Set.range (Tm C τ) => Qcs C τ * Matrix.of m.1 * Qics C τ`. Establish `h0 : Continuous fun m : Set.range (Tm C τ) => (Matrix.of m.1 : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)` using `continuous_subtype_val`. Conclude with `(continuous_const.matrix_mul h0).matrix_mul continuous_const`.

Establish `hg : Continuous g`. Apply `Continuous.subtype_mk` to reduce the goal to its premises. Rewrite using `[Units.continuous_iff]`. Prove the components needed by the constructor for the conclusion. Conclude with `hv`.

Conclude with `(continuous_const.matrix_mul hv.matrix_conjTranspose).matrix_mul continuous_const`. Use `MeasurableEmbedding.of_measurable_inverse_on_range hcont.measurable ?_ hg.measurable ?_` and prove the remaining obligations. Rewrite using `[hrange]`. Conclude with `(isClosed_setOf_of_mem_UH_Hpk D.R.k D.R.rS).measurableSet`. Introduce `x`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `show Qcs C τ * Matrix.of (Tm C τ x) * Qics C τ = _`. Rewrite using `[of_Tm_eq_Qics_mul_mul_Qcs]`. Conclude with `Qcs_mul_Qics_conj_mul_Qics_eq_self C τ _`.
-/
theorem Tm_emb (C : Choice X θ) (τ : D.what₂.Tau) : MeasurableEmbedding (Tm C τ) := by
  haveI : BorelSpace (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) := ⟨rfl⟩
  have hcont : Continuous (Tm C τ) := by
    have h : Continuous fun x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => Qics C τ * ((x : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * Qcs C τ :=
      (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul
        continuous_const
    exact h
  have hrange : Set.range (Tm C τ) = {m | Matrix.of m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} := by
    ext m
    constructor
    · rintro ⟨x, rfl⟩
      exact of_Tm_mem_UH_Hpk C τ x
    · intro hm
      exact mem_range_Tm_of_of_mem_UH C τ hm
  have hUJ : ∀ m : Set.range (Tm C τ), (Qcs C τ * Matrix.of m.1 * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) *
      (Qcs C τ * Matrix.of m.1 * Qics C τ) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    intro m
    apply Qcs_conj_conjTranspose_Jm_eq_Jm_of_mem_UH C τ
    obtain ⟨x, hx⟩ := m.2
    rw [← hx]
    exact of_Tm_mem_UH_Hpk C τ x
  have hl : ∀ m : Set.range (Tm C τ), Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m.1 * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) *
      (Qcs C τ * Matrix.of m.1 * Qics C τ) = 1 := by
    intro m
    rw [show ∀ A B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, A * Bᴴ * A * B = A * (Bᴴ * A * B) from fun A B => by
      simp only [Matrix.mul_assoc], hUJ m, Jm_mul_self_eq_one]
  let g : Set.range (Tm C τ) → Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) := fun m =>
    ⟨⟨Qcs C τ * Matrix.of m.1 * Qics C τ, Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m.1 * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)),
      (by first | exact Matrix.mul_eq_one_comm.mp (hl m) | exact mul_eq_one_comm.mp (hl m) | exact Matrix.mul_eq_one_symm (hl m) | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp (hl m)), hl m⟩, hUJ m⟩
  have hv : Continuous fun m : Set.range (Tm C τ) => Qcs C τ * Matrix.of m.1 * Qics C τ := by
    have h0 : Continuous fun m : Set.range (Tm C τ) => (Matrix.of m.1 : Matrix (Fin (2 * D.R.rS + D.R.k + 1))
        (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) := continuous_subtype_val
    exact (continuous_const.matrix_mul h0).matrix_mul continuous_const
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    constructor
    · exact hv
    · exact (continuous_const.matrix_mul hv.matrix_conjTranspose).matrix_mul continuous_const
  refine MeasurableEmbedding.of_measurable_inverse_on_range hcont.measurable ?_ hg.measurable ?_
  · rw [hrange]
    exact (isClosed_setOf_of_mem_UH_Hpk D.R.k D.R.rS).measurableSet
  · intro x
    apply Subtype.ext
    apply Units.ext
    show Qcs C τ * Matrix.of (Tm C τ x) * Qics C τ = _
    rw [of_Tm_eq_Qics_mul_mul_Qcs]
    exact Qcs_mul_Qics_conj_mul_Qics_eq_self C τ _

/- English proof (translation)
Apply `Matrix.of.injective` to reduce the goal to its premises. Use `show Matrix.of (Tm C τ (a * b)) = Matrix.of (Tm C τ a) * Matrix.of (Tm C τ b)`. Rewrite using `[of_Tm_eq_Qics_mul_mul_Qcs, of_Tm_eq_Qics_mul_mul_Qcs, of_Tm_eq_Qics_mul_mul_Qcs, Qics_mul_Qcs_conj_mul_conj_eq_conj_mul]`. Apply the tactic sequence `all_goals first | rfl | simp [Subgroup.coe_mul, Units.val_mul]`.
-/
theorem Tm_mul (C : Choice X θ) (τ : D.what₂.Tau) (a b : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Tm C τ (a * b) = mulF (Tm C τ a, Tm C τ b) := by
  apply Matrix.of.injective
  show Matrix.of (Tm C τ (a * b)) = Matrix.of (Tm C τ a) * Matrix.of (Tm C τ b)
  rw [of_Tm_eq_Qics_mul_mul_Qcs, of_Tm_eq_Qics_mul_mul_Qcs, of_Tm_eq_Qics_mul_mul_Qcs, Qics_mul_Qcs_conj_mul_conj_eq_conj_mul]
  all_goals first | rfl | simp [Subgroup.coe_mul, Units.val_mul]

/- English proof (translation)
Apply `Matrix.of.injective` to reduce the goal to its premises. Use `show Matrix.of (Tm C τ a⁻¹) = (Matrix.of (Tm C τ a))⁻¹`. Rewrite using `[of_Tm_eq_Qics_mul_mul_Qcs, of_Tm_eq_Qics_mul_mul_Qcs]`. Use `symm`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises.

Rewrite using `[Qics_mul_Qcs_conj_mul_conj_eq_conj_mul]`. Simplify using `only [Subgroup.coe_inv, Units.mul_inv, Matrix.mul_one, Qics_mul_Qcs_eq_one]`.
-/
theorem Tm_inv (C : Choice X θ) (τ : D.what₂.Tau) (a : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Tm C τ a⁻¹ = Formalism.FourierDecayAlt.B2.invM (Tm C τ a) := by
  apply Matrix.of.injective
  show Matrix.of (Tm C τ a⁻¹) = (Matrix.of (Tm C τ a))⁻¹
  rw [of_Tm_eq_Qics_mul_mul_Qcs, of_Tm_eq_Qics_mul_mul_Qcs]
  symm
  apply Matrix.inv_eq_right_inv
  rw [Qics_mul_Qcs_conj_mul_conj_eq_conj_mul]
  simp only [Subgroup.coe_inv, Units.mul_inv, Matrix.mul_one, Qics_mul_Qcs_eq_one]

/- English proof (translation)
The claim follows from `of_Tm_mem_UH_Hpk C τ x`.
-/
theorem Tm_mem (C : Choice X θ) (τ : D.what₂.Tau) (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix.of (Tm C τ x) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := of_Tm_mem_UH_Hpk C τ x

/- English proof (translation)
The claim follows from `mem_range_Tm_of_of_mem_UH C τ hm`.
-/
theorem mem_range_Tm (C : Choice X θ) (τ : D.what₂.Tau) {m : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS}
    (hm : Matrix.of m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) : m ∈ Set.range (Tm C τ) := mem_range_Tm_of_of_mem_UH C τ hm

/- English proof (translation)
Establish `hE` using `Tm_emb C τ`. Establish `hae : ∀ᵐ m ∂μ, m ∈ Set.range (Tm C τ)`. Rewrite using `[ae_iff]`. Use `measure_mono_null (fun m hm => ?_) hμ` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hm ⊢`.

Conclude with `fun h => hm (mem_range_Tm C τ h)`. Rewrite using `[← hE.lintegral_map, hE.map_comap, Measure.restrict_eq_self_of_ae_mem hae]`.
-/
theorem comap_lint (C : Choice X θ) (τ : D.what₂.Tau) {μ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    (hμ : μ {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (F : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → ℝ≥0∞) :
    ∫⁻ x, F (Tm C τ x) ∂(μ.comap (Tm C τ)) = ∫⁻ m, F m ∂μ := by
  have hE := Tm_emb C τ
  have hae : ∀ᵐ m ∂μ, m ∈ Set.range (Tm C τ) := by
    rw [ae_iff]
    refine measure_mono_null (fun m hm => ?_) hμ
    simp only [Set.mem_setOf_eq] at hm ⊢
    exact fun h => hm (mem_range_Tm C τ h)
  rw [← hE.lintegral_map, hE.map_comap, Measure.restrict_eq_self_of_ae_mem hae]

/- English proof (translation)
Establish `hE` using `Tm_emb C τ`. Use `first`. Consider the case `exact SigmaFinite.of_map _ hE.measurable.aemeasurable (by rw [hE.map_comap]; infer_instance)`. Consider the case `infer_instance`.
-/
theorem sigmaFinite_comap (C : Choice X θ) (τ : D.what₂.Tau) {μ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    [SigmaFinite μ] (hμ : μ {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0) :
    SigmaFinite (μ.comap (Tm C τ)) := by
  have hE := Tm_emb C τ
  first
    | exact SigmaFinite.of_map _ hE.measurable.aemeasurable (by rw [hE.map_comap]; infer_instance)
    | infer_instance

/- English proof (translation)
Establish `hE` using `Tm_emb C τ`. Use `first`. Consider the case `infer_instance`. Consider the case `(have h : μ.comap (Tm C τ) = Measure.sum (fun n => (sfiniteSeq μ n).comap (Tm C τ)) := by`. Use extensionality with `s hs`.

Rewrite using `[hE.comap_apply, Measure.sum_apply _ hs]`. Use `conv_lhs => rw [← sum_sfiniteSeq μ]`. Rewrite using `[Measure.sum_apply _ (hE.measurableSet_image.mpr hs)]`. Simplify using `only [hE.comap_apply]`. Use `haveI : ∀ n, IsFiniteMeasure ((sfiniteSeq μ n).comap (Tm C τ)) := fun n => ⟨by rw [hE.comap_apply _ Set.univ]; exact measure_lt_top _ _⟩`.

Rewrite using `[h]`. Use the proof step `infer_instance)`.
-/
theorem sFinite_comap (C : Choice X θ) (τ : D.what₂.Tau) {μ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    [SFinite μ] : SFinite (μ.comap (Tm C τ)) := by
  have hE := Tm_emb C τ
  first
    | infer_instance
    | (have h : μ.comap (Tm C τ) = Measure.sum (fun n => (sfiniteSeq μ n).comap (Tm C τ)) := by
          ext s hs
          rw [hE.comap_apply, Measure.sum_apply _ hs]
          conv_lhs => rw [← sum_sfiniteSeq μ]
          rw [Measure.sum_apply _ (hE.measurableSet_image.mpr hs)]
          simp only [hE.comap_apply]
       haveI : ∀ n, IsFiniteMeasure ((sfiniteSeq μ n).comap (Tm C τ)) := fun n =>
         ⟨by rw [hE.comap_apply _ Set.univ]; exact measure_lt_top _ _⟩
       rw [h]
       infer_instance)

/- English proof (translation)
The claim follows from `(isClosed_setOf_of_mem_UH_Hpk D.R.k D.R.rS).measurableSet.compl`.
-/
theorem measurableSet_notUH : MeasurableSet {m : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS |
    Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} :=
  (isClosed_setOf_of_mem_UH_Hpk D.R.k D.R.rS).measurableSet.compl

/- English proof (translation)
Establish `hSm` using `measurableSet_notUH (D := D)`. Use `set S := {m : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} with hSdef`. Establish `key : ∀ s x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS, s ∉ S → x ∈ S → (fun i j => (Matrix.of s * Matrix.of x) i j) ∈ S`. Introduce `s x hs hx hsx`. Establish `hs' : (Matrix.of s)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of s = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS` using `Classical.byContradiction fun h => hs h`.

Establish `hsx' : (Matrix.of s * Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (Matrix.of s * Matrix.of x) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS` using `hsx`. Establish `hx' : ¬ ((Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of x = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)` using `hx`. Apply `hx'` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hsx'`. Establish `hc : μS Sᶜ = μS Set.univ`. Rewrite using `[measure_compl hSm (by rw [hS0]; exact ENNReal.zero_ne_top), hS0, tsub_zero]`. Establish `hne : μS Set.univ ≠ 0` using `Measure.measure_univ_ne_zero.mpr hSne`. Establish `h` using `hq (S.indicator 1) (measurable_one.indicator hSm)`.

Rewrite `h` using `[lintegral_indicator_one hSm, hG0]`. Establish `hle : ∫⁻ x, S.indicator (fun _ => μS Set.univ) x ∂ν ≤ ∫⁻ x, ∫⁻ s, S.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ∂ν`. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ S`. Rewrite using `[Set.indicator_of_mem hx, ← hc, ← lintegral_indicator_one hSm.compl]`.

Use `lintegral_mono fun s => ?_` and prove the remaining obligations. Distinguish the cases in `hs : s ∈ S`. Apply the tactic sequence `have hs2 : s ∉ Sᶜ := fun h2 => h2 hs first | rw [Set.indicator_of_not_mem hs2] | rw [Set.indicator_of_notMem hs2] first | exact zero_le | exact zero_le _ | positivity`. Apply the tactic sequence `rw [Set.indicator_of_mem (Set.mem_compl hs), Set.indicator_of_mem (key s x hs hx)] all_goals exact le_rfl`. Apply the tactic sequence `first | rw [Set.indicator_of_not_mem hx] | rw [Set.indicator_of_notMem hx] first | exact zero_le | exact zero_le _ | positivity`.

Rewrite `hle` using `[← h, lintegral_indicator_const hSm]`. Conclude with `(mul_eq_zero.mp (le_zero_iff.mp hle)).resolve_left hne`.
-/
theorem quot_conc {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)} (hq : Formalism.MainNotions.S.IsQuotMeas μG μS ν)
    (hG0 : μG {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (hS0 : μS {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0) (hSne : μS ≠ 0) :
    ν {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0 := by
  have hSm := measurableSet_notUH (D := D)
  set S := {m : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} with hSdef
  have key : ∀ s x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS, s ∉ S → x ∈ S →
      (fun i j => (Matrix.of s * Matrix.of x) i j) ∈ S := by
    intro s x hs hx hsx
    have hs' : (Matrix.of s)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of s = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS :=
      Classical.byContradiction fun h => hs h
    have hsx' : (Matrix.of s * Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (Matrix.of s * Matrix.of x) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hsx
    have hx' : ¬ ((Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of x = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := hx
    apply hx'
    calc (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of x
        = (Matrix.of x)ᴴ * ((Matrix.of s)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of s) * Matrix.of x := by rw [hs']
      _ = (Matrix.of s * Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (Matrix.of s * Matrix.of x) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hsx'
  have hc : μS Sᶜ = μS Set.univ := by
    rw [measure_compl hSm (by rw [hS0]; exact ENNReal.zero_ne_top), hS0, tsub_zero]
  have hne : μS Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hSne
  have h := hq (S.indicator 1) (measurable_one.indicator hSm)
  rw [lintegral_indicator_one hSm, hG0] at h
  have hle : ∫⁻ x, S.indicator (fun _ => μS Set.univ) x ∂ν ≤
      ∫⁻ x, ∫⁻ s, S.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ∂ν := by
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, ← hc, ← lintegral_indicator_one hSm.compl]
      refine lintegral_mono fun s => ?_
      by_cases hs : s ∈ S
      · have hs2 : s ∉ Sᶜ := fun h2 => h2 hs
        first | rw [Set.indicator_of_not_mem hs2] | rw [Set.indicator_of_notMem hs2]
        first | exact zero_le | exact zero_le _ | positivity
      · rw [Set.indicator_of_mem (Set.mem_compl hs), Set.indicator_of_mem (key s x hs hx)]
        all_goals exact le_rfl
    · first | rw [Set.indicator_of_not_mem hx] | rw [Set.indicator_of_notMem hx]
      first | exact zero_le | exact zero_le _ | positivity
  rw [← h, lintegral_indicator_const hSm] at hle
  exact (mul_eq_zero.mp (le_zero_iff.mp hle)).resolve_left hne

/- English proof (translation)
Establish `hE` using `Tm_emb C τ`. Take `⟨F, hF, hFT⟩ : ∃ F : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → ℝ≥0∞, Measurable F ∧ ∀ x, F (Tm C τ x) = f x` from `⟨Function.extend (Tm C τ) f (fun _ => 0), hE.measurable_extend hf measurable_const, fun x => hE.injective.extend_apply f _ x⟩`. Establish `hmu : muGB X (Qcs C τ) (Qics C τ) τ = (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map (Tm C τ)` using `rfl`. Establish `key` using `hq F hF`. Rewrite `key` using `[hmu, hE.lintegral_map]`.

Simplify using `only [hFT] at key`. Rewrite using `[key]`. Use `symm`. Establish `inner : ∀ x, ∫⁻ s, f (s * x) ∂(μS.comap (Tm C τ)) = ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of (Tm C τ x)) i j) ∂μS`. Introduce `x`.

Rewrite using `[← comap_lint C τ hS0 (fun s => F (fun i j => (Matrix.of s * Matrix.of (Tm C τ x)) i j))]`. Use `congr 1`. Use function extensionality and compare the values at `s`. Rewrite using `[← hFT (s * x), Tm_mul]`. Both sides reduce to the same expression.

Conclude with `(lintegral_congr fun x => inner x).trans (comap_lint C τ hν0 (fun y => ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of y) i j) ∂μS))`.
-/
theorem weil_J (C : Choice X θ) (τ : D.what₂.Tau) {μS ν : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    (hq : Formalism.MainNotions.S.IsQuotMeas (muGB X (Qcs C τ) (Qics C τ) τ) μS ν)
    (hS0 : μS {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (hν0 : ν {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) =
      ∫⁻ x, ∫⁻ s, f (s * x) ∂(μS.comap (Tm C τ)) ∂(ν.comap (Tm C τ)) := by
  have hE := Tm_emb C τ
  obtain ⟨F, hF, hFT⟩ : ∃ F : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → ℝ≥0∞, Measurable F ∧ ∀ x, F (Tm C τ x) = f x :=
    ⟨Function.extend (Tm C τ) f (fun _ => 0), hE.measurable_extend hf measurable_const,
      fun x => hE.injective.extend_apply f _ x⟩
  have hmu : muGB X (Qcs C τ) (Qics C τ) τ = (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map (Tm C τ) := rfl
  have key := hq F hF
  rw [hmu, hE.lintegral_map] at key
  simp only [hFT] at key
  rw [key]
  symm
  have inner : ∀ x, ∫⁻ s, f (s * x) ∂(μS.comap (Tm C τ)) =
      ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of (Tm C τ x)) i j) ∂μS := by
    intro x
    rw [← comap_lint C τ hS0 (fun s => F (fun i j => (Matrix.of s * Matrix.of (Tm C τ x)) i j))]
    congr 1
    funext s
    rw [← hFT (s * x), Tm_mul]
    rfl
  exact (lintegral_congr fun x => inner x).trans
    (comap_lint C τ hν0 (fun y => ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of y) i j) ∂μS))

/- English proof (translation)
Establish `hdet : Continuous fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x).det`. Conclude with `(continuous_id (X := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)).matrix_det`. Establish `hadj : Continuous fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x).adjugate`. Conclude with `(continuous_id (X := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)).matrix_adjugate`. Establish `hinv : Measurable fun x : Formalism.QuantumDeterminants.Mt k r => ((Matrix.of x).det)⁻¹` using `hdet.measurable.inv`.

Establish `e : (Formalism.FourierDecayAlt.B2.invM (k` using `k) (r := r)) = fun x i j => ((Matrix.of x).det)⁻¹ * (Matrix.of x).adjugate i j := by`. Use function extensionality and compare the values at `x i j`. Use `show ((Matrix.of x)⁻¹ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j = _`. Rewrite using `[Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]`. Apply the tactic sequence `first | rw [Ring.inverse_eq_inv'] | rw [Ring.inverse_eq_inv] | simp`.

Rewrite using `[e]`. Use `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Conclude with `hinv.mul ((continuous_apply j).comp ((continuous_apply i).comp hadj)).measurable`.
-/
private theorem measurable_invM' (k r : ℕ) : Measurable (Formalism.FourierDecayAlt.B2.invM (k := k) (r := r)) := by
  have hdet : Continuous fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x).det := by
    exact (continuous_id (X := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)).matrix_det
  have hadj : Continuous fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x).adjugate := by
    exact (continuous_id (X := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)).matrix_adjugate
  have hinv : Measurable fun x : Formalism.QuantumDeterminants.Mt k r => ((Matrix.of x).det)⁻¹ := hdet.measurable.inv
  have e : (Formalism.FourierDecayAlt.B2.invM (k := k) (r := r)) =
      fun x i j => ((Matrix.of x).det)⁻¹ * (Matrix.of x).adjugate i j := by
    funext x i j
    show ((Matrix.of x)⁻¹ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j = _
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    first | rw [Ring.inverse_eq_inv'] | rw [Ring.inverse_eq_inv] | simp
  rw [e]
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  exact hinv.mul ((continuous_apply j).comp ((continuous_apply i).comp hadj)).measurable

/- English proof (translation)
Use `haveI : BorelSpace (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) := ⟨rfl⟩`. Establish `hE` using `Tm_emb C τ`. Establish `hinvm : Measurable (fun x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => x⁻¹)` using `continuous_inv.measurable`. Establish `hae : ∀ᵐ m ∂μS, m ∈ Set.range (Tm C τ)`. Rewrite using `[ae_iff]`.

Use `measure_mono_null (fun m hm => ?_) hS0` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hm ⊢`. Conclude with `fun h => hm (mem_range_Tm C τ h)`. Establish `hc : (Tm C τ ∘ fun x => x⁻¹) = Formalism.FourierDecayAlt.B2.invM ∘ Tm C τ` using `funext fun x => Tm_inv C τ x`. Rewrite using `[← hE.comap_map ((μS.comap (Tm C τ)).map fun x => x⁻¹), Measure.map_map hE.measurable hinvm, hc, ← Measure.map_map (measurable_invM' D.R.k D.R.rS) hE.measurable, hE.map_comap, Measure.restrict_eq_self_of_ae_mem hae, hinv]`.
-/
theorem inv_comap (C : Choice X θ) (τ : D.what₂.Tau) {μS : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    (hS0 : μS {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (hinv : μS.map Formalism.FourierDecayAlt.B2.invM = μS) :
    (μS.comap (Tm C τ)).map (fun x => x⁻¹) = μS.comap (Tm C τ) := by
  haveI : BorelSpace (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) := ⟨rfl⟩
  have hE := Tm_emb C τ
  have hinvm : Measurable (fun x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => x⁻¹) := continuous_inv.measurable
  have hae : ∀ᵐ m ∂μS, m ∈ Set.range (Tm C τ) := by
    rw [ae_iff]
    refine measure_mono_null (fun m hm => ?_) hS0
    simp only [Set.mem_setOf_eq] at hm ⊢
    exact fun h => hm (mem_range_Tm C τ h)
  have hc : (Tm C τ ∘ fun x => x⁻¹) = Formalism.FourierDecayAlt.B2.invM ∘ Tm C τ := funext fun x => Tm_inv C τ x
  rw [← hE.comap_map ((μS.comap (Tm C τ)).map fun x => x⁻¹), Measure.map_map hE.measurable hinvm, hc,
    ← Measure.map_map (measurable_invM' D.R.k D.R.rS) hE.measurable, hE.map_comap,
    Measure.restrict_eq_self_of_ae_mem hae, hinv]

end Formalism.L2.SG.RealObj.EnergyConvJ
