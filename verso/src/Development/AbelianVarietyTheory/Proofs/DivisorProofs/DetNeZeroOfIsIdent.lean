import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsOrthonormalOfLinearIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieMeasureFrameBoxGe
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.FrameBox

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def sgnR {κ : Type} {p q : κ → ℕ} {Ψ : Finset (E →+* ℂ)} (σ : κ ≃ Ψ)
    (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (τ : Ψ) (a : Fin r) : ℝ :=
  if ((e (σ.symm τ)).symm a).isLeft then 1 else -1

def SkewCond {Ψ : Finset (E →+* ℂ)} (d : Ψ → Fin r → ℝ) (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) : Prop :=
  ∀ τ : Ψ, (∑ a, Y (τ, a, a) = 0) ∧
    ∀ a b, Y (τ, b, a) * (d τ b : ℂ) + (d τ a : ℂ) * (starRingEnd ℂ) (Y (τ, a, b)) = 0

def boxEnt (d : Fin r → ℝ) (z a b a' b' : Fin r) : ℂ :=
  if a < b then (if a' = a ∧ b' = b then 1 else if a' = b ∧ b' = a then -((d a * d b : ℝ) : ℂ) else 0)
  else if b < a then
    (if a' = b ∧ b' = a then Complex.I else if a' = a ∧ b' = b then Complex.I * ((d a * d b : ℝ) : ℂ) else 0)
  else (if a' = a ∧ b' = a then Complex.I else if a' = z ∧ b' = z then -Complex.I else 0)

open Classical in

def boxVec {Ψ : Finset (E →+* ℂ)} (d : Ψ → Fin r → ℝ) (z : Fin r) (k : Ψ × {ab : Fin r × Fin r // ab ≠ (z, z)}) :
    EuclideanSpace ℂ (Ψ × Fin r × Fin r) :=
  WithLp.toLp 2 fun m => if m.1 = k.1 then boxEnt (d k.1) z k.2.1.1 k.2.1.2 m.2.1 m.2.2 else 0

def entryL {Ψ : Finset (E →+* ℂ)} (m : Ψ × Fin r × Fin r) : EuclideanSpace ℂ (Ψ × Fin r × Fin r) →ₗ[ℝ] ℂ :=
  ((EuclideanSpace.proj m : EuclideanSpace ℂ (Ψ × Fin r × Fin r) →L[ℂ] ℂ) : _ →ₗ[ℂ] ℂ).restrictScalars ℝ

def boxCoord {Ψ : Finset (E →+* ℂ)} (z : Fin r) (k : Ψ × {ab : Fin r × Fin r // ab ≠ (z, z)}) :
    EuclideanSpace ℂ (Ψ × Fin r × Fin r) →ₗ[ℝ] ℝ :=
  if k.2.1.1 < k.2.1.2 then Complex.reLm ∘ₗ entryL (k.1, k.2.1.1, k.2.1.2)
  else if k.2.1.2 < k.2.1.1 then Complex.imLm ∘ₗ entryL (k.1, k.2.1.2, k.2.1.1)
  else Complex.imLm ∘ₗ entryL (k.1, k.2.1.1, k.2.1.1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem entryL_apply {Ψ : Finset (E →+* ℂ)} (m : Ψ × Fin r × Fin r) (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) :
    entryL m Y = Y m := rfl

end GlobalTheory.CovTop.VolUp.FrameBox

namespace GlobalTheory.CovTop.VolUp.FrameBox
open Matrix

/- English proof (translation)
Take `⟨h1, h2⟩` from `hI (σ.symm τ)`. Rewrite `h1`, `h2` using `[Equiv.apply_symm_apply]`. Use `set P := permM (e (σ.symm τ)) with hP`. Use `set J := Formalism.UG.Jpq (p (σ.symm τ)) (q (σ.symm τ)) with hJdef`. Use `set M := mat x τ with hMdef`.

Use `set B := A (σ.symm τ) with hBdef`. Establish `hPA : (Pᵀ * B) * M = 1` using `by rw [Matrix.mul_assoc, h2, transpose_mul_permM]`. Establish `hdetM : M.det ≠ 0`. Introduce `h`. Use `congrArg Matrix.det hPA` as an intermediate fact.

Rewrite `this` using `[det_mul, h, mul_zero, det_one]`. Conclude with `zero_ne_one this`. Use `⟨hdetM, fun h => ?_⟩` and prove the remaining obligations. Establish `hJ : J * J = 1` using `by simp [hJdef, Formalism.UG.Jpq, fromBlocks_multiply]`. Establish `hPc : Pᴴ = Pᵀ`.

Apply the tactic sequence `ext i j; simp only [hP, permM, conjTranspose_apply, transpose_apply, of_apply]; split_ifs <;> simp`. Establish `hX : Mᴴ * (Bᴴ * J * B) * M = Pᵀ * J * P`. Rewrite using `[← hPc, ← h2, conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hsq : (Pᵀ * J * P) * (Pᵀ * J * P) = 1`.

Establish `e1 : (Pᵀ * J * P) * (Pᵀ * J * P) = Pᵀ * J * (P * Pᵀ) * J * P` using `by simp only [Matrix.mul_assoc]`. Rewrite using `[e1, permM_mul_transpose, Matrix.mul_one, Matrix.mul_assoc Pᵀ J J, hJ, Matrix.mul_one, transpose_mul_permM]`. Establish `hd0 : (Bᴴ * J * B).det = 0`. Rewrite using `[h1, det_neg, det_transpose, h, mul_zero]`. Use `congrArg Matrix.det hsq` as an intermediate fact.

Rewrite `this` using `[← hX, det_mul, det_mul, det_mul, hd0]`. Simplify using `at this`.
-/
theorem det_ne_zero_of_isIdent {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (hI : IsIdent p q Ψ G x σ A e) (τ : Ψ) : (mat x τ).det ≠ 0 ∧ (G.map τ.1).det ≠ 0 := by
  obtain ⟨h1, h2⟩ := hI (σ.symm τ)
  rw [Equiv.apply_symm_apply] at h1 h2
  set P := permM (e (σ.symm τ)) with hP
  set J := Formalism.UG.Jpq (p (σ.symm τ)) (q (σ.symm τ)) with hJdef
  set M := mat x τ with hMdef
  set B := A (σ.symm τ) with hBdef
  have hPA : (Pᵀ * B) * M = 1 := by rw [Matrix.mul_assoc, h2, transpose_mul_permM]
  have hdetM : M.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hPA
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  refine ⟨hdetM, fun h => ?_⟩
  have hJ : J * J = 1 := by simp [hJdef, Formalism.UG.Jpq, fromBlocks_multiply]
  have hPc : Pᴴ = Pᵀ := by
    ext i j; simp only [hP, permM, conjTranspose_apply, transpose_apply, of_apply]; split_ifs <;> simp
  have hX : Mᴴ * (Bᴴ * J * B) * M = Pᵀ * J * P := by
    rw [← hPc, ← h2, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have hsq : (Pᵀ * J * P) * (Pᵀ * J * P) = 1 := by
    have e1 : (Pᵀ * J * P) * (Pᵀ * J * P) = Pᵀ * J * (P * Pᵀ) * J * P := by simp only [Matrix.mul_assoc]
    rw [e1, permM_mul_transpose, Matrix.mul_one, Matrix.mul_assoc Pᵀ J J, hJ, Matrix.mul_one, transpose_mul_permM]
  have hd0 : (Bᴴ * J * B).det = 0 := by
    rw [h1, det_neg, det_transpose, h, mul_zero]
  have := congrArg Matrix.det hsq
  rw [← hX, det_mul, det_mul, det_mul, hd0] at this
  simp at this

end GlobalTheory.CovTop.VolUp.FrameBox
