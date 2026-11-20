import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicScalar

/- English proof (translation)
Introduce `p q n hn Gm A hA hG b`. Establish `hJ : (Formalism.UG.Jpq p q)ᴴ = Formalism.UG.Jpq p q` using `by simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]`. Establish `h1 : Gm⁻¹ * Gm = 1` using `Matrix.nonsing_inv_mul _ hG`. Establish `hb : (UpqT.mat b)ᴴ * Formalism.UG.Jpq p q * UpqT.mat b = Formalism.UG.Jpq p q` using `b.2`. Establish `hl : (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) * A = 1` using `by rw [Matrix.mul_assoc, hA, h1]`.

Establish `e : Fin n ≃ Fin p ⊕ Fin q` using `(finCongr hn.symm).trans finSumFinEquiv.symm`. Establish `hr : A * (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) = 1` using `(Matrix.mul_eq_one_comm_of_equiv e).1 hl`. Establish `hc : A * conjFrame Gm A (UpqT.mat b) = UpqT.mat b * A`. Establish `: A * conjFrame Gm A (UpqT.mat b) = A * (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) * (UpqT.mat b * A)`. Simplify using `only [conjFrame, Matrix.mul_assoc]`.

Rewrite using `[this, hr, Matrix.one_mul]`. Express the relevant statement in the definitionally equal form `(conjFrame Gm A (UpqT.mat b))ᴴ * Gm * conjFrame Gm A (UpqT.mat b) = Gm`. Generalize the expression as in `conjFrame Gm A (UpqT.mat b) = C at hc`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hA]`.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Aᴴ * ((UpqT.mat b)ᴴ * Formalism.UG.Jpq p q * UpqT.mat b) * A := by`. Rewrite using `[hc]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Gm := by rw [hb, hA]`.
-/
theorem conjFrame_mem_UH : ∀ (p q n : ℕ), p + q = n → ∀ (Gm : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ), (Aᴴ * Formalism.UG.Jpq p q * A : Matrix (Fin n) (Fin n) ℂ) = Gm → IsUnit Gm.det → ∀ b : UpqT p q, conjFrame Gm A (UpqT.mat b) ∈ Formalism.QuantumDeterminants.UH Gm := by
  intro p q n hn Gm A hA hG b
  have hJ : (Formalism.UG.Jpq p q)ᴴ = Formalism.UG.Jpq p q := by simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]
  have h1 : Gm⁻¹ * Gm = 1 := Matrix.nonsing_inv_mul _ hG
  have hb : (UpqT.mat b)ᴴ * Formalism.UG.Jpq p q * UpqT.mat b = Formalism.UG.Jpq p q := b.2
  have hl : (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) * A = 1 := by rw [Matrix.mul_assoc, hA, h1]
  have e : Fin n ≃ Fin p ⊕ Fin q := (finCongr hn.symm).trans finSumFinEquiv.symm
  have hr : A * (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hl
  have hc : A * conjFrame Gm A (UpqT.mat b) = UpqT.mat b * A := by
    have : A * conjFrame Gm A (UpqT.mat b) = A * (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) * (UpqT.mat b * A) := by
      simp only [conjFrame, Matrix.mul_assoc]
    rw [this, hr, Matrix.one_mul]
  change (conjFrame Gm A (UpqT.mat b))ᴴ * Gm * conjFrame Gm A (UpqT.mat b) = Gm
  generalize conjFrame Gm A (UpqT.mat b) = C at hc
  calc Cᴴ * Gm * C = (A * C)ᴴ * Formalism.UG.Jpq p q * (A * C) := by
        rw [← hA]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Aᴴ * ((UpqT.mat b)ᴴ * Formalism.UG.Jpq p q * UpqT.mat b) * A := by
        rw [hc]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Gm := by rw [hb, hA]

end GlobalTheory.AdelicScalar
