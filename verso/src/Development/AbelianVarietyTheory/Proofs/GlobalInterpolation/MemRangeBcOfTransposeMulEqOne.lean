import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OverLatticeIffSelfDualOverBase
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.OverCompare

/- English proof (translation)
Take `⟨a, rfl⟩` from `hA`. Set `a' : GL n R` to `⟨((a⁻¹ : GL n R) : Matrix n n R)ᵀ, (a : Matrix n n R)ᵀ, by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one], by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩`. Use `⟨a', Units.ext ?_⟩` and prove the remaining obligations. Establish `h1 : ((bc f a' : GL n S) : Matrix n n S) = ((bc f a⁻¹ : GL n S) : Matrix n n S)ᵀ`. Use extensionality with `i j`.

Both sides reduce to the same expression. Establish `h2 : ((bc f a⁻¹ : GL n S) : Matrix n n S)ᵀ * ((bc f a : GL n S) : Matrix n n S)ᵀ = 1`. Rewrite using `[← Matrix.transpose_mul, map_inv, Units.mul_inv, Matrix.transpose_one]`. Rewrite using `[h1]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mem_range_bc_of_transpose_mul_eq_one {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    {n : Type} [Fintype n] [DecidableEq n] (A B : GL n S)
    (hAB : (A : Matrix n n S)ᵀ * (B : Matrix n n S) = 1) (hA : A ∈ (bc (n := n) f).range) :
    B ∈ (bc (n := n) f).range := by
  obtain ⟨a, rfl⟩ := hA
  let a' : GL n R := ⟨((a⁻¹ : GL n R) : Matrix n n R)ᵀ, (a : Matrix n n R)ᵀ,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  refine ⟨a', Units.ext ?_⟩
  have h1 : ((bc f a' : GL n S) : Matrix n n S) = ((bc f a⁻¹ : GL n S) : Matrix n n S)ᵀ := by
    ext i j; rfl
  have h2 : ((bc f a⁻¹ : GL n S) : Matrix n n S)ᵀ * ((bc f a : GL n S) : Matrix n n S)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, map_inv, Units.mul_inv, Matrix.transpose_one]
  rw [h1]
  calc ((bc f a⁻¹ : GL n S) : Matrix n n S)ᵀ
      = ((bc f a⁻¹ : GL n S) : Matrix n n S)ᵀ *
          (((bc f a : GL n S) : Matrix n n S)ᵀ * (B : Matrix n n S)) := by rw [hAB, Matrix.mul_one]
    _ = (B : Matrix n n S) := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

/- English proof (translation)
Introduce `K _ O k J b c g h Λ Λ' hb hc hJ hg`. Establish `hJ' : ((b⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ * ((c⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = J`. Establish `e1 : ((b⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ * (b : Matrix (Fin k) (Fin k) K)ᵀ = 1`. Rewrite using `[← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]`. Combine the equalities or inequalities in the displayed calculation.

Establish `key : ((b⁻¹ * g * b : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ * ((c⁻¹ * h * c : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]`. Use `_ = 1 := by rw [hJ', hg, hJ]`. Rewrite using `[hb.mem_stabGL_iff, hc.mem_stabGL_iff]`.

Use `⟨mem_range_bc_of_transpose_mul_eq_one _ _ _ key, mem_range_bc_of_transpose_mul_eq_one _ _ _ ?_⟩` and prove the remaining obligations. Use `congrArg Matrix.transpose key` as an intermediate fact. Rewrite `this` using `[Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one]`. Then use the resulting hypothesis.
-/
theorem mem_stabGL_iff_of_dual_frames : ∀ (K : Type) [Field K] (O : ValuationSubring K) (k : ℕ)
    (J : Matrix (Fin k) (Fin k) K) (b c g h : GL (Fin k) K) (Λ Λ' : Submodule O (Fin k → K)),
    GlobalTheory.OverCompare.IsFrame Λ b → GlobalTheory.OverCompare.IsFrame Λ' c →
    (b : Matrix (Fin k) (Fin k) K)ᵀ * J * (c : Matrix (Fin k) (Fin k) K) = 1 →
    (g : Matrix (Fin k) (Fin k) K)ᵀ * J * (h : Matrix (Fin k) (Fin k) K) = J →
    (g ∈ stabGL Λ ↔ h ∈ stabGL Λ') := by
  intro K _ O k J b c g h Λ Λ' hb hc hJ hg
  have hJ' : ((b⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *
      ((c⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = J := by
    have e1 : ((b⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *
        (b : Matrix (Fin k) (Fin k) K)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    calc _ = ((b⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *
          ((b : Matrix (Fin k) (Fin k) K)ᵀ * J * (c : Matrix (Fin k) (Fin k) K)) *
          ((c⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) := by rw [hJ, Matrix.mul_one]
      _ = (((b⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *
          (b : Matrix (Fin k) (Fin k) K)ᵀ) * J * ((c : Matrix (Fin k) (Fin k) K) *
          ((c⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [e1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  have key : ((b⁻¹ * g * b : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *
      ((c⁻¹ * h * c : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = 1 := by
    calc _ = (b : Matrix (Fin k) (Fin k) K)ᵀ * ((g : Matrix (Fin k) (Fin k) K)ᵀ *
          (((b⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *
          ((c⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)) * (h : Matrix (Fin k) (Fin k) K)) *
          (c : Matrix (Fin k) (Fin k) K) := by
          simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hJ', hg, hJ]
  rw [hb.mem_stabGL_iff, hc.mem_stabGL_iff]
  refine ⟨mem_range_bc_of_transpose_mul_eq_one _ _ _ key,
    mem_range_bc_of_transpose_mul_eq_one _ _ _ ?_⟩
  have := congrArg Matrix.transpose key
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this

end GlobalTheory.OverCompare
