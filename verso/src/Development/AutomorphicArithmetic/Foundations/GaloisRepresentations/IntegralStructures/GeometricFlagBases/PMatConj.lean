import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

/- English proof (translation)
Establish `h1 : (P : Matrix (Fin d) (Fin d) L) * ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `h2 : ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) * (P : Matrix (Fin d) (Fin d) L) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Set `e : U ≃ₗ[L] U` to `LinearEquiv.ofLinear (Matrix.toLin b b (P : Matrix (Fin d) (Fin d) L)) (Matrix.toLin b b ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L)) (by rw [← Matrix.toLin_mul b b b, h1, Matrix.toLin_one]) (by rw [← Matrix.toLin_mul b b b, h2, Matrix.toLin_one])`.

Use `⟨b.map e, fun j => ?_⟩` and prove the remaining obligations. Establish `h : e (b j) = ∑ i, (P : Matrix (Fin d) (Fin d) L) i j • b i` using `Matrix.toLin_self b b _ j`. Simplify using `[h]`.
-/
private theorem conj_basis {L : Type} [Field L] {M : Type*} [AddCommGroup M] [Module L M]
    (U : Submodule L M) {d : ℕ} (b : Module.Basis (Fin d) L U) (P : GL (Fin d) L) :
    ∃ b' : Module.Basis (Fin d) L U,
      ∀ j, (b' j).1 = ∑ i, (P : Matrix (Fin d) (Fin d) L) i j • (b i).1 := by
  have h1 : (P : Matrix (Fin d) (Fin d) L) * ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) * (P : Matrix (Fin d) (Fin d) L) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let e : U ≃ₗ[L] U := LinearEquiv.ofLinear (Matrix.toLin b b (P : Matrix (Fin d) (Fin d) L))
    (Matrix.toLin b b ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L))
    (by rw [← Matrix.toLin_mul b b b, h1, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul b b b, h2, Matrix.toLin_one])
  refine ⟨b.map e, fun j => ?_⟩
  have h : e (b j) = ∑ i, (P : Matrix (Fin d) (Fin d) L) i j • b i :=
    Matrix.toLin_self b b _ j
  simp [h]

/- English proof (translation)
Establish `key : ∀ (B : Matrix (Fin d) (Fin d) L) (j : Fin d), ∑ i, B i j • y i = ∑ t, (P * B) t j • x t`. Introduce `B j`. Simplify using `only [hy, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]`.

Rewrite using `[key, show P * (Q * A * P) = A * P by`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul], hy j]`. Simplify using `only [map_sum, map_smul, hx, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]`.
-/
private theorem conj_mat {L : Type} [Field L] {M : Type*} [AddCommGroup M] [Module L M]
    (f : M →ₗ[L] M) {d : ℕ} (x y : Fin d → M) (A P Q : Matrix (Fin d) (Fin d) L) (hPQ : P * Q = 1)
    (hx : ∀ j, f (x j) = ∑ i, A i j • x i) (hy : ∀ j, y j = ∑ i, P i j • x i) (j : Fin d) :
    f (y j) = ∑ i, (Q * A * P) i j • y i := by
  have key : ∀ (B : Matrix (Fin d) (Fin d) L) (j : Fin d),
      ∑ i, B i j • y i = ∑ t, (P * B) t j • x t := by
    intro B j
    simp only [hy, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  rw [key, show P * (Q * A * P) = A * P by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul], hy j]
  simp only [map_sum, map_smul, hx, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]

/- English proof (translation)
Introduce `l _ k _ H Ω _ _ L _ _ θ d ρ P ⟨b, hb⟩`. Take `⟨b', hb'⟩` from `conj_basis _ b P`. Use `⟨b', fun σ j => ?_⟩` and prove the remaining obligations. Establish `h1 : (P : Matrix (Fin d) (Fin d) L) * ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Rewrite using `[cj_apply, Units.val_mul, Units.val_mul]`. Conclude with `conj_mat (galV l H Ω L σ) (fun i => (b i).1) (fun i => (b' i).1) _ _ _ h1 (hb σ) hb' j`.
-/
theorem UpperTheory.Gal.Int.Geo.matConj_of :
    MatConj := by
  intro l _ k _ H Ω _ _ L _ _ θ d ρ P ⟨b, hb⟩
  obtain ⟨b', hb'⟩ := conj_basis _ b P
  refine ⟨b', fun σ j => ?_⟩
  have h1 : (P : Matrix (Fin d) (Fin d) L) * ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [cj_apply, Units.val_mul, Units.val_mul]
  exact conj_mat (galV l H Ω L σ) (fun i => (b i).1) (fun i => (b' i).1) _ _ _ h1 (hb σ) hb' j
