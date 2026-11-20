import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscriminantNormShapesBis

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

def SolveOnto : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → ∀ Y : udPre K 𝔭 k a,
      ∃ Y' P W Z Z₀ : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k),
        Y' - Y.1 = Z₀ * diagQ K 𝔭 k a ∧ P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y' ∧
        Y'ᴴ * diagQ K 𝔭 k a * Y' - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a ∧
        W + Pᴴ * Z + Zᴴ * P + Zᴴ * diagQ K 𝔭 k a * Z = 0

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}

/- English proof (translation)
Establish `h` using `Formalism.HermitianLattices.Ext.L3.localizedQuotients.star_ι (K := K) (F := F) Fact.out x`. Conclude with `FaithfulSMul.algebraMap_injective (𝓞 K) K h`.
-/
private theorem star_algebraMap_ringOfIntegers (x : 𝓞 F) :
    star (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 K) x := by
  have h := Formalism.HermitianLattices.Ext.L3.localizedQuotients.star_ι (K := K) (F := F) Fact.out x
  exact FaithfulSMul.algebraMap_injective (𝓞 K) K h

/- English proof (translation)
Unfold `diagQ`. Rewrite using `[Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.star_apply, star_mk, star_algebraMap_ringOfIntegers]`.
-/
theorem diagQ_conjTranspose (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    (diagQ K 𝔭 k a)ᴴ = diagQ K 𝔭 k a := by
  unfold diagQ
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  rw [Pi.star_apply, star_mk, star_algebraMap_ringOfIntegers]

/- English proof (translation)
Rewrite using `[Matrix.add_mul, hPY, Matrix.mul_add, Matrix.mul_assoc]`.
-/
theorem hom_shift {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : Fin m → 𝓞 F}
    {Y P : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hPY : P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y) (Z : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    (P + diagQ K 𝔭 k a * Z) * diagQ K 𝔭 k a = diagQ K 𝔭 k a * (Y + Z * diagQ K 𝔭 k a) := by
  rw [Matrix.add_mul, hPY, Matrix.mul_add, Matrix.mul_assoc]

/- English proof (translation)
Establish `hH` using `diagQ_conjTranspose (K := K) 𝔭 k a`. Establish `h1 : Yᴴ * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Pᴴ`. Establish `h` using `congrArg Matrix.conjTranspose hPY`. Rewrite `h` using `[conjTranspose_mul, conjTranspose_mul, hH]`. Conclude with `h.symm`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_add, conjTranspose_mul, hH, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Use `_ = _ := by`. Rewrite using `[hW, h1, ← hPY]`.

Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]`.
-/
theorem form_shift {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : Fin m → 𝓞 F}
    {Y P W : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hPY : P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y)
    (hW : Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a)
    (Z : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    (Y + Z * diagQ K 𝔭 k a)ᴴ * diagQ K 𝔭 k a * (Y + Z * diagQ K 𝔭 k a) - diagQ K 𝔭 k a =
      diagQ K 𝔭 k a * (W + Pᴴ * Z + Zᴴ * P + Zᴴ * diagQ K 𝔭 k a * Z) * diagQ K 𝔭 k a := by
  have hH := diagQ_conjTranspose (K := K) 𝔭 k a
  have h1 : Yᴴ * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Pᴴ := by
    have h := congrArg Matrix.conjTranspose hPY
    rw [conjTranspose_mul, conjTranspose_mul, hH] at h
    exact h.symm
  calc _ = Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a + Yᴴ * diagQ K 𝔭 k a * Z * diagQ K 𝔭 k a + diagQ K 𝔭 k a * Zᴴ * (diagQ K 𝔭 k a * Y) +
        diagQ K 𝔭 k a * Zᴴ * diagQ K 𝔭 k a * Z * diagQ K 𝔭 k a := by
        simp only [conjTranspose_add, conjTranspose_mul, hH, Matrix.add_mul, Matrix.mul_add,
          Matrix.mul_assoc]
        abel
    _ = _ := by
        rw [hW, h1, ← hPY]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]

/- English proof (translation)
Simplify using `only [conjTranspose_add, conjTranspose_mul, diagQ_conjTranspose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws.
-/
theorem eq_shift {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : Fin m → 𝓞 F}
    (P W Z Z' : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    W + Pᴴ * (Z + Z') + (Z + Z')ᴴ * P + (Z + Z')ᴴ * diagQ K 𝔭 k a * (Z + Z') =
      (W + Pᴴ * Z + Zᴴ * P + Zᴴ * diagQ K 𝔭 k a * Z) + (P + diagQ K 𝔭 k a * Z)ᴴ * Z' +
        Z'ᴴ * (P + diagQ K 𝔭 k a * Z) + Z'ᴴ * diagQ K 𝔭 k a * Z' := by
  simp only [conjTranspose_add, conjTranspose_mul, diagQ_conjTranspose, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_assoc]
  abel

/- English proof (translation)
Use `show (Y + Z * diagQ K 𝔭 k a)ᴴ * diagQ K 𝔭 k a * (Y + Z * diagQ K 𝔭 k a) = diagQ K 𝔭 k a`. Establish `h` using `form_shift hPY hW Z`. Rewrite `h` using `[hZ, Matrix.mul_zero, Matrix.zero_mul]`. Conclude with `sub_eq_zero.mp h`.
-/
theorem mem_skSet_of_solve {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : Fin m → 𝓞 F}
    {Y P W Z : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hPY : P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y)
    (hW : Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a)
    (hZ : W + Pᴴ * Z + Zᴴ * P + Zᴴ * diagQ K 𝔭 k a * Z = 0) :
    Y + Z * diagQ K 𝔭 k a ∈ skSet K 𝔭 k a := by
  show (Y + Z * diagQ K 𝔭 k a)ᴴ * diagQ K 𝔭 k a * (Y + Z * diagQ K 𝔭 k a) = diagQ K 𝔭 k a
  have h := form_shift hPY hW Z
  rw [hZ, Matrix.mul_zero, Matrix.zero_mul] at h
  exact sub_eq_zero.mp h

/- English proof (translation)
Introduce `K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk Y`. Take `⟨Y', P, W, Z, Z₀, hY, hPY, hW, hZ⟩` from `hS K F hK 𝔭 h𝔭 m a ha k hk Y`. Use `⟨Y' + Z * diagQ K 𝔭 k a, mem_skSet_of_solve hPY hW hZ, Z₀ + Z, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.add_mul, ← hY]`. Normalize the expressions using the abelian group laws.
-/
theorem liftOnto_of_solve (hS : SolveOnto) : LiftOnto := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk Y
  obtain ⟨Y', P, W, Z, Z₀, hY, hPY, hW, hZ⟩ := hS K F hK 𝔭 h𝔭 m a ha k hk Y
  refine ⟨Y' + Z * diagQ K 𝔭 k a, mem_skSet_of_solve hPY hW hZ, Z₀ + Z, ?_⟩
  rw [Matrix.add_mul, ← hY]
  abel

/- English proof (translation)
The claim follows from `discOnto_of_lift hU (liftOnto_of_solve hS)`.
-/
theorem discOnto_of_solve (hU : UDModel) (hS : SolveOnto) : DiscOnto :=
  discOnto_of_lift hU (liftOnto_of_solve hS)

end Formalism.L2.SG.Pf.discriminantNormShapes
