import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalRationalTranslate
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J j m C D Z J₀ fr u`. Establish `hmap : ∀ {a b c : ℕ} (X : Matrix (Fin a) (Fin b) E) (Y : Matrix (Fin b) (Fin c) E), adMat F (X * Y) = adMat F X * adMat F Y` using `fun X Y => by`. Simplify using `only [adMat]`. Conclude with `Matrix.map_mul`. Establish `hsub : adMat F ((1 : Matrix (Fin n) (Fin n) E) - D * (cT (σ : E →+* E) C * J)) = adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J))`.

Establish `e : (1 : Matrix (Fin n) (Fin n) E) - D * (cT (σ : E →+* E) C * J) = C * (cT (σ : E →+* E) D * J) + Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J))`. Rewrite using `[← fr.sum]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, ← hmap, ← hmap]`. Simplify using `only [adMat]`.

Conclude with `Matrix.map_add _ (map_add _) _ _`. Establish `hZ : ((1 : Matrix (Fin n) (Fin n) E) - D * (cT (σ : E →+* E) C * J)) * Z = Z`. Rewrite using `[Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, fr.cz, Matrix.mul_zero, sub_zero]`. Rewrite using `[GlobalTheory.EisCT.mem_unipRad_iff_dual fr.cd u]`. Use `set M := (matHom _ σ J u).1`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, B, h2⟩`. Use `⟨by rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1; exact h1, B * adMat F Z, ?_⟩` and prove the remaining obligations. Use `congrArg (· * adMat F Z) h2` as an intermediate fact. Rewrite `this` using `[Matrix.mul_assoc, ← hmap, hZ, Matrix.mul_assoc]`.

Rewrite `this` using `[Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add]`. Rewrite using `[this, add_comm]`. Introduce and unpack `⟨h1, b, h2⟩`. Use `⟨by rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_self], b * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)), ?_⟩` and prove the remaining obligations. Establish `h1' : (M - 1) * adMat F C = 0` using `by rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_self]`.

Establish `h2' : (M - 1) * adMat F Z = adMat F C * b` using `by rw [Matrix.sub_mul, Matrix.one_mul, h2]; abel`. Rewrite using `[hsub, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1', h2', Matrix.zero_mul, zero_add, Matrix.mul_assoc]`.
-/
theorem mem_unipRad_iff_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ u : GAd σ J, u ∈ unipRad σ J C ↔ ((matHom _ σ J u).1 * adMat F C = adMat F C ∧ ∃ b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), (matHom _ σ J u).1 * adMat F Z = adMat F Z + adMat F C * b) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ fr u
  have hmap : ∀ {a b c : ℕ} (X : Matrix (Fin a) (Fin b) E) (Y : Matrix (Fin b) (Fin c) E),
      adMat F (X * Y) = adMat F X * adMat F Y := fun X Y => by
    simp only [adMat]; exact Matrix.map_mul
  have hsub : adMat F ((1 : Matrix (Fin n) (Fin n) E) - D * (cT (σ : E →+* E) C * J)) =
      adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) := by
    have e : (1 : Matrix (Fin n) (Fin n) E) - D * (cT (σ : E →+* E) C * J) =
        C * (cT (σ : E →+* E) D * J) + Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) := by
      rw [← fr.sum]; abel
    rw [e, ← hmap, ← hmap]
    simp only [adMat]; exact Matrix.map_add _ (map_add _) _ _
  have hZ : ((1 : Matrix (Fin n) (Fin n) E) - D * (cT (σ : E →+* E) C * J)) * Z = Z := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, fr.cz, Matrix.mul_zero, sub_zero]
  rw [GlobalTheory.EisCT.mem_unipRad_iff_dual fr.cd u]
  set M := (matHom _ σ J u).1
  constructor
  · rintro ⟨h1, B, h2⟩
    refine ⟨by rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1; exact h1, B * adMat F Z, ?_⟩
    have := congrArg (· * adMat F Z) h2
    rw [Matrix.mul_assoc, ← hmap, hZ, Matrix.mul_assoc] at this
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add] at this
    rw [this, add_comm]
  · rintro ⟨h1, b, h2⟩
    refine ⟨by rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_self], b * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)), ?_⟩
    have h1' : (M - 1) * adMat F C = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_self]
    have h2' : (M - 1) * adMat F Z = adMat F C * b := by rw [Matrix.sub_mul, Matrix.one_mul, h2]; abel
    rw [hsub, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1', h2', Matrix.zero_mul, zero_add, Matrix.mul_assoc]

end GlobalTheory.SphEis
