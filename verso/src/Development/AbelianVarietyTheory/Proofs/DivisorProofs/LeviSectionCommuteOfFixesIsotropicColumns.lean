import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFrameCols
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv α x hx`. Take `⟨hxC, hxD⟩` from `Subgroup.mem_inf.mp hx`. Establish `hC : (matHom _ σ J x).1 * adMat F C = adMat F C` using `hxC`. Establish `hD : (matHom _ σ J x).1 * adMat F D = adMat F D` using `hxD`. Establish `formOf : ∀ (K : Matrix (Fin n) (Fin j) E), x⁻¹ ∈ fixG σ J K → adMat F (cT (σ : E →+* E) K * J) * (matHom _ σ J x).1 = adMat F (cT (σ : E →+* E) K * J)`.

Introduce `K hK`. Establish `h1 : (matHom _ σ J x⁻¹).1 * adMat F K = adMat F K * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))`. Rewrite using `[Matrix.mul_one]`. Conclude with `hK`. Use `form_mul_of_mul_cols h1` as an intermediate fact.

Rewrite `this` using `[inv_inv, Formalism.UG.cT_one, Matrix.one_mul]`. Then use the resulting hypothesis. Establish `fC` using `formOf C ((fixG σ J C).inv_mem hxC)`. Establish `fD` using `formOf D ((fixG σ J D).inv_mem hxD)`. Use `set X := (matHom _ σ J x).1 with hX`. Establish `hZ : X * adMat F Z = adMat F Z * (adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * X * adMat F Z)`.

Establish `h1 : adMat F (1 : Matrix (Fin n) (Fin n) E) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `e : X * adMat F Z = adMat F (C * (cT (σ : E →+* E) D * J) + Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + D * (cT (σ : E →+* E) C * J)) * X * adMat F Z`. Rewrite using `[hF.sum, h1, Matrix.one_mul]`. Establish `z1 : adMat F (cT (σ : E →+* E) D * J) * X * adMat F Z = 0`. Rewrite using `[fD, adMat, adMat, ← Matrix.map_mul, hF.dz, Matrix.map_zero _ (map_zero _)]`.

Establish `z2 : adMat F (cT (σ : E →+* E) C * J) * X * adMat F Z = 0`. Rewrite using `[fC, adMat, adMat, ← Matrix.map_mul, hF.cz, Matrix.map_zero _ (map_zero _)]`. Establish `hadd : ∀ {p : ℕ} (A B : Matrix (Fin n) (Fin p) E), adMat F (A + B) = adMat F A + adMat F B` using `fun A B => Matrix.map_add _ (map_add _) A B`. Establish `hmul : ∀ {p : ℕ} (A : Matrix (Fin n) (Fin p) E) (B : Matrix (Fin p) (Fin n) E), adMat F (A * B) = adMat F A * adMat F B` using `fun A B => Matrix.map_mul`. Rewrite using `[e, hadd, hadd, hmul, hmul, hmul, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc (adMat F C), Matrix.mul_assoc (adMat F C), z1, Matrix.mul_assoc (adMat F D), Matrix.mul_assoc (adMat F D), z2, Matrix.mul_zero, Matrix.mul_zero, zero_add, add_zero, …`.

Apply `eq_of_frame_cols F E σ n J j m C D Z J₀ hF` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, hlv.onC, ← hX, hC, ← Matrix.mul_assoc, hC, hlv.onC]`. Rewrite using `[map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, hlv.onZ, ← hX, hZ, ← Matrix.mul_assoc, hlv.onZ]`. Rewrite using `[map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, hlv.onD, ← hX, hD, ← Matrix.mul_assoc, hD, hlv.onD]`.
-/
theorem lv_comm_of_fix_cols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ α, ∀ x ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)), lv α * x = x * lv α := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv α x hx
  obtain ⟨hxC, hxD⟩ := Subgroup.mem_inf.mp hx
  have hC : (matHom _ σ J x).1 * adMat F C = adMat F C := hxC
  have hD : (matHom _ σ J x).1 * adMat F D = adMat F D := hxD
  have formOf : ∀ (K : Matrix (Fin n) (Fin j) E), x⁻¹ ∈ fixG σ J K →
      adMat F (cT (σ : E →+* E) K * J) * (matHom _ σ J x).1 = adMat F (cT (σ : E →+* E) K * J) := by
    intro K hK
    have h1 : (matHom _ σ J x⁻¹).1 * adMat F K = adMat F K * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]; exact hK
    have := form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at this
  have fC := formOf C ((fixG σ J C).inv_mem hxC)
  have fD := formOf D ((fixG σ J D).inv_mem hxD)
  set X := (matHom _ σ J x).1 with hX
  have hZ : X * adMat F Z = adMat F Z * (adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * X * adMat F Z) := by
    have h1 : adMat F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    have e : X * adMat F Z = adMat F (C * (cT (σ : E →+* E) D * J) +
        Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + D * (cT (σ : E →+* E) C * J)) * X * adMat F Z := by
      rw [hF.sum, h1, Matrix.one_mul]
    have z1 : adMat F (cT (σ : E →+* E) D * J) * X * adMat F Z = 0 := by
      rw [fD, adMat, adMat, ← Matrix.map_mul, hF.dz, Matrix.map_zero _ (map_zero _)]
    have z2 : adMat F (cT (σ : E →+* E) C * J) * X * adMat F Z = 0 := by
      rw [fC, adMat, adMat, ← Matrix.map_mul, hF.cz, Matrix.map_zero _ (map_zero _)]
    have hadd : ∀ {p : ℕ} (A B : Matrix (Fin n) (Fin p) E), adMat F (A + B) = adMat F A + adMat F B :=
      fun A B => Matrix.map_add _ (map_add _) A B
    have hmul : ∀ {p : ℕ} (A : Matrix (Fin n) (Fin p) E) (B : Matrix (Fin p) (Fin n) E),
        adMat F (A * B) = adMat F A * adMat F B := fun A B => Matrix.map_mul
    rw [e, hadd, hadd, hmul, hmul, hmul, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul,
      Matrix.mul_assoc (adMat F C), Matrix.mul_assoc (adMat F C), z1, Matrix.mul_assoc (adMat F D),
      Matrix.mul_assoc (adMat F D), z2, Matrix.mul_zero, Matrix.mul_zero, zero_add, add_zero,
      Matrix.mul_assoc (adMat F Z), Matrix.mul_assoc (adMat F Z)]
  apply eq_of_frame_cols F E σ n J j m C D Z J₀ hF
  · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, hlv.onC, ← hX, hC,
      ← Matrix.mul_assoc, hC, hlv.onC]
  · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, hlv.onZ, ← hX, hZ,
      ← Matrix.mul_assoc, hlv.onZ]
  · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, hlv.onD, ← hX, hD,
      ← Matrix.mul_assoc, hD, hlv.onD]

end GlobalTheory.SphEis
