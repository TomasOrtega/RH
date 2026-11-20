import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J j m C D Z J₀ hF g C' D' Z' hC hZ hD`. Establish `hinj : Function.Injective (inclR (F` using `F) (E := E) (AF F)) := Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)`. Simplify using `only [adMat] at hC hZ hD`. Use `set ι := inclR (F := F) (E := E) (AF F) with hι`. Use `set x : Matrix (Fin n) (Fin n) E := C' * (cT (σ : E →+* E) D * J) + Z' * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + D' * (cT (σ : E →+* E) C * J) with hx`.

Establish `hM : (matHom _ σ J g).1 = x.map ι`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hF.sum, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]`. Use `_ = x.map ι := by`. Rewrite using `[hx]`.

Simplify using `only [Matrix.map_add _ (map_add ι), Matrix.map_mul, Matrix.mul_add, ← Matrix.mul_assoc]`. Rewrite using `[hC, hZ, hD]`. Establish `hdet : x.det ≠ 0` using `by haveI : Nontrivial (AF F ⊗[F] E) := ⟨⟨ι 0, ι 1, fun e => zero_ne_one (hinj e)⟩⟩`. Introduce `h0`. Establish `hu : IsUnit (x.map ι).det`.

Rewrite using `[← hM]`. Conclude with `Matrix.isUnits_det_units _`. Establish `h1` using `ι.map_det x`. Rewrite `h1` using `[h0, map_zero, RingHom.mapMatrix_apply]`. Rewrite `hu` using `[← h1]`.

Conclude with `not_isUnit_zero hu`. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero x hdet, ?_, Units.ext hM.symm⟩` and prove the remaining obligations. Use `show cT (σ : E →+* E) x * J * x = J`. Apply `Matrix.map_injective hinj` to reduce the goal to its premises. Establish `hg : cT (sigR (AF F) σ) (matHom _ σ J g).1 * JR (AF F) J * (matHom _ σ J g).1 = JR (AF F) J` using `g.2`.

Establish `hcT : cT (sigR (AF F) σ) (x.map ι) = (cT (σ : E →+* E) x).map ι`. Use extensionality with `a b`. Simplify using `[Formalism.UG.cT, sigR, hι, inclR]`. Rewrite `hg` using `[hM, hcT, JR, ← hι, ← Matrix.map_mul, ← Matrix.map_mul]`. Conclude with `hg`.
-/
theorem mem_ratPts_of_cols_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (g : GAd σ J) (C' D' : Matrix (Fin n) (Fin j) E) (Z' : Matrix (Fin n) (Fin m) E), (matHom _ σ J g).1 * adMat F C = adMat F C' → (matHom _ σ J g).1 * adMat F Z = adMat F Z' → (matHom _ σ J g).1 * adMat F D = adMat F D' → g ∈ ratPts σ J := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF g C' D' Z' hC hZ hD
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)
  dsimp only [adMat] at hC hZ hD
  set ι := inclR (F := F) (E := E) (AF F) with hι
  set x : Matrix (Fin n) (Fin n) E := C' * (cT (σ : E →+* E) D * J) + Z' * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
    D' * (cT (σ : E →+* E) C * J) with hx
  have hM : (matHom _ σ J g).1 = x.map ι := by
    calc (matHom _ σ J g).1
        = (matHom _ σ J g).1 * (C * (cT (σ : E →+* E) D * J) + Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
            D * (cT (σ : E →+* E) C * J)).map ι := by
          rw [hF.sum, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
      _ = x.map ι := by
          rw [hx]
          simp only [Matrix.map_add _ (map_add ι), Matrix.map_mul, Matrix.mul_add, ← Matrix.mul_assoc]
          rw [hC, hZ, hD]
  have hdet : x.det ≠ 0 := by
    haveI : Nontrivial (AF F ⊗[F] E) := ⟨⟨ι 0, ι 1, fun e => zero_ne_one (hinj e)⟩⟩
    intro h0
    have hu : IsUnit (x.map ι).det := by
      rw [← hM]; exact Matrix.isUnits_det_units _
    have h1 := ι.map_det x
    rw [h0, map_zero, RingHom.mapMatrix_apply] at h1
    rw [← h1] at hu
    exact not_isUnit_zero hu
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero x hdet, ?_, Units.ext hM.symm⟩
  show cT (σ : E →+* E) x * J * x = J
  apply Matrix.map_injective hinj
  have hg : cT (sigR (AF F) σ) (matHom _ σ J g).1 * JR (AF F) J * (matHom _ σ J g).1 = JR (AF F) J := g.2
  have hcT : cT (sigR (AF F) σ) (x.map ι) = (cT (σ : E →+* E) x).map ι := by
    ext a b; simp [Formalism.UG.cT, sigR, hι, inclR]
  rw [hM, hcT, JR, ← hι, ← Matrix.map_mul, ← Matrix.map_mul] at hg
  exact hg

end GlobalTheory.SphEis
