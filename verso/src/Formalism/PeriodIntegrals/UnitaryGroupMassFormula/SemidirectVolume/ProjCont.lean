import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjHA

noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

/- English proof (translation)
Replace the relevant objects with their definitions. Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem toMatrix'_lin (g : HA R σ J) :
    LinearMap.toMatrix' (lin R σ J g) =
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
  unfold Formalism.L2.SG.Sub.lin
  first
    | exact LinearMap.toMatrix'_mulVecLin _
    | exact LinearMap.toMatrix'_toLin' _
    | (ext i j; simp [LinearMap.toMatrix'_apply, Matrix.mulVec, dotProduct, Pi.single_apply])

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem piMat_eq (g : HA R σ J) :
    piMat (P := P) (T := T) g = LinearMap.toMatrix' (datR R σ J P T).pU +
      LinearMap.toMatrix' (datR R σ J P T).pW *
        ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
          LinearMap.toMatrix' (datR R σ J P T).pW := by
  simp only [piMat, PG.Dat.Pi, map_add, LinearMap.toMatrix'_comp, toMatrix'_lin, Matrix.mul_assoc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_inv (g : HA R σ J) : HA.mat R σ J g⁻¹ = (HA.mat R σ J g)⁻¹ := rfl

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem continuous_piMat_inv [TopologicalSpace R] [IsTopologicalRing (R ⊗[F] E)] :
    Continuous fun g : HA R σ J => piMat (P := P) (T := T) g⁻¹ := by
  have hm : Continuous fun g : HA R σ J =>
      (((HA.mat R σ J g)⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  simp only [piMat_eq, mat_inv]
  exact continuous_const.add ((continuous_const.matrix_mul hm).matrix_mul continuous_const)

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem continuous_piMat [TopologicalSpace R] [IsTopologicalRing (R ⊗[F] E)] :
    Continuous fun g : HA R σ J => piMat (P := P) (T := T) g := by
  have hm : Continuous fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  simp only [piMat_eq]
  exact continuous_const.add ((continuous_const.matrix_mul hm).matrix_mul continuous_const)

variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem continuous_piG [TopologicalSpace R] [IsTopologicalRing (R ⊗[F] E)] :
    Continuous fun s : S0 R σ J P => piG hσσ hJ hP (s : HA R σ J) s.2 := by
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  exact ⟨(continuous_piMat (P := P) (T := T)).comp continuous_subtype_val,
    (continuous_piMat_inv (P := P) (T := T)).comp continuous_subtype_val⟩

end Cont

end PI.VolSemiDirect.W
