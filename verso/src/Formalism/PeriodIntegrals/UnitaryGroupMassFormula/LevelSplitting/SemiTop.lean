import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.MulInvPiGMemN
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.SemidirectExistsOfParts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

noncomputable section

namespace PI.LevelKSplit.W.SemiT

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.LevelKSplit.W.SemiA PI.VolSemiDirect.W
open scoped TensorProduct

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] {R : Type}
  [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

/- English proof (translation)
Rewrite using `[piMat, PI.LevelKSplit.W.SemiG.Dat.Pi, map_add, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, lin, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', Matrix.mul_assoc]`.
-/
theorem piMat_eq (g : HA R σ J) :
    piMat (P := P) (T := T) g = LinearMap.toMatrix' (datR R σ J P T).pU +
      LinearMap.toMatrix' (datR R σ J P T).pW *
        ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
          LinearMap.toMatrix' (datR R σ J P T).pW := by
  rw [piMat, PI.LevelKSplit.W.SemiG.Dat.Pi, map_add, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_comp, lin, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', Matrix.mul_assoc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_inv (g : HA R σ J) : HA.mat R σ J g⁻¹ = (HA.mat R σ J g)⁻¹ := rfl

/- English proof (translation)
Establish `hm : Continuous fun g : HA R σ J => ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))` using `Units.continuous_val.comp continuous_subtype_val`. Establish `he : (fun g : HA R σ J => piMat (P` using `P) (T := T) g) = fun g => LinearMap.toMatrix' (datR R σ J P T).pU + LinearMap.toMatrix' (datR R σ J P T).pW * ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * LinearMap.toMatrix' (datR R σ J P T).pW := funext piMat_eq`. Rewrite using `[he]`. Conclude with `continuous_const.add ((continuous_const.matrix_mul hm).matrix_mul continuous_const)`.
-/
theorem continuous_piMat : Continuous fun g : HA R σ J => piMat (P := P) (T := T) g := by
  have hm : Continuous fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  have he : (fun g : HA R σ J => piMat (P := P) (T := T) g) = fun g =>
      LinearMap.toMatrix' (datR R σ J P T).pU + LinearMap.toMatrix' (datR R σ J P T).pW *
        ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
          LinearMap.toMatrix' (datR R σ J P T).pW := funext piMat_eq
  rw [he]
  exact continuous_const.add ((continuous_const.matrix_mul hm).matrix_mul continuous_const)

/- English proof (translation)
Conclude with `(continuous_piMat (P := P) (T := T)).comp continuous_inv`.
-/
theorem continuous_piMat_inv : Continuous fun g : HA R σ J => piMat (P := P) (T := T) g⁻¹ := by
  exact (continuous_piMat (P := P) (T := T)).comp continuous_inv

variable (R) in

def fwdM (hP : P.IsStd σ J T) (p : Nsub R σ J P × Hsub R σ J P) : Ssub R σ J P :=
  ⟨(p.1 : HA R σ J) * (p.2 : HA R σ J), (Ssub R σ J P).mul_mem (N_le_S' (R := R) hP p.1.2) (H_le_S p.2.2)⟩

/- English proof (translation)
Apply `continuous_induced_rng.2` to reduce the goal to its premises. Conclude with `(continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)`.
-/
theorem continuous_fwdM (hP : P.IsStd σ J T) : Continuous (fwdM R hP) := by
  apply continuous_induced_rng.2
  exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

/- English proof (translation)
Apply `continuous_induced_rng.2` to reduce the goal to its premises. Use `Units.continuous_iff.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `(continuous_piMat (P := P) (T := T)).comp continuous_subtype_val`. Conclude with `(continuous_piMat_inv (P := P) (T := T)).comp continuous_subtype_val`.
-/
theorem continuous_piG : Continuous fun s : Ssub R σ J P => piG hσσ hJ hP (s : HA R σ J) s.2 := by
  apply continuous_induced_rng.2
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_piMat (P := P) (T := T)).comp continuous_subtype_val
  · exact (continuous_piMat_inv (P := P) (T := T)).comp continuous_subtype_val

variable (R) in

def bwdM (s : Ssub R σ J P) : Nsub R σ J P × Hsub R σ J P :=
  (⟨(s : HA R σ J) * (piG (R := R) hσσ hJ hP (s : HA R σ J) s.2)⁻¹, mul_inv_piG_mem_N hσσ hJ hP s.2⟩,
    ⟨piG (R := R) hσσ hJ hP (s : HA R σ J) s.2, piG_mem_H hσσ hJ hP (s : HA R σ J) s.2⟩)

/- English proof (translation)
Establish `hpi` using `continuous_piG (R := R) hσσ hJ hP`. Use `Continuous.prodMk ?_ ?_` and prove the remaining obligations. Apply `continuous_induced_rng.2` to reduce the goal to its premises. Conclude with `continuous_subtype_val.mul hpi.inv`. Apply `continuous_induced_rng.2` to reduce the goal to its premises.

Conclude with `hpi`.
-/
theorem continuous_bwdM : Continuous (bwdM R hσσ hJ hP) := by
  have hpi := continuous_piG (R := R) hσσ hJ hP
  refine Continuous.prodMk ?_ ?_
  · apply continuous_induced_rng.2
    exact continuous_subtype_val.mul hpi.inv
  · apply continuous_induced_rng.2
    exact hpi

/- English proof (translation)
Introduce and unpack `⟨n, h⟩`. Establish `hnS` using `N_le_S' (R := R) hP n.2`. Establish `hhS` using `H_le_S (R := R) h.2`. Establish `key : piG (R` using `R) hσσ hJ hP ((n : HA R σ J) * (h : HA R σ J)) ((Ssub R σ J P).mul_mem hnS hhS) = h := by`. Rewrite using `[piG_mul hσσ hJ hP hnS hhS, piG_of_N hσσ hJ hP n.2 hnS, piG_of_H hσσ hJ hP h.2 hhS, one_mul]`.

Use `Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)` and prove the remaining obligations. Use `show (n : HA R σ J) * (h : HA R σ J) * (piG (R := R) hσσ hJ hP ((n : HA R σ J) * (h : HA R σ J)) _)⁻¹ = n`. Rewrite using `[key, mul_inv_cancel_right]`. Conclude with `key`.
-/
theorem bwd_fwd : Function.LeftInverse (bwdM R hσσ hJ hP) (fwdM R hP) := by
  rintro ⟨n, h⟩
  have hnS := N_le_S' (R := R) hP n.2
  have hhS := H_le_S (R := R) h.2
  have key : piG (R := R) hσσ hJ hP ((n : HA R σ J) * (h : HA R σ J))
      ((Ssub R σ J P).mul_mem hnS hhS) = h := by
    rw [piG_mul hσσ hJ hP hnS hhS, piG_of_N hσσ hJ hP n.2 hnS, piG_of_H hσσ hJ hP h.2 hhS, one_mul]
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · show (n : HA R σ J) * (h : HA R σ J) *
      (piG (R := R) hσσ hJ hP ((n : HA R σ J) * (h : HA R σ J)) _)⁻¹ = n
    rw [key, mul_inv_cancel_right]
  · exact key

/- English proof (translation)
Introduce `s`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `inv_mul_cancel_right _ _`.
-/
theorem fwd_bwd : Function.RightInverse (bwdM R hσσ hJ hP) (fwdM R hP) := by
  intro s
  apply Subtype.ext
  exact inv_mul_cancel_right _ _

variable (R) in

def homeoNH : (Nsub R σ J P × Hsub R σ J P) ≃ₜ Ssub R σ J P where
  toFun := fwdM R hP
  invFun := bwdM R hσσ hJ hP
  left_inv := bwd_fwd hσσ hJ hP
  right_inv := fwd_bwd hσσ hJ hP
  continuous_toFun := continuous_fwdM hP
  continuous_invFun := continuous_bwdM (R := R) hσσ hJ hP

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ hh _ hn => norm_N hh hn, homeoNH R hσσ hJ hP, fun _ => rfl⟩`.
-/
theorem semi_gen : Semi (Ssub R σ J P) (Nsub R σ J P) (Hsub R σ J P) :=
  ⟨fun _ hh _ hn => norm_N hh hn, homeoNH R hσσ hJ hP, fun _ => rfl⟩

end Cont

/- English proof (translation)
Unfold `PI.LevelKSplit.W.ExS.SemiNHSAll PI.LevelKSplit.ForAllCM PI.LevelKSplit.W.ExS.SemiNHS`. Introduce `F E _ _ _ _ _ σ _ M J _ hJ hσσ r P T hP`. Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Conclude with `semi_gen hσσ hJ hP`.
-/
theorem semidirect_topological_all : PI.LevelKSplit.W.ExS.SemiNHSAll := by
  unfold PI.LevelKSplit.W.ExS.SemiNHSAll PI.LevelKSplit.ForAllCM PI.LevelKSplit.W.ExS.SemiNHS
  intro F E _ _ _ _ _ σ _ M J _ hJ hσσ r P T hP
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact semi_gen hσσ hJ hP

end PI.LevelKSplit.W.SemiT
