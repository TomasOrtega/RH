import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.KUni

variable {D : D7} {V : HSp D}

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv hB`.
-/
theorem inv_eq {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : B⁻¹ = Bᴴ * G :=
  Matrix.inv_eq_left_inv hB

/- English proof (translation)
Rewrite using `[inv_eq hB]`. Conclude with `mul_eq_one_comm.mp hB`.
-/
theorem mul_inv' {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : B * B⁻¹ = 1 := by
  rw [inv_eq hB]; exact mul_eq_one_comm.mp hB

/- English proof (translation)
Rewrite using `[inv_eq hB]`. Conclude with `hB`.
-/
theorem inv_mul' {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : B⁻¹ * B = 1 := by
  rw [inv_eq hB]; exact hB

/- English proof (translation)
Establish `h` using `congrArg Matrix.conjTranspose hB`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at h`. Conclude with `mul_eq_one_comm.mp h`.
-/
theorem gB {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : Gᴴ * B * Bᴴ = 1 := by
  have h := congrArg Matrix.conjTranspose hB
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at h
  exact mul_eq_one_comm.mp h

/- English proof (translation)
Rewrite using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, inv_eq hB]`. Establish `e : (Bᴴ * G * g * B)ᴴ * (Bᴴ * G * g * B) = Bᴴ * gᴴ * (Gᴴ * B * Bᴴ) * G * g * B`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]`. Rewrite using `[e, gB hB, Matrix.mul_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem conj_unitary {G B g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) (hg : gᴴ * G * g = G) :
    B⁻¹ * g * B ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, inv_eq hB]
  have e : (Bᴴ * G * g * B)ᴴ * (Bᴴ * G * g * B) = Bᴴ * gᴴ * (Gᴴ * B * Bᴴ) * G * g * B := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, gB hB, Matrix.mul_one]
  calc Bᴴ * gᴴ * G * g * B = Bᴴ * (gᴴ * G * g) * B := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, hB]

/- English proof (translation)
Rewrite `hu` using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]`. Rewrite using `[inv_eq hB]`. Establish `e : (B * u * (Bᴴ * G))ᴴ * G * (B * u * (Bᴴ * G)) = Gᴴ * B * uᴴ * (Bᴴ * G * B) * u * Bᴴ * G`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]`. Rewrite using `[e, hB, Matrix.mul_one]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem back_unitary {G B u : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1)
    (hu : u ∈ Matrix.unitaryGroup (Fin V.rank) ℂ) : (B * u * B⁻¹)ᴴ * G * (B * u * B⁻¹) = G := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
  rw [inv_eq hB]
  have e : (B * u * (Bᴴ * G))ᴴ * G * (B * u * (Bᴴ * G)) = Gᴴ * B * uᴴ * (Bᴴ * G * B) * u * Bᴴ * G := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, hB, Matrix.mul_one]
  calc Gᴴ * B * uᴴ * u * Bᴴ * G = Gᴴ * B * (uᴴ * u) * Bᴴ * G := by simp only [Matrix.mul_assoc]
    _ = (Gᴴ * B * Bᴴ) * G := by rw [hu, Matrix.mul_one]
    _ = G := by rw [gB hB, Matrix.one_mul]

open Formalism.IndefR.Eqv in

/- English proof (translation)
Establish `hsum : ∀ x : AE D, psiT D τ x = ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D) ((basAF D).repr x c)) * psiT D τ (basAF D c)`. Introduce `x`. Use `conv_lhs => rw [← (basAF D).sum_repr x]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def, map_mul]`. Establish `hc : ∀ c, Continuous fun x : AE D => (basAF D).repr x c` using `fun c => (continuous_apply c).comp (G5.tensCoordH (basE D) (AF D.host.F)).continuous`. Establish `halg : Continuous fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a)`. Establish `e : (fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a)) = fun a => thetaC D τ ((fstA D.host.F a) ⊗ₜ[D.host.F] (1 : D.host.E))`. Use function extensionality and compare the values at `a`.

Simplify using `only [psiT, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, infPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `((isInfFam_thetaC D) τ).2.comp continuous_fst`. Establish `hfun : (⇑(psiT D τ) : AE D → ℂ) = fun x => ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D) ((basAF D).repr x c)) * psiT D τ (basAF D c)` using `funext hsum`.

Rewrite using `[hfun]`. Conclude with `continuous_finset_sum _ fun c _ => (halg.comp (hc c)).mul continuous_const`.
-/
theorem psiT_continuous (τ : D.what₂.Tau) : Continuous (psiT D τ) := by
  have hsum : ∀ x : AE D, psiT D τ x = ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D) ((basAF D).repr x c)) *
      psiT D τ (basAF D c) := by
    intro x
    conv_lhs => rw [← (basAF D).sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Algebra.smul_def, map_mul]
  have hc : ∀ c, Continuous fun x : AE D => (basAF D).repr x c := fun c =>
    (continuous_apply c).comp (G5.tensCoordH (basE D) (AF D.host.F)).continuous
  have halg : Continuous fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a) := by
    have e : (fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a)) =
        fun a => thetaC D τ ((fstA D.host.F a) ⊗ₜ[D.host.F] (1 : D.host.E)) := by
      funext a
      simp only [psiT, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, infPart,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one]
      rfl
    rw [e]
    exact ((isInfFam_thetaC D) τ).2.comp continuous_fst
  have hfun : (⇑(psiT D τ) : AE D → ℂ) = fun x => ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D)
      ((basAF D).repr x c)) * psiT D τ (basAF D c) := funext hsum
  rw [hfun]
  exact continuous_finset_sum _ fun c _ => (halg.comp (hc c)).mul continuous_const

open Formalism.IndefR.Eqv in
/- English proof (translation)
Rewrite using `[infMat_thetaC]`. Both sides reduce to the same expression.
-/
theorem inB_eq (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V) (τ : D.what₂.Tau) :
    inB (thetaC D) V B g τ = (B τ)⁻¹ * infMat D.sp.cm.sig V.gram (thetaC D τ) g * B τ := by
  rw [infMat_thetaC]; rfl

end GlobalTheory.SeeSaw.KUni

open GlobalTheory.SeeSaw.KUni Formalism.IndefR.Eqv in

/- English proof (translation)
Introduce `D θ V B hθ hB`. Take `rfl` from `eq_thetaC D hθ`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `continuous_pi fun τ => ?_` and prove the remaining obligations. Establish `hm : Continuous fun g : GA D V => mt V g` using `Units.continuous_val.comp continuous_subtype_val`.

Establish `h1 : Continuous fun k : GinfC V => (mt V k.1).map (psiT D τ)` using `(hm.comp continuous_subtype_val).matrix_map (psiT_continuous τ)`. Conclude with `(continuous_const.matrix_mul h1).matrix_mul continuous_const`. Introduce `k k' τ`. Rewrite using `[inB_eq, inB_eq, inB_eq]`. Simplify using `only [Subgroup.coe_mul, infMat_thetaC, matA_mul, Matrix.map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_inv' (hB τ)]`. Simplify using `only [Matrix.mul_assoc, Matrix.one_mul]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`. Introduce `k τ`.

Rewrite using `[inB_eq]`. Conclude with `conj_unitary (hB τ) (infMat_unitary' D V k.1 τ)`. Introduce `u hu`. Establish `hgs : IsUnitFam D V fun τ => B τ * u τ * (B τ)⁻¹` using `fun τ => back_unitary (hB τ) (hu τ)`. Use `⟨⟨famH D V _ hgs, famH_mem_GinfC D V _ hgs⟩, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `τ`. Rewrite using `[inB_eq, infMat_famH]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = u τ := by rw [inv_mul' (hB τ), Matrix.one_mul, Matrix.mul_one]`.
-/
theorem GlobalTheory.SeeSaw.ontoUni_inB : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsInfFam θ → (∀ τ, (B τ)ᴴ * gramAt D V τ * B τ = 1) → OntoUni fun k : GinfC V => inB θ V B k.1 := by
  intro D θ V B hθ hB
  obtain rfl := eq_thetaC D hθ
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine continuous_pi fun τ => ?_
    have hm : Continuous fun g : GA D V => mt V g := Units.continuous_val.comp continuous_subtype_val
    have h1 : Continuous fun k : GinfC V => (mt V k.1).map (psiT D τ) :=
      (hm.comp continuous_subtype_val).matrix_map (psiT_continuous τ)
    exact (continuous_const.matrix_mul h1).matrix_mul continuous_const
  · intro k k' τ
    rw [inB_eq, inB_eq, inB_eq]
    simp only [Subgroup.coe_mul, infMat_thetaC, matA_mul, Matrix.map_mul]
    calc (B τ)⁻¹ * ((matA D V k).map (psiT D τ) * (matA D V k').map (psiT D τ)) * B τ
        = (B τ)⁻¹ * (matA D V k).map (psiT D τ) * (B τ * (B τ)⁻¹) * (matA D V k').map (psiT D τ) * B τ := by
          rw [mul_inv' (hB τ)]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  · intro k τ
    rw [inB_eq]
    exact conj_unitary (hB τ) (infMat_unitary' D V k.1 τ)
  · intro u hu
    have hgs : IsUnitFam D V fun τ => B τ * u τ * (B τ)⁻¹ := fun τ => back_unitary (hB τ) (hu τ)
    refine ⟨⟨famH D V _ hgs, famH_mem_GinfC D V _ hgs⟩, ?_⟩
    funext τ
    rw [inB_eq, infMat_famH]
    calc (B τ)⁻¹ * (B τ * u τ * (B τ)⁻¹) * B τ = ((B τ)⁻¹ * B τ) * u τ * ((B τ)⁻¹ * B τ) := by
          simp only [Matrix.mul_assoc]
      _ = u τ := by rw [inv_mul' (hB τ), Matrix.one_mul, Matrix.mul_one]
