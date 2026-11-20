import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PsiEqOfFin
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FibFact
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellT

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.StdUnn
open Formalism.IndefR.Eqv (psiT psiT_sigR psiT_inclR thetaC eq_thetaC glueA splitInv psiT_glueA finPart_glueA ae_ext'
  continuous_glueA continuous_splitInv continuous_psiT)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTP

open Classical

variable {D : D7} {m n : ℕ}

def insT (τ : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) : Mx D m n :=
  Matrix.of fun i j => glueA D (splitInv D fun τ' => if τ' = τ then v i j else 0) 0

/- English proof (translation)
The claim follows from `psiT_glueA D τ' _ 0`.
-/
theorem psiT_insT (τ τ' : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    psiT D τ' (insT τ v i j) = if τ' = τ then v i j else 0 := psiT_glueA D τ' _ 0

/- English proof (translation)
The claim follows from `finPart_glueA D _ 0`.
-/
theorem finPart_insT (τ : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    finPart D (insT τ v i j) = 0 := finPart_glueA D _ 0

/- English proof (translation)
Use extensionality with `i j`. Apply `ae_ext' D` to reduce the goal to its premises. Introduce `τ'`. Rewrite using `[Matrix.add_apply, RingHom.map_add, psiT_insT, psiT_insT, psiT_insT]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[Matrix.add_apply, RingHom.map_add, finPart_insT, finPart_insT, finPart_insT, add_zero]`.
-/
theorem insT_add (τ : D.what₂.Tau) (v w : Matrix (Fin m) (Fin n) ℂ) : insT (D := D) τ (v + w) = insT τ v + insT τ w := by
  ext i j
  apply ae_ext' D
  · intro τ'
    rw [Matrix.add_apply, RingHom.map_add, psiT_insT, psiT_insT, psiT_insT]
    split_ifs <;> simp
  · rw [Matrix.add_apply, RingHom.map_add, finPart_insT, finPart_insT, finPart_insT, add_zero]

/- English proof (translation)
Use extensionality with `i j`. Apply `ae_ext' D` to reduce the goal to its premises. Introduce `τ'`. Rewrite using `[psiT_insT, Matrix.zero_apply, Matrix.zero_apply, RingHom.map_zero]`. Apply the tactic sequence `split_ifs <;> rfl`.

Rewrite using `[finPart_insT, Matrix.zero_apply, RingHom.map_zero]`.
-/
theorem insT_zero (τ : D.what₂.Tau) : insT (D := D) (m := m) (n := n) τ 0 = 0 := by
  ext i j
  apply ae_ext' D
  · intro τ'
    rw [psiT_insT, Matrix.zero_apply, Matrix.zero_apply, RingHom.map_zero]
    split_ifs <;> rfl
  · rw [finPart_insT, Matrix.zero_apply, RingHom.map_zero]

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Use `(continuous_glueA D 0).comp ((continuous_splitInv D).comp (continuous_pi fun τ' => ?_))` and prove the remaining obligations. Use `split_ifs`. Conclude with `(continuous_apply j).comp (continuous_apply i)`. Conclude with `continuous_const`.
-/
theorem continuous_insT (τ : D.what₂.Tau) : Continuous (insT (D := D) (m := m) (n := n) τ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (continuous_glueA D 0).comp ((continuous_splitInv D).comp (continuous_pi fun τ' => ?_))
  split_ifs
  · exact (continuous_apply j).comp (continuous_apply i)
  · exact continuous_const

/- English proof (translation)
Rewrite using `[eq_thetaC D hθ]`. Use extensionality with `i j`. Use `show psiT D τ' (insT τ v i j) = _`. Rewrite using `[psiT_insT]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem compAt_insT {θ : InfFam D} (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) :
    compAt θ τ' (insT τ v) = if τ' = τ then v else 0 := by
  rw [eq_thetaC D hθ]
  ext i j
  show psiT D τ' (insT τ v i j) = _
  rw [psiT_insT]
  split_ifs <;> rfl

/- English proof (translation)
Use extensionality with `i j`. Conclude with `finPart_insT τ v i j`.
-/
theorem finMap_insT (τ : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) : (insT (D := D) τ v).map (finPart D) = 0 := by
  ext i j; exact finPart_insT τ v i j

def sIns (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin n → ℂ) →+ Mx D m n where
  toFun u := insT τ (fr * Matrix.of u)
  map_zero' := by simp [insT_zero]
  map_add' u v := by
    rw [show Matrix.of (u + v) = Matrix.of u + Matrix.of v from rfl, Matrix.mul_add, insT_add]

set_option synthInstance.maxHeartbeats 400000 in

def piF (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) : Mx D m n →+ (Fin m → Fin n → ℂ) where
  toFun y := Matrix.of.symm (fr⁻¹ * compAt θ τ y)
  map_zero' := by
    ext i j
    simp [compAt]
  map_add' y y' := by
    have h : compAt θ τ (y + y') = compAt θ τ y + compAt θ τ y' := by
      ext i j; simp only [compAt, Matrix.map_apply, Matrix.add_apply, RingHom.map_add]
    ext i j
    simp only [h, Matrix.mul_add]
    rfl

set_option synthInstance.maxHeartbeats 400000 in
/- English proof (translation)
Use `show Matrix.of.symm (fr⁻¹ * compAt θ τ (insT τ (fr * Matrix.of u))) = u`. Rewrite using `[compAt_insT hθ, if_pos rfl, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr, Matrix.one_mul]`. Both sides reduce to the same expression.
-/
theorem piF_sIns {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {fr : Matrix (Fin m) (Fin m) ℂ}
    (hfr : IsUnit fr.det) (u : Fin m → Fin n → ℂ) : piF θ τ fr (sIns (D := D) τ fr u) = u := by
  show Matrix.of.symm (fr⁻¹ * compAt θ τ (insT τ (fr * Matrix.of u))) = u
  rw [compAt_insT hθ, if_pos rfl, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr, Matrix.one_mul]
  rfl

/- English proof (translation)
Establish `h : Continuous fun y : Mx D m n => (fr⁻¹ * compAt θ τ y : Matrix (Fin m) (Fin n) ℂ)`. Use `Continuous.matrix_mul continuous_const ?_` and prove the remaining obligations. Rewrite using `[eq_thetaC D hθ]`. Conclude with `Continuous.matrix_map continuous_id (Formalism.IndefR.Eqv.continuous_psiT (D := D) τ)`. Conclude with `h`.
-/
theorem continuous_piF {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) :
    Continuous (piF (n := n) θ τ fr) := by
  have h : Continuous fun y : Mx D m n => (fr⁻¹ * compAt θ τ y : Matrix (Fin m) (Fin n) ℂ) := by
    refine Continuous.matrix_mul continuous_const ?_
    rw [eq_thetaC D hθ]
    exact Continuous.matrix_map continuous_id (Formalism.IndefR.Eqv.continuous_psiT (D := D) τ)
  exact h

/- English proof (translation)
Use `show Continuous fun u : Fin m → Fin n → ℂ => insT τ (fr * Matrix.of u)`. Conclude with `(continuous_insT τ).comp (Continuous.matrix_mul continuous_const continuous_id)`.
-/
theorem continuous_sIns (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) :
    Continuous (sIns (D := D) (n := n) τ fr) := by
  show Continuous fun u : Fin m → Fin n → ℂ => insT τ (fr * Matrix.of u)
  exact (continuous_insT τ).comp (Continuous.matrix_mul continuous_const continuous_id)

end PositivityTheory.Rg.Sw.Glob.FTP
