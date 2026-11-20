import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FrMIsIsom

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.S.Pv.SecW

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

variable {n r k : ℕ} (ε : Fin n → Bool)

def fr2L (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ)
    (e' p' : Fin r → Fin n → ℂ) (z' : Fin n → ℂ) (w' : Fin k → Fin n → ℂ) (T : ℝ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun v := syn e' p' z' w' T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v)
  map_add' v v' := by
    simp only [syn, UnitaryIsometries.hJ_add_right, add_smul, Finset.sum_add_distrib, neg_add, add_div]
    abel
  map_smul' c v := by
    simp only [syn, UnitaryIsometries.hJ_smul_right, RingHom.id_apply, smul_add, Finset.smul_sum, smul_smul]
    rw [show -(c * hJ ε z v) / (T : ℂ) = c * (-hJ ε z v / T) by ring]

def fr2M (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ)
    (e' p' : Fin r → Fin n → ℂ) (z' : Fin n → ℂ) (w' : Fin k → Fin n → ℂ) (T : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix' (fr2L ε e p z w e' p' z' w' T)

variable {ε} {e p : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {w : Fin k → Fin n → ℂ}
  {e' p' : Fin r → Fin n → ℂ} {z' : Fin n → ℂ} {w' : Fin k → Fin n → ℂ} {T : ℝ}

/- English proof (translation)
Unfold `fr2M`. Rewrite using `[LinearMap.toMatrix'_mulVec]`. Both sides reduce to the same expression.
-/
theorem frameChangeMatrix_mulVec (v : Fin n → ℂ) :
    fr2M ε e p z w e' p' z' w' T *ᵥ v =
      syn e' p' z' w' T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v) := by
  unfold fr2M
  rw [LinearMap.toMatrix'_mulVec]
  rfl

/- English proof (translation)
Establish `h : fr2M ε e p z w e' p' z' w' T *ᵥ Pi.single j 1 = _` using `frameChangeMatrix_mulVec _`. Rewrite `h` using `[Matrix.mulVec_single_one]`. Conclude with `congrFun h i`.
-/
theorem frameChangeMatrix_entry (i j : Fin n) :
    fr2M ε e p z w e' p' z' w' T i j =
      syn e' p' z' w' T (fun a => hJ ε (p a) (Pi.single j 1)) (fun a => hJ ε (e a) (Pi.single j 1))
        (hJ ε z (Pi.single j 1)) (fun l => hJ ε (w l) (Pi.single j 1)) i := by
  have h : fr2M ε e p z w e' p' z' w' T *ᵥ Pi.single j 1 = _ := frameChangeMatrix_mulVec _
  rw [Matrix.mulVec_single_one] at h
  exact congrFun h i

/- English proof (translation)
Introduce `x y`. Rewrite using `[frameChangeMatrix_mulVec, frameChangeMatrix_mulVec, hJ_syn_syn F']`. Use `conv_rhs => rw [recon F hdim x, recon F hdim y, hJ_syn_syn F]`.
-/
theorem frameChangeMatrix_isometry (F : Frm ε e p z w T) (F' : Frm ε e' p' z' w' T) (hdim : n = 2 * r + 1 + k) :
    UnitaryIsometries.IsIsom ε (fr2M ε e p z w e' p' z' w' T) := by
  intro x y
  rw [frameChangeMatrix_mulVec, frameChangeMatrix_mulVec, hJ_syn_syn F']
  conv_rhs => rw [recon F hdim x, recon F hdim y, hJ_syn_syn F]

/- English proof (translation)
Rewrite using `[frameChangeMatrix_mulVec]`. Establish `h1 : (fun a => hJ ε (p a) (e b)) = fun a => if a = b then (1 : ℂ) else 0`. Use function extensionality and compare the values at `a`. Rewrite using `[UnitaryIsometries.hJ_conj, F.ep b a]`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hab, Ne.symm hab]`. Establish `h2 : (fun a => hJ ε (e a) (e b)) = fun _ => (0 : ℂ)`. Use function extensionality and compare the values at `a`.

Conclude with `F.ee a b`. Establish `h3 : hJ ε z (e b) = 0` using `by rw [UnitaryIsometries.hJ_conj, F.ez b, map_zero]`. Establish `h4 : (fun j => hJ ε (w j) (e b)) = fun _ => (0 : ℂ)`. Use function extensionality and compare the values at `j`. Rewrite using `[UnitaryIsometries.hJ_conj, F.ew b j, map_zero]`.

Rewrite using `[h1, h2, h3, h4]`. Simplify using `[syn]`.
-/
theorem frameChangeMatrix_isotropic (F : Frm ε e p z w T) (b : Fin r) : fr2M ε e p z w e' p' z' w' T *ᵥ e b = e' b := by
  rw [frameChangeMatrix_mulVec]
  have h1 : (fun a => hJ ε (p a) (e b)) = fun a => if a = b then (1 : ℂ) else 0 := by
    funext a
    rw [UnitaryIsometries.hJ_conj, F.ep b a]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab, Ne.symm hab]
  have h2 : (fun a => hJ ε (e a) (e b)) = fun _ => (0 : ℂ) := by
    funext a
    exact F.ee a b
  have h3 : hJ ε z (e b) = 0 := by rw [UnitaryIsometries.hJ_conj, F.ez b, map_zero]
  have h4 : (fun j => hJ ε (w j) (e b)) = fun _ => (0 : ℂ) := by
    funext j
    rw [UnitaryIsometries.hJ_conj, F.ew b j, map_zero]
  rw [h1, h2, h3, h4]
  simp [syn]

/- English proof (translation)
Rewrite using `[frameChangeMatrix_mulVec]`. Establish `h1 : (fun a => hJ ε (p a) z) = fun _ => (0 : ℂ)`. Use function extensionality and compare the values at `a`. Conclude with `F.pz a`. Establish `h2 : (fun a => hJ ε (e a) z) = fun _ => (0 : ℂ)`.

Use function extensionality and compare the values at `a`. Conclude with `F.ez a`. Establish `h4 : (fun j => hJ ε (w j) z) = fun _ => (0 : ℂ)`. Use function extensionality and compare the values at `j`. Rewrite using `[UnitaryIsometries.hJ_conj, F.zw j, map_zero]`.

Rewrite using `[h1, h2, F.zz, h4]`. Establish `hT : (T : ℂ) ≠ 0` using `by exact_mod_cast F.T_ne`. Simplify using `[syn, hT]`.
-/
theorem fr2M_mulVec_z (F : Frm ε e p z w T) : fr2M ε e p z w e' p' z' w' T *ᵥ z = z' := by
  rw [frameChangeMatrix_mulVec]
  have h1 : (fun a => hJ ε (p a) z) = fun _ => (0 : ℂ) := by
    funext a
    exact F.pz a
  have h2 : (fun a => hJ ε (e a) z) = fun _ => (0 : ℂ) := by
    funext a
    exact F.ez a
  have h4 : (fun j => hJ ε (w j) z) = fun _ => (0 : ℂ) := by
    funext j
    rw [UnitaryIsometries.hJ_conj, F.zw j, map_zero]
  rw [h1, h2, F.zz, h4]
  have hT : (T : ℂ) ≠ 0 := by exact_mod_cast F.T_ne
  simp [syn, hT]

end Formalism.L2.S.Pv.SecW
