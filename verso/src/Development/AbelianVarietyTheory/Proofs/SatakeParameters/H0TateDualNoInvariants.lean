import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.TateDualCoef

open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts TensorProduct

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

def coordEquiv :
    TensorProduct (N.O i) (Module.Dual (N.O i) (Fin R.r → N.O i)) (Kf N i) ≃ₗ[N.O i] (Fin R.r → Kf N i) :=
  (TensorProduct.congr (Pi.basisFun (N.O i) (Fin R.r)).dualBasis.equivFun (LinearEquiv.refl _ _)) ≪≫ₗ
    TensorProduct.comm (N.O i) (Fin R.r → N.O i) (Kf N i) ≪≫ₗ
      TensorProduct.piScalarRight (N.O i) (N.O i) (Kf N i) (Fin R.r)

/- English proof (translation)
Use extensionality with `a`. Simplify using `[coordEquiv, TensorProduct.piScalarRight_apply]`.
-/
theorem coordEquiv_tmul (f : Module.Dual (N.O i) (Fin R.r → N.O i)) (c : Kf N i) :
    coordEquiv N i (f ⊗ₜ c) = fun a => f (Pi.single a 1) • c := by
  ext a
  simp [coordEquiv, TensorProduct.piScalarRight_apply]

/- English proof (translation)
Establish `hv : ∀ v : Fin R.r → N.O i, f v = ∑ b, v b * f (Pi.single b 1)` using `fun v => by conv_lhs => rw [pi_eq_sum_univ v]`. Simplify using `only [map_sum, map_smul, smul_eq_mul]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `congr 2`. Use function extensionality and compare the values at `j`.

Simplify using `[Pi.single_apply, eq_comm]`. Simplify using `only [Glob.T2, Glob.Wp, twistRep, glRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply, Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, MonoidHom.inv_apply]`. Rewrite using `[map_smul, hv]`. Simplify using `only [smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Simplify using `[Matrix.toLin'_apply, Pi.smul_apply, mul_assoc]`.
-/
theorem tate_dual_single_basis (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g : G H.E N.Om)
    (f : Module.Dual (N.O i) (Fin R.r → N.O i)) (a : Fin R.r) :
    (Glob.T2 N i ρ g f) (Pi.single a 1) =
      ∑ b, ((Glob.epsO N i g : (N.O i)ˣ) : N.O i) * ((((N.chi i 1 g⁻¹)⁻¹ : (N.O i)ˣ) : N.O i) *
        ((ρ g⁻¹ : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)) b a) * f (Pi.single b 1) := by
  have hv : ∀ v : Fin R.r → N.O i, f v = ∑ b, v b * f (Pi.single b 1) := fun v => by
    conv_lhs => rw [pi_eq_sum_univ v]
    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  simp only [Glob.T2, Glob.Wp, twistRep, glRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply,
    Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, MonoidHom.inv_apply]
  rw [map_smul, hv]
  simp only [smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [Matrix.toLin'_apply, Pi.smul_apply, mul_assoc]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, Matrix.mulVec_add]`. Consider the case `tmul f c`. Establish `e1 : coefRep (Glob.T2 N i ρ) (Kf N i) g (f ⊗ₜ c) = (Glob.T2 N i ρ g f) ⊗ₜ c` using `rfl`.

Rewrite using `[e1, coordEquiv_tmul, coordEquiv_tmul]`. Use function extensionality and compare the values at `a`. Rewrite using `[tate_dual_single_basis]`. Simplify using `only [Matrix.mulVec, dotProduct, matT, matW, Matrix.smul_apply, Matrix.transpose_apply, Matrix.map_apply, smul_eq_mul]`. Simplify using `only [Algebra.smul_def, map_sum, map_mul, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [eps, Glob.epsO]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coordEquiv_equivariant (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g : G H.E N.Om)
    (x : TensorProduct (N.O i) (Module.Dual (N.O i) (Fin R.r → N.O i)) (Kf N i)) :
    coordEquiv N i (coefRep (Glob.T2 N i ρ) (Kf N i) g x) = (matT N i ρ g).mulVec (coordEquiv N i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, Matrix.mulVec_add]
  | tmul f c =>
    have e1 : coefRep (Glob.T2 N i ρ) (Kf N i) g (f ⊗ₜ c) = (Glob.T2 N i ρ g f) ⊗ₜ c := rfl
    rw [e1, coordEquiv_tmul, coordEquiv_tmul]
    funext a
    rw [tate_dual_single_basis]
    simp only [Matrix.mulVec, dotProduct, matT, matW, Matrix.smul_apply, Matrix.transpose_apply,
      Matrix.map_apply, smul_eq_mul]
    simp only [Algebra.smul_def, map_sum, map_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [eps, Glob.epsO]
    ring

/- English proof (translation)
Introduce `R H what₂ N i ρ Dg h`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Rewrite using `[Submodule.mem_bot]`. Establish `hfix : ∀ g ∈ Dg, (matT N i ρ g).mulVec (coordEquiv N i x) = coordEquiv N i x`.

Introduce `g hg`. Rewrite using `[← coordEquiv_equivariant]`. Use `congr 1`. Conclude with `(Representation.mem_invariants _ x).1 hx ⟨g, hg⟩`. Establish `h0` using `h _ hfix`.

Conclude with `(coordEquiv N i).injective (by rw [h0, map_zero])`.
-/
theorem H0_coefRep_T2_comp_subtype_eq_bot_of_noInv : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (Dg : Subgroup (G H.E N.Om)), GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.NoInv Dg (GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matT N i ρ) → H0 ((Formalism.MainNotions.N.coefRep (Formalism.MainNotions.N.Glob.T2 N i ρ) (Kf N i)).comp Dg.subtype) = ⊥ := by
  intro R H what₂ N i ρ Dg h
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  have hfix : ∀ g ∈ Dg, (matT N i ρ g).mulVec (coordEquiv N i x) = coordEquiv N i x := by
    intro g hg
    rw [← coordEquiv_equivariant]
    congr 1
    exact (Representation.mem_invariants _ x).1 hx ⟨g, hg⟩
  have h0 := h _ hfix
  exact (coordEquiv N i).injective (by rw [h0, map_zero])

end GlobalTheory.TateDualCoef
