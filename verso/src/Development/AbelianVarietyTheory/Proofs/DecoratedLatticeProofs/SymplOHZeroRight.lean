import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ContrComb

variable {D : D7}

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem symplOH_zero_right (S T : HSp D) (x : WO S T) : symplOH S T x 0 = 0 := by
  simp [symplOH, symplO, hO]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem symplOH_zero_left (S T : HSp D) (x : WO S T) : symplOH S T 0 x = 0 := by
  simp [symplOH, symplO, hO]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem heis_left {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (ψ : AddChar (AF D.host.F) ℂ) (l : Link B B'.L B'.ζ)
    (S : HSp D) (vL : VolM D B'.L.rank S.rank) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) (a : WO B.A S)
    (u : WO B.A S) (v : WO S B'.A) :
    heisO ψ B.A S a (fun u' => contr l S vL f₁ f₂ u' v) u =
      contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (a, 0)) f₁) f₂ u v := by
  simp only [heisO, contr]
  rw [← integral_const_mul]
  congr 1
  funext w
  have h1 : (B.o.resS S).symm (u, l.κ S w) + (B.o.resS S).symm (a, 0) = (B.o.resS S).symm (u + a, l.κ S w) := by
    rw [← map_add]; simp
  rw [B.o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_right, add_zero, h1]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem heis_right {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (ψ : AddChar (AF D.host.F) ℂ) (l : Link B B'.L B'.ζ)
    (S : HSp D) (vL : VolM D B'.L.rank S.rank) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) (b : WO S B'.A)
    (u : WO B.A S) (v : WO S B'.A) :
    heisO ψ S B'.A b (contr l S vL f₁ f₂ u) v =
      contr l S vL f₁ (heisO ψ S B'.V₀ ((B'.o.resT S).symm (b, 0)) f₂) u v := by
  simp only [heisO, contr]
  rw [← integral_const_mul]
  congr 1
  funext w
  have h1 : (B'.o.resT S).symm (v, w) + (B'.o.resT S).symm (b, 0) = (B'.o.resT S).symm (v + b, w) := by
    rw [← map_add]; simp
  rw [B'.o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_right, add_zero, h1]
  ring

end GlobalTheory.ContrComb
end

noncomputable section
namespace GlobalTheory.ContrComb

variable {D : D7}

def extL {V₀ A L S : HSp D} (o : OrthDec V₀ A L) : WO A S →+ WO V₀ S :=
  (o.resS S).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)

def extR {V₀ A L S : HSp D} (o : OrthDec V₀ A L) : WO S A →+ WO S V₀ :=
  (o.resT S).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem extL_apply {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO A S) : extL (S := S) o u = (o.resS S).symm (u, 0) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem extR_apply {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO S A) : extR (S := S) o u = (o.resT S).symm (u, 0) := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_extL {V₀ A L S : HSp D} (o : OrthDec V₀ A L) : Continuous (extL (S := S) o) :=
  (o.continuous_resS_symm S).comp (continuous_id.prodMk continuous_const)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_extR {V₀ A L S : HSp D} (o : OrthDec V₀ A L) : Continuous (extR (S := S) o) :=
  (o.continuous_resT_symm S).comp (continuous_id.prodMk continuous_const)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem extL_inf {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO A S) (h : u.map (infPart D) = 0) :
    (extL (S := S) o u).map (infPart D) = 0 := by
  rw [extL_apply, OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
  change (u * o.pA).map (infPart D) = 0
  rw [Matrix.map_mul, h, Matrix.zero_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem extR_inf {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO S A) (h : u.map (infPart D) = 0) :
    (extR (S := S) o u).map (infPart D) = 0 := by
  rw [extR_apply, OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
  change (o.jA * u).map (infPart D) = 0
  rw [Matrix.map_mul, h, Matrix.mul_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules.
-/
theorem extL_half {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (e : AE D) (u : WO A S) (h : IsHalf e u) :
    IsHalf e (extL (S := S) o u) := by
  intro i j
  rw [extL_apply, OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
  change e * (u * o.pA) i j = (u * o.pA) i j
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, h i]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities.
-/
theorem extR_half {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (e : AE D) (u : WO S A) (h : IsHalf e u) :
    IsHalf e (extR (S := S) o u) := by
  intro i j
  rw [extR_apply, OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
  change e * (o.jA * u) i j = (o.jA * u) i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, h k j]

end GlobalTheory.ContrComb
end
