import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobSympl
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobPhase
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IterEqOfRange

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem mlin_norm_le {m : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin m => (Fin k → ℝ)) ℂ) :
    ‖M‖ ≤ ∑ l : Fin m → Fin k, ‖M (fun i => ev (l i))‖ := by
  refine M.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : v = fun i => ∑ j, v i j • ev j := by
    funext i
    ext j'
    simp [ev, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv, M.map_sum]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [M.map_smul_univ, norm_smul, norm_prod, mul_comm]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_) (norm_nonneg _)
  exact norm_le_pi_norm (v i) (r i)

def Gf (ψ : AddChar (AF D.host.F) ℂ) (L : (Fin k → ℝ) →+ WO S T) (f : WO S T → ℂ) (x : WO S T) :
    (Fin k → ℝ) → ℂ := fun t => heisO ψ S T (L t) f x

def Ff (L : (Fin k → ℝ) →+ WO S T) (f : WO S T → ℂ) (x : WO S T) : (Fin k → ℝ) → ℂ := fun t => f (x + L t)

def ellAdd (Λ : Ainf D.host.F →+ ℂ) (L : (Fin k → ℝ) →+ WO S T) (x : WO S T) : (Fin k → ℝ) →+ ℂ :=
  AddMonoidHom.mk' (fun t => Λ (symplOH S T x (L t)).1) (fun t t' => by
    simp only [map_add, symplOH_add_right]
    exact Λ.map_add _ _)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem continuous_ellAdd (Λ : Ainf D.host.F →+ ℂ) (hΛ : Continuous Λ) (L : (Fin k → ℝ) →+ WO S T)
    (hL : Continuous L) (x : WO S T) : Continuous (ellAdd Λ L x) := by
  have hs : Continuous fun t => symplOH S T x (L t) := (continuous_symplOH_right x).comp hL
  have h1 : Continuous fun t => Λ (symplOH S T x (L t)).1 := hΛ.comp (continuous_fst.comp hs)
  exact h1

def ellx (Λ : Ainf D.host.F →+ ℂ) (hΛ : Continuous Λ) (L : (Fin k → ℝ) →+ WO S T) (hL : Continuous L)
    (x : WO S T) : (Fin k → ℝ) →L[ℝ] ℂ :=
  AddMonoidHom.toRealLinearMap (ellAdd Λ L x) (continuous_ellAdd Λ hΛ L hL x)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ellx_apply (Λ : Ainf D.host.F →+ ℂ) (hΛ : Continuous Λ) (L : (Fin k → ℝ) →+ WO S T) (hL : Continuous L)
    (x : WO S T) (t : Fin k → ℝ) : ellx Λ hΛ L hL x t = Λ (symplOH S T x (L t)).1 := rfl

section Bound

variable {ψ : AddChar (AF D.host.F) ℂ} {Λ : Ainf D.host.F →+ ℂ} (hΛ : Continuous Λ)
  (hψΛ : ∀ z : AF D.host.F, z.2 = 0 → ψ z = Complex.exp (Λ z.1))
  {L : (Fin k → ℝ) →+ WO S T} (hL : IsRealFrame L)

include hΛ hψΛ hL in
/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem Gf_eq (f : WO S T → ℂ) (x : WO S T) :
    Gf ψ L f x = fun t => Complex.exp (ellx Λ hΛ L hL.1 x t) * Ff L f x t := by
  funext t
  have hr : eInf D • L t = L t := (wo_real_iff (L t)).mp (hL.2.1 t)
  simp only [Gf, Ff, heisO, ellx_apply]
  rw [hψΛ _ (symplOH_snd x (L t) hr)]

include hΛ hψΛ hL in
/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem Gf_smooth {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : WO S T) : ContDiff ℝ ∞ (Gf ψ L f x) := by
  rw [Gf_eq hΛ hψΛ hL]
  exact ((Complex.contDiff_exp (𝕜 := ℝ)).comp (ellx Λ hΛ L hL.1 x).contDiff).mul
    (hf.smooth k L hL.1 hL.2.1 x)

end Bound

end Formalism.IndefR.Eqv

end
