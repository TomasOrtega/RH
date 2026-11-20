import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.EFinSmulEqOfFinPart
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NormIterFderivApplyLe

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

def actOAdd (g : GA D S) (h : GA D T) : WO S T →+ WO S T := AddMonoidHom.mk' (actO S T g h) (actO_add g h)

/- English proof (translation)
Unfold `actO`. Conclude with `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`.
-/
theorem continuous_actO (g : GA D S) (h : GA D T) : Continuous (actO S T g h) := by
  unfold actO
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

/- English proof (translation)
Establish `hLPM : ∀ w, ((actOAdd g⁻¹ h⁻¹).comp L) ((P.comp (actOAdd g h)) w) = eInf D • w`. Introduce `w`. Use `show actO S T g⁻¹ h⁻¹ (L (P (actO S T g h w))) = eInf D • w`. Rewrite using `[hLP, actO_smul, actO_inv']`. Use `⟨⟨(continuous_actO g⁻¹ h⁻¹).comp hL.1, fun t => ?_, fun w hw => ⟨P (actO S T g h w), ?_⟩⟩, hPc.comp (continuous_actO g h), hLPM⟩` and prove the remaining obligations.

Rewrite using `[wo_real_iff] show eInf D • actO S T g⁻¹ h⁻¹ (L t) = actO S T g⁻¹ h⁻¹ (L t)`. Rewrite using `[← actO_smul, (wo_real_iff (L t)).mp (hL.2.1 t)]`. Use `hLPM w` as an intermediate fact. Rewrite `this` using `[(wo_real_iff w).mp hw]`. Conclude with `this`.
-/
theorem transported_frame {L : (Fin k → ℝ) →+ WO S T} {P : WO S T →+ (Fin k → ℝ)} (hL : IsRealFrame L)
    (hPc : Continuous P) (hLP : ∀ w, L (P w) = eInf D • w) (g : GA D S) (h : GA D T) :
    IsRealFrame ((actOAdd g⁻¹ h⁻¹).comp L) ∧ Continuous (P.comp (actOAdd g h)) ∧
      ∀ w, ((actOAdd g⁻¹ h⁻¹).comp L) ((P.comp (actOAdd g h)) w) = eInf D • w := by
  have hLPM : ∀ w, ((actOAdd g⁻¹ h⁻¹).comp L) ((P.comp (actOAdd g h)) w) = eInf D • w := by
    intro w
    show actO S T g⁻¹ h⁻¹ (L (P (actO S T g h w))) = eInf D • w
    rw [hLP, actO_smul, actO_inv']
  refine ⟨⟨(continuous_actO g⁻¹ h⁻¹).comp hL.1, fun t => ?_, fun w hw => ⟨P (actO S T g h w), ?_⟩⟩,
    hPc.comp (continuous_actO g h), hLPM⟩
  · rw [wo_real_iff]
    show eInf D • actO S T g⁻¹ h⁻¹ (L t) = actO S T g⁻¹ h⁻¹ (L t)
    rw [← actO_smul, (wo_real_iff (L t)).mp (hL.2.1 t)]
  · have := hLPM w
    rw [(wo_real_iff w).mp hw] at this
    exact this

/- English proof (translation)
Take `⟨U, hU, hUf⟩` from `hf.level`. Establish `hψc : Continuous ψ` using `hψ.1.1`. Use `⟨fun γ w => ?_, ⟨U, hU, fun u hu hu0 => ?_⟩, ?_, fun k' L' hL' hL'0 w => ?_⟩` and prove the remaining obligations. Simplify using `only [heisO]`. Rewrite using `[add_assoc, hf.quasi γ (w + w₀), symplOH_add_left, symplOH_add_right, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]`.

Use `congr 2`. Normalize the expressions using the abelian group laws. Establish `hufin : eFin D • u = u` using `(wo_fin_iff u).mp hu0`. Use function extensionality and compare the values at `y`. Establish `h1` using `congrFun (hUf u hu hu0) (y + w₀)`.

Simplify using `only [heisO] at h1 ⊢`. Rewrite using `[← h1, show y + u + w₀ = y + w₀ + u by abel, symplOH_add_left y u w₀, symplOH_fin_real u w₀ hufin hw, add_zero, symplOH_add_left y w₀ u, symplOH_real_fin w₀ u hw hufin, add_zero]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `(hψc.comp ((continuous_symplOH_left w₀))).mul (hf.cont.comp (continuous_id.add continuous_const))`. Take `⟨Λ, hΛ, hψΛ⟩` from `psi_real ψ hψ`.

Establish `hsm` using `hf.smooth k' L' hL' hL'0 (w + w₀)`. Establish `hr : ∀ t, eInf D • L' t = L' t` using `fun t => (wo_real_iff (L' t)).mp (hL'0 t)`. Set `c : (Fin k' → ℝ) →+ ℂ` to `AddMonoidHom.mk' (fun t => Λ (symplOH S T (L' t) w₀).1) (fun a b => by`. Simplify using `only [map_add, symplOH_add_left]`. Conclude with `Λ.map_add _ _)`.

Establish `hc : Continuous c`. Establish `h1 : Continuous fun t => symplOH S T (L' t) w₀` using `(continuous_symplOH_left w₀).comp hL'`. Conclude with `hΛ.comp (continuous_fst.comp h1)`. Establish `hfun : (fun t => heisO ψ S T w₀ f (w + L' t)) = fun t => ψ (symplOH S T w w₀) * (Complex.exp (AddMonoidHom.toRealLinearMap c hc t) * f (w + w₀ + L' t))`. Use function extensionality and compare the values at `t`.

Simplify using `only [heisO]`. Rewrite using `[symplOH_add_left, AddChar.map_add_eq_mul, hψΛ _ (symplOH_snd (L' t) w₀ hw)]`. Rewrite using `[show w + L' t + w₀ = w + w₀ + L' t by abel, mul_assoc]`. Both sides reduce to the same expression. Rewrite using `[hfun]`.

Conclude with `contDiff_const.mul (((Complex.contDiff_exp (𝕜 := ℝ)).comp (AddMonoidHom.toRealLinearMap c hc).contDiff).mul hsm)`.
-/
theorem thetaO_heis {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (w₀ : WO S T) (hw : eInf D • w₀ = w₀) : IsThetaFunO ψ S T (heisO ψ S T w₀ f) := by
  obtain ⟨U, hU, hUf⟩ := hf.level
  have hψc : Continuous ψ := hψ.1.1
  refine ⟨fun γ w => ?_, ⟨U, hU, fun u hu hu0 => ?_⟩, ?_, fun k' L' hL' hL'0 w => ?_⟩
  · simp only [heisO]
    rw [add_assoc, hf.quasi γ (w + w₀), symplOH_add_left, symplOH_add_right, ← mul_assoc, ← mul_assoc,
      ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2
    abel
  · have hufin : eFin D • u = u := (wo_fin_iff u).mp hu0
    funext y
    have h1 := congrFun (hUf u hu hu0) (y + w₀)
    simp only [heisO] at h1 ⊢
    rw [← h1, show y + u + w₀ = y + w₀ + u by abel, symplOH_add_left y u w₀, symplOH_fin_real u w₀ hufin hw,
      add_zero, symplOH_add_left y w₀ u, symplOH_real_fin w₀ u hw hufin, add_zero]
    ring
  · exact (hψc.comp ((continuous_symplOH_left w₀))).mul (hf.cont.comp (continuous_id.add continuous_const))
  · obtain ⟨Λ, hΛ, hψΛ⟩ := psi_real ψ hψ
    have hsm := hf.smooth k' L' hL' hL'0 (w + w₀)
    have hr : ∀ t, eInf D • L' t = L' t := fun t => (wo_real_iff (L' t)).mp (hL'0 t)
    let c : (Fin k' → ℝ) →+ ℂ := AddMonoidHom.mk' (fun t => Λ (symplOH S T (L' t) w₀).1) (fun a b => by
      simp only [map_add, symplOH_add_left]; exact Λ.map_add _ _)
    have hc : Continuous c := by
      have h1 : Continuous fun t => symplOH S T (L' t) w₀ := (continuous_symplOH_left w₀).comp hL'
      exact hΛ.comp (continuous_fst.comp h1)
    have hfun : (fun t => heisO ψ S T w₀ f (w + L' t)) =
        fun t => ψ (symplOH S T w w₀) * (Complex.exp (AddMonoidHom.toRealLinearMap c hc t) * f (w + w₀ + L' t)) := by
      funext t
      simp only [heisO]
      rw [symplOH_add_left, AddChar.map_add_eq_mul, hψΛ _ (symplOH_snd (L' t) w₀ hw)]
      rw [show w + L' t + w₀ = w + w₀ + L' t by abel, mul_assoc]
      rfl
    rw [hfun]
    exact contDiff_const.mul (((Complex.contDiff_exp (𝕜 := ℝ)).comp
      (AddMonoidHom.toRealLinearMap c hc).contDiff).mul hsm)

end Formalism.IndefR.Eqv

end
