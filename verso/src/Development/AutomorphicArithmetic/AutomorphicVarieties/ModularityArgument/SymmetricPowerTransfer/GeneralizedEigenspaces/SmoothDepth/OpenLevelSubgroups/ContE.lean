import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.ContRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.FinMH

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

/- English proof (translation)
Introduce `I _ j`. Take `⟨hG, hD⟩` from `Wt.contRep I`. Establish `hB : ∀ S : I → Bool, FiniteDimensional ℂ (Wt.Bi 3 (Wt.dg j S))` using `fun S => Wt.finMH _ 3 _`. Use `⟨⟨Module.Finite.pi, fun x f => hG j x f⟩, ⟨Wt.finMH I 2 (fun _ => j), fun e x f => ?_⟩⟩` and prove the remaining obligations. Establish `key : (fun g => f ((repE j e g) x)) = fun g => ((∏ v, Matrix.GeneralLinearGroup.det (g v) ^ e v : ℂˣ) : ℂ) * f ((Wt.repD I j 0 g) x)`.

Use function extensionality and compare the values at `g`. Simplify using `[repE, Wt.repD_apply, Wt.detE]`. Rewrite using `[key]`. Use `Continuous.mul (Units.continuous_val.comp ?_) (hD j 0 x f)` and prove the remaining obligations. Conclude with `continuous_finset_prod _ fun v _ => ((Matrix.GeneralLinearGroup.continuous_det).comp (continuous_apply v)).zpow (e v)`.
-/
theorem UpperTheory.V.Z.Sym.Al.contE :
    ∀ (I : Type) [Fintype I] (j : ℕ), (FiniteDimensional ℂ (Wt.VG I j) ∧ ContCoef (Wt.repG I j)) ∧
        (FiniteDimensional ℂ (Wt.VD I j) ∧ ∀ e : I → ℤ, ContCoef (repE j e)) := by
  intro I _ j
  obtain ⟨hG, hD⟩ := Wt.contRep I
  have hB : ∀ S : I → Bool, FiniteDimensional ℂ (Wt.Bi 3 (Wt.dg j S)) := fun S => Wt.finMH _ 3 _
  refine ⟨⟨Module.Finite.pi, fun x f => hG j x f⟩, ⟨Wt.finMH I 2 (fun _ => j), fun e x f => ?_⟩⟩
  have key : (fun g => f ((repE j e g) x)) = fun g =>
      ((∏ v, Matrix.GeneralLinearGroup.det (g v) ^ e v : ℂˣ) : ℂ) * f ((Wt.repD I j 0 g) x) := by
    funext g
    simp [repE, Wt.repD_apply, Wt.detE]
  rw [key]
  refine Continuous.mul (Units.continuous_val.comp ?_) (hD j 0 x f)
  exact continuous_finset_prod _ fun v _ =>
    ((Matrix.GeneralLinearGroup.continuous_det).comp (continuous_apply v)).zpow (e v)
