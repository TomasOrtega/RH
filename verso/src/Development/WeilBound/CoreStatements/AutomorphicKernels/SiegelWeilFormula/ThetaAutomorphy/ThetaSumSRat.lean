import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
import Development.WeilBound.ThetaLifts.LeviDeterminants.WeilRepRationalDarbouxFixesThetaDistribution
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.DoubledGroupTopologicalProperties

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Tauto

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Establish `hS : d.S γ Ψ ∈ d.sch` using `d.ok.dbl.lin.pres γ Ψ hΨ`. Take `⟨g₀, hg₀⟩` from `PositivityTheory.ThKF0.Resc.rat_mat (inv_mem hγ)`. Take `⟨g₁, hg₁⟩` from `PositivityTheory.ThKF0.Resc.rat_mat hγ`. Establish `hinj : Function.Injective (incM F : Matrix (Fin d.m) (Fin d.m) E → Matrix (Fin d.m) (Fin d.m) (AE F E))` using `PositivityTheory.SiegelWeilFormula.kfour.incM_injective`. Establish `hmul : ∀ {p q r : ℕ} (A : Matrix (Fin p) (Fin q) E) (B : Matrix (Fin q) (Fin r) E), incM F (A * B) = incM F A * incM F B` using `fun A B => Matrix.map_mul (f := inclR (F := F) (E := E) (AF F))`.

Establish `hone : incM F (1 : Matrix (Fin d.m) (Fin d.m) E) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `e01 : g₀ * g₁ = 1` using `hinj (by`. Rewrite using `[hmul, ← hg₀, ← hg₁, hone]`. Use `congrArg (fun u : UA σ d.A.J => ((u.1 : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E))) (inv_mul_cancel γ)` as an intermediate fact. Simplify using `at this`.

Simplify using `using this)`. Establish `e10 : g₁ * g₀ = 1` using `(Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).1 e01`. Set `e : Matrix (Fin d.m) (Fin d.n) E ≃ Matrix (Fin d.m) (Fin d.n) E` to `⟨fun X => g₀ * X, fun X => g₁ * X, fun X => by simp [← Matrix.mul_assoc, e10], fun X => by simp [← Matrix.mul_assoc, e01]⟩`. Establish `h1` using `(hT F E σ d (d.S γ Ψ) hS).1`. Establish `h2` using `(hT F E σ d Ψ hΨ).1`.

Establish `h3 : HasSum (fun X : Matrix (Fin d.m) (Fin d.n) E => d.T Ψ (incM F (e X))) (thetaSum F (d.S γ Ψ))`. Use `h1.congr_fun fun X => ?_` and prove the remaining obligations. Rewrite using `[(hP F E σ d Ψ hΨ).2.2 γ (incM F X)]`. Simplify using `only [e, Equiv.coe_fn_mk, hmul, mat, ← hg₀]`. Conclude with `h3.unique ((e.hasSum_iff).2 h2)`.
-/
theorem thetaSum_S_rat (hP : TPar) (hT : TTheta) (d : SD σ) {γ : UA σ d.A.J} (hγ : γ ∈ ratU σ d.A.J)
    {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) : thetaSum F (d.S γ Ψ) = thetaSum F Ψ := by
  have hS : d.S γ Ψ ∈ d.sch := d.ok.dbl.lin.pres γ Ψ hΨ
  obtain ⟨g₀, hg₀⟩ := PositivityTheory.ThKF0.Resc.rat_mat (inv_mem hγ)
  obtain ⟨g₁, hg₁⟩ := PositivityTheory.ThKF0.Resc.rat_mat hγ
  have hinj : Function.Injective (incM F : Matrix (Fin d.m) (Fin d.m) E → Matrix (Fin d.m) (Fin d.m) (AE F E)) :=
    PositivityTheory.SiegelWeilFormula.kfour.incM_injective
  have hmul : ∀ {p q r : ℕ} (A : Matrix (Fin p) (Fin q) E) (B : Matrix (Fin q) (Fin r) E),
      incM F (A * B) = incM F A * incM F B := fun A B => Matrix.map_mul (f := inclR (F := F) (E := E) (AF F))
  have hone : incM F (1 : Matrix (Fin d.m) (Fin d.m) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have e01 : g₀ * g₁ = 1 := hinj (by
    rw [hmul, ← hg₀, ← hg₁, hone]
    have := congrArg (fun u : UA σ d.A.J => ((u.1 : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)))
      (inv_mul_cancel γ)
    simp at this; simpa using this)
  have e10 : g₁ * g₀ = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).1 e01
  let e : Matrix (Fin d.m) (Fin d.n) E ≃ Matrix (Fin d.m) (Fin d.n) E :=
    ⟨fun X => g₀ * X, fun X => g₁ * X, fun X => by simp [← Matrix.mul_assoc, e10], fun X => by simp [← Matrix.mul_assoc, e01]⟩
  have h1 := (hT F E σ d (d.S γ Ψ) hS).1
  have h2 := (hT F E σ d Ψ hΨ).1
  have h3 : HasSum (fun X : Matrix (Fin d.m) (Fin d.n) E => d.T Ψ (incM F (e X))) (thetaSum F (d.S γ Ψ)) := by
    refine h1.congr_fun fun X => ?_
    rw [(hP F E σ d Ψ hΨ).2.2 γ (incM F X)]
    simp only [e, Equiv.coe_fn_mk, hmul, mat, ← hg₀]
  exact h3.unique ((e.hasSum_iff).2 h2)

end PositivityTheory.SiegelWeilFormula.Tauto

end
