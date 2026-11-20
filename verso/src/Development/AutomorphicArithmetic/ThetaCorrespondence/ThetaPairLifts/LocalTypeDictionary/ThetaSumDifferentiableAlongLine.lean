import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacter
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSmoothLinePureWeight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacterStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
noncomputable section
open scoped Classical
namespace GlobalTheory.ThetaLineDer
/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hcm hψ hG hW γ hγ m f f₁ φ hφ hD u`. Establish `hstd : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1` using `fun i => ((hφ i).2.and hG.std).mono fun v h => h.1.trans h.2`. Establish `hmem : ∀ i (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (φ i) ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d)` using `fun i g => GlobalTheory.TensUniq.pure_mem_schA g (φ i) (hφ i).1 (hstd i)`. Use `choose c g hc hlim using fun i => _root_.GlobalTheory.T.twisted_smoothLine_pure_weight hP M ψ χX χW om hcm hψ hG hW γ hγ (f i) (φ i) (hφ i).1 (hφ i).2`. Use `choose Λ hΛ using fun i => GlobalTheory.ThetaHeisCLM.exists_clm_thetaSum_rho_pure M ψ hψ hG u (φ i) (hφ i).1 (hφ i).2`.

Establish `hcurve : (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i))))) = fun t => ∑ i, Λ i (c i t)`. Use function extensionality and compare the values at `t`. Rewrite using `[map_sum]`. Simplify using `only [hc]`. Rewrite using `[rho_sum M ψ hψ u _ (fun i => hmem i _)]`.

Simplify using `only [hΛ]`. Establish `hg : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g i) (φ i) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)`. Introduce `i`. Use function extensionality and compare the values at `x`. Establish `hR` using `GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hφ i).1 (hstd i)`.

Establish `h1` using `hD i _ hR x`. Establish `ev : Continuous fun s : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) => s (fun j => evI F (x j))`. Establish `h1` using `(SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ).continuous`. Establish `h2` using `(continuous_eval_const (F := BoundedContinuousFunction (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ) (fun j => evI F (x j))).comp h1`. Conclude with `h2`.

Establish `h2 : HasDerivAt (fun t : ℝ => c i t (fun j => evI F (x j)) * ∏ᶠ v, φ i v fun j => evFin F v (x j)) (g i (fun j => evI F (x j)) * ∏ᶠ v, φ i v fun j => evFin F v (x j)) 0`. Rewrite using `[hasDerivAt_iff_tendsto_slope]`. Conclude with `(((ev.tendsto (g i)).comp (hlim i)).mul_const _).congr' (Filter.Eventually.of_forall fun t => schwartz_diffQuotient_eval_mul_eq_slope _ _ _ t)`. Establish `h3 : (fun t : ℝ => c i t (fun j => evI F (x j)) * ∏ᶠ v, φ i v fun j => evFin F v (x j)) = fun t => om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evI F) (⇑(f i)) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j))) x`. Use function extensionality and compare the values at `t`.

Use `show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c i t) (φ i) x = om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x`. Rewrite using `[hc i t]`. Rewrite `h2` using `[h3]`. Conclude with `h2.unique h1`. Establish `hend : GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i))) = ∑ i, Λ i (g i)`.

Rewrite using `[rho_sum M ψ hψ u _ (fun i => hmem i _)]`. Simplify using `only [← hg, hΛ]`. Establish `hc0 : ∀ i, HasDerivAt (fun t => Λ i (c i t)) (Λ i (g i)) 0`. Introduce `i`. Rewrite using `[hasDerivAt_iff_tendsto_slope]`.

Use `((Λ i).continuous.tendsto (g i) |>.comp (hlim i)).congr' (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `[slope_def_module, map_sub, map_smul]`. Rewrite using `[hcurve, hend]`. Use `HasDerivAt.sum (u := Finset.univ) fun i _ => hc0 i` as an intermediate fact. Simplify `this` using `[Finset.sum_fn]`.
-/
theorem hasDerivAt_theta_sum_along_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Wd, ∀ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
    (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))))
      (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)))) 0 := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hcm hψ hG hW γ hγ m f f₁ φ hφ hD u
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 :=
    fun i => ((hφ i).2.and hG.std).mono fun v h => h.1.trans h.2
  have hmem : ∀ i (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (φ i) ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun i g => GlobalTheory.TensUniq.pure_mem_schA g (φ i) (hφ i).1 (hstd i)
  choose c g hc hlim using fun i => _root_.GlobalTheory.T.twisted_smoothLine_pure_weight hP M ψ χX χW om hcm hψ hG hW γ hγ (f i) (φ i) (hφ i).1 (hφ i).2
  choose Λ hΛ using fun i => GlobalTheory.ThetaHeisCLM.exists_clm_thetaSum_rho_pure M ψ hψ hG u (φ i) (hφ i).1 (hφ i).2
  have hcurve : (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))))
      = fun t => ∑ i, Λ i (c i t) := by
    funext t
    rw [map_sum]
    simp only [hc]
    rw [rho_sum M ψ hψ u _ (fun i => hmem i _)]
    simp only [hΛ]
  have hg : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g i) (φ i) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i) := by
    intro i
    funext x
    have hR := GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hφ i).1 (hstd i)
    have h1 := hD i _ hR x
    have ev : Continuous fun s : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) => s (fun j => evI F (x j)) :=
      by
        have h1 := (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ).continuous
        have h2 := (continuous_eval_const (F := BoundedContinuousFunction (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)
          (fun j => evI F (x j))).comp h1
        exact h2
    have h2 : HasDerivAt (fun t : ℝ => c i t (fun j => evI F (x j)) * ∏ᶠ v, φ i v fun j => evFin F v (x j))
        (g i (fun j => evI F (x j)) * ∏ᶠ v, φ i v fun j => evFin F v (x j)) 0 := by
      rw [hasDerivAt_iff_tendsto_slope]
      exact (((ev.tendsto (g i)).comp (hlim i)).mul_const _).congr' (Filter.Eventually.of_forall fun t => schwartz_diffQuotient_eval_mul_eq_slope _ _ _ t)
    have h3 : (fun t : ℝ => c i t (fun j => evI F (x j)) * ∏ᶠ v, φ i v fun j => evFin F v (x j)) =
        fun t => om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evI F) (⇑(f i)) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j))) x := by
      funext t
      show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c i t) (φ i) x = om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x
      rw [hc i t]
    rw [h3] at h2
    exact h2.unique h1
  have hend : GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i))) = ∑ i, Λ i (g i) := by
    rw [rho_sum M ψ hψ u _ (fun i => hmem i _)]
    simp only [← hg, hΛ]
  have hc0 : ∀ i, HasDerivAt (fun t => Λ i (c i t)) (Λ i (g i)) 0 := by
    intro i
    rw [hasDerivAt_iff_tendsto_slope]
    refine ((Λ i).continuous.tendsto (g i) |>.comp (hlim i)).congr' (Filter.Eventually.of_forall fun t => ?_)
    simp [slope_def_module, map_sub, map_smul]
  rw [hcurve, hend]
  have := HasDerivAt.sum (u := Finset.univ) fun i _ => hc0 i
  simpa [Finset.sum_fn] using this
end GlobalTheory.ThetaLineDer
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.ThetaLineDer.hasDerivAt_theta_sum_along_line | exact _root_.GlobalTheory.ThetaLineDer.hasDerivAt_theta_sum_along_line | (intros; apply _root_.GlobalTheory.ThetaLineDer.hasDerivAt_theta_sum_along_line <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.theta_sum_differentiable_along_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Wd, ∀ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
    (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))))
      (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)))) 0 := by
  first | exact @_root_.GlobalTheory.ThetaLineDer.hasDerivAt_theta_sum_along_line | exact _root_.GlobalTheory.ThetaLineDer.hasDerivAt_theta_sum_along_line | (intros; apply _root_.GlobalTheory.ThetaLineDer.hasDerivAt_theta_sum_along_line <;> assumption)
end
