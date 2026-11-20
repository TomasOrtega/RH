import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittFrameTorusEqLeviElement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.ArchLineSum

open GlobalTheory.SplitScalar GlobalTheory.LatVac

variable {D : D7}

/- English proof (translation)
Apply `(InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective` to reduce the goal to its premises. Use `show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm _) = _`. Rewrite using `[RingEquiv.apply_symm_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]`. Use extensionality with `w`. Use `show t = InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w.1)).symm t)`.

Conclude with `((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w.1)).apply_symm_apply t).symm`. Conclude with `absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.2 w.2)`.
-/
theorem fstA_realAd (t : ℝ) : fstA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) = fstA D.host.F (GlobalTheory.WittLevi.realAd D t) := by
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective
  show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm _) = _
  rw [RingEquiv.apply_symm_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  ext w
  · show t = InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
      ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w.1)).symm t)
    exact ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w.1)).apply_symm_apply t).symm
  · exact absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.2 w.2)

/- English proof (translation)
Use `show fstA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E) = fstA D.host.F (GlobalTheory.WittLevi.realAd D t) ⊗ₜ[D.host.F] (1 : D.host.E)`. Rewrite using `[fstA_realAd]`.
-/
theorem infPart_realAd (t : ℝ) : infPart D (algebraMap (AF D.host.F) (AE D) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t)) =
    infPart D (GlobalTheory.WittLevi.realE D t) := by
  show fstA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E) = fstA D.host.F (GlobalTheory.WittLevi.realAd D t) ⊗ₜ[D.host.F] (1 : D.host.E)
  rw [fstA_realAd]

/- English proof (translation)
Rewrite using `[infPart_realAd]`. Conclude with `GlobalTheory.WittLevi.theta_realE hθ ρ t`.
-/
theorem theta_realAd {θ : InfFam D} (hθ : IsInfFam θ) (ρ : D.what₂.Tau) (t : ℝ) :
    θ ρ (infPart D (algebraMap (AF D.host.F) (AE D) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t))) = t := by
  rw [infPart_realAd]; exact GlobalTheory.WittLevi.theta_realE hθ ρ t

/- English proof (translation)
Rewrite using `[Algebra.smul_def, map_mul]`. Both sides reduce to the same expression.
-/
theorem finPart_smul (u : AF D.host.F) (a : AE D) :
    finPart D (u • a) = (sndA D.host.F u ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D a := by
  rw [Algebra.smul_def, map_mul]; rfl

/- English proof (translation)
Rewrite using `[Algebra.smul_def, map_mul]`.
-/
theorem infPart_smul (u : AF D.host.F) (a : AE D) :
    infPart D (u • a) = infPart D (algebraMap (AF D.host.F) (AE D) u) * infPart D a := by
  rw [Algebra.smul_def, map_mul]

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Establish `hL : ∀ τ, IsLineAt θ τ (compAt θ τ w) (lineAt θ τ (compAt θ τ w))` using `fun τ => Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ _)`. Use extensionality with `i j`. Rewrite using `[← sub_eq_zero]`. Apply `GlobalTheory.StdUnn.RealComp.eq_zero_of_parts` to reduce the goal to its premises. Rewrite using `[← GlobalTheory.StdUnn.RealComp.theta_zero_iff hθ]`.

Introduce `ρ`. Rewrite using `[(infPart D).map_sub, (θ ρ).map_sub, sub_eq_zero, Matrix.sum_apply, map_sum (infPart D), map_sum (θ ρ)]`. Establish `e1 : ∀ τ, θ ρ (infPart D (lineAt θ τ (compAt θ τ w) t i j)) = if ρ = τ then (t : ℂ) * θ ρ (infPart D (w i j)) else 0`. Introduce `τ`. Use `congrFun (congrFun ((hL τ).2.2 t ρ) i) j` as an intermediate fact.

Express the relevant statement in the definitionally equal form `θ ρ (infPart D (lineAt θ τ (compAt θ τ w) t i j)) = _ at this`. Rewrite using `[this]`. Use `split_ifs with h`. Substitute `h` using the available equality. Both sides reduce to the same expression.

Both sides reduce to the same expression. Rewrite using `[Finset.sum_congr rfl fun τ _ => e1 τ, Finset.sum_ite_eq Finset.univ ρ, if_pos (Finset.mem_univ _)]`. Use `show θ ρ (infPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w i j)) = _`. Rewrite using `[infPart_smul, (θ ρ).map_mul, theta_realAd hθ]`. Rewrite using `[(finPart D).map_sub, sub_eq_zero, Matrix.sum_apply, map_sum (finPart D)] show finPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w i j) = _`.

Rewrite using `[finPart_smul, show sndA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) = 0 from rfl, TensorProduct.zero_tmul, zero_mul]`. Conclude with `(Finset.sum_eq_zero fun τ _ => congrFun (congrFun ((hL τ).2.1 t) i) j).symm`.
-/
theorem realAd_smul_eq {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {w : WO S T}
    (hw : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) w) (t : ℝ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w = ∑ τ, lineAt θ τ (compAt θ τ w) t := by
  classical
  have hL : ∀ τ, IsLineAt θ τ (compAt θ τ w) (lineAt θ τ (compAt θ τ w)) := fun τ =>
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ _)
  ext i j
  rw [← sub_eq_zero]
  apply GlobalTheory.StdUnn.RealComp.eq_zero_of_parts
  · rw [← GlobalTheory.StdUnn.RealComp.theta_zero_iff hθ]
    intro ρ
    rw [(infPart D).map_sub, (θ ρ).map_sub, sub_eq_zero, Matrix.sum_apply, map_sum (infPart D), map_sum (θ ρ)]
    have e1 : ∀ τ, θ ρ (infPart D (lineAt θ τ (compAt θ τ w) t i j)) =
        if ρ = τ then (t : ℂ) * θ ρ (infPart D (w i j)) else 0 := by
      intro τ
      have := congrFun (congrFun ((hL τ).2.2 t ρ) i) j
      change θ ρ (infPart D (lineAt θ τ (compAt θ τ w) t i j)) = _ at this
      rw [this]
      split_ifs with h
      · subst h; rfl
      · rfl
    rw [Finset.sum_congr rfl fun τ _ => e1 τ, Finset.sum_ite_eq Finset.univ ρ, if_pos (Finset.mem_univ _)]
    show θ ρ (infPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w i j)) = _
    rw [infPart_smul, (θ ρ).map_mul, theta_realAd hθ]
  · rw [(finPart D).map_sub, sub_eq_zero, Matrix.sum_apply, map_sum (finPart D)]
    show finPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w i j) = _
    rw [finPart_smul, show sndA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) = 0 from rfl, TensorProduct.zero_tmul,
      zero_mul]
    exact (Finset.sum_eq_zero fun τ _ => congrFun (congrFun ((hL τ).2.1 t) i) j).symm

end GlobalTheory.ArchLineSum

namespace GlobalTheory.ArchLineSum

open GlobalTheory.SplitScalar GlobalTheory.LatVac

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `D ψ θ hψ hθ S T f hf w hw x`. Establish `hc : Continuous ψ` using `hψ.1.1`. Establish `hL : ∀ τ, IsLineAt θ τ (compAt θ τ w) (lineAt θ τ (compAt θ τ w))` using `fun τ => Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ _)`. Set `Λ : (D.what₂.Tau → ℝ) →+ WO S T` to `∑ τ, (lineAt θ τ (compAt θ τ w)).comp (Pi.evalAddMonoidHom (fun _ : D.what₂.Tau => ℝ) τ)`. Establish `hΛ : ∀ s, Λ s = ∑ τ, lineAt θ τ (compAt θ τ w) (s τ)` using `fun s => by`.

Simplify using `[Λ, AddMonoidHom.finset_sum_apply]`. Establish `hΛc : Continuous Λ`. Rewrite using `[show (Λ : (D.what₂.Tau → ℝ) → WO S T) = fun s => ∑ τ, lineAt θ τ (compAt θ τ w) (s τ) from funext hΛ]`. Conclude with `continuous_finset_sum _ fun τ _ => (hL τ).1.comp (continuous_apply τ)`. Establish `hΛf : ∀ s, (Λ s).map (finPart D) = 0` using `fun s => by`.

Use extensionality with `i j`. Rewrite using `[hΛ]`. Use `show finPart D ((∑ τ, lineAt θ τ (compAt θ τ w) (s τ) : WO S T) i j) = 0`. Rewrite using `[Matrix.sum_apply, map_sum (finPart D)]`. Conclude with `Finset.sum_eq_zero fun τ _ => congrFun (congrFun ((hL τ).2.1 (s τ)) i) j`.

Set `G : (D.what₂.Tau → ℝ) → ℂ` to `fun s => heisO ψ S T (Λ s) f x`. Establish `hχ : ∀ τ, Differentiable ℝ fun t : ℝ => ψ (symplOH S T x (lineAt θ τ (compAt θ τ w) t))` using `fun τ => by`. Use `GlobalTheory.FockTranslate.differentiable_of_char _ (hc.comp (continuous_const.mul (continuous_symplO S T continuous_const (hL τ).1))) ?_ ?_` and prove the remaining obligations. Rewrite using `[map_zero, symplOH, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one]`. Introduce `s t`.

Rewrite using `[map_add, symplOH_add_right, AddChar.map_add_eq_mul]`. Establish `hpsi : ∀ s, ψ (symplOH S T x (Λ s)) = ∏ τ, ψ (symplOH S T x (lineAt θ τ (compAt θ τ w) (s τ)))`. Introduce `s`. Rewrite using `[hΛ]`. Set `φ : WO S T →+ AF D.host.F` to `⟨⟨symplOH S T x, by rw [symplOH, symplO_zero_right, mul_zero]⟩, symplOH_add_right S T x⟩`.

Establish `key : ∀ (s' : Finset D.what₂.Tau) (g : D.what₂.Tau → WO S T), ψ (φ (∑ τ ∈ s', g τ)) = ∏ τ ∈ s', ψ (φ (g τ))`. Introduce `s' g`. Proceed by induction on `s' using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty, Finset.prod_empty, map_zero, AddChar.map_zero_eq_one]`. Consider the case `insert a s' ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, map_add, AddChar.map_add_eq_mul, ih]`.

Conclude with `key Finset.univ _`. Establish `hGd : Differentiable ℝ G`. Establish `h1 : Differentiable ℝ fun s : D.what₂.Tau → ℝ => ψ (symplOH S T x (Λ s))`. Simplify using `only [hpsi]`. Establish `hp : ∀ s' : Finset D.what₂.Tau, Differentiable ℝ fun s : D.what₂.Tau → ℝ => ∏ τ ∈ s', ψ (symplOH S T x (lineAt θ τ (compAt θ τ w) (s τ)))`.

Introduce `s'`. Proceed by induction on `s' using Finset.induction_on with`. Consider the case `empty => simp only [Finset.prod_empty]`. Conclude with `differentiable_const _`. Consider the case `insert a s' ha ih`.

Simplify using `only [Finset.prod_insert ha]`. Establish `hτ : Differentiable ℝ fun s : D.what₂.Tau → ℝ => s a` using `differentiable_apply a`. Conclude with `((hχ a).comp hτ).mul ih`. Conclude with `hp Finset.univ`. Establish `h2 : Differentiable ℝ fun s : D.what₂.Tau → ℝ => f (x + Λ s)`.

Set `e` to `Fintype.equivFin D.what₂.Tau`. Set `ℓ : (Fin (Fintype.card D.what₂.Tau) → ℝ) ≃L[ℝ] (D.what₂.Tau → ℝ)` to `(LinearEquiv.funCongrLeft ℝ ℝ e).toContinuousLinearEquiv`. Establish `hs` using `hf.smooth _ (Λ.comp (ℓ : (Fin (Fintype.card D.what₂.Tau) → ℝ) →+ (D.what₂.Tau → ℝ))) (hΛc.comp ℓ.continuous) (fun t => hΛf _) x`. Establish `: (fun s : D.what₂.Tau → ℝ => f (x + Λ s)) = (fun t => f (x + Λ.comp (ℓ : (Fin (Fintype.card D.what₂.Tau) → ℝ) →+ (D.what₂.Tau → ℝ)) t)) ∘ ℓ.symm`. Use function extensionality and compare the values at `s`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `(hs.differentiable (by simp)).comp ℓ.symm.differentiable`. Conclude with `h1.mul h2`. Establish `hfun : (fun t : ℝ => heisO ψ S T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w) f x) = G ∘ (fun t : ℝ => fun _ : D.what₂.Tau => t)`.

Use function extensionality and compare the values at `t`. Simplify using `only [Function.comp, G, hΛ]`. Rewrite using `[realAd_smul_eq hθ hw t]`. Establish `hdiag : HasDerivAt (fun t : ℝ => (fun _ : D.what₂.Tau => t)) (fun _ => (1 : ℝ)) 0` using `hasDerivAt_pi.2 fun _ => hasDerivAt_id 0`. Establish `hG0 : HasFDerivAt G (fderiv ℝ G 0) ((fun t : ℝ => fun _ : D.what₂.Tau => t) 0)` using `(hGd 0).hasFDerivAt`.

Establish `hcomp` using `hG0.comp_hasDerivAt (0 : ℝ) hdiag`. Rewrite using `[hfun]`. It suffices to establish `key : fderiv ℝ G 0 (fun _ => 1) = ∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ w) f x by`. Rewrite using `[← key]`. Conclude with `hcomp`.

Rewrite using `[show (fun _ : D.what₂.Tau => (1 : ℝ)) = ∑ τ, Pi.single τ (1 : ℝ) from (Finset.univ_sum_single _).symm, map_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `hline : HasDerivAt (fun t : ℝ => t • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ)) ((1 : ℝ) • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ)) 0` using `(hasDerivAt_id 0).smul_const _`. Establish `hG0' : HasFDerivAt G (fderiv ℝ G 0) ((fun t : ℝ => t • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ)) 0)`. Simplify using `using (hGd 0).hasFDerivAt`.

Establish `h3` using `hG0'.comp_hasDerivAt (0 : ℝ) hline`. Rewrite `h3` using `[one_smul]`. Establish `e : (G ∘ fun t : ℝ => t • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ)) = fun t => heisO ψ S T (lineAt θ τ (compAt θ τ w) t) f x`. Use function extensionality and compare the values at `t`. Simplify using `only [Function.comp, G, hΛ]`.

Rewrite using `[Finset.sum_eq_single τ (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]`. Simplify using the standard rewrite rules. Rewrite `h3` using `[e]`. Conclude with `h3.deriv.symm`.
-/
theorem hasDerivAt_realAd_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ S T f →
    ∀ w : WO S T, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) w → ∀ x : WO S T,
      HasDerivAt (fun t : ℝ => heisO ψ S T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w) f x)
        (∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ w) f x) 0 := by
  intro D ψ θ hψ hθ S T f hf w hw x
  classical
  have hc : Continuous ψ := hψ.1.1
  have hL : ∀ τ, IsLineAt θ τ (compAt θ τ w) (lineAt θ τ (compAt θ τ w)) := fun τ =>
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ _)
  let Λ : (D.what₂.Tau → ℝ) →+ WO S T :=
    ∑ τ, (lineAt θ τ (compAt θ τ w)).comp (Pi.evalAddMonoidHom (fun _ : D.what₂.Tau => ℝ) τ)
  have hΛ : ∀ s, Λ s = ∑ τ, lineAt θ τ (compAt θ τ w) (s τ) := fun s => by
    simp [Λ, AddMonoidHom.finset_sum_apply]
  have hΛc : Continuous Λ := by
    rw [show (Λ : (D.what₂.Tau → ℝ) → WO S T) = fun s => ∑ τ, lineAt θ τ (compAt θ τ w) (s τ) from funext hΛ]
    exact continuous_finset_sum _ fun τ _ => (hL τ).1.comp (continuous_apply τ)
  have hΛf : ∀ s, (Λ s).map (finPart D) = 0 := fun s => by
    ext i j
    rw [hΛ]
    show finPart D ((∑ τ, lineAt θ τ (compAt θ τ w) (s τ) : WO S T) i j) = 0
    rw [Matrix.sum_apply, map_sum (finPart D)]
    exact Finset.sum_eq_zero fun τ _ => congrFun (congrFun ((hL τ).2.1 (s τ)) i) j
  let G : (D.what₂.Tau → ℝ) → ℂ := fun s => heisO ψ S T (Λ s) f x
  have hχ : ∀ τ, Differentiable ℝ fun t : ℝ => ψ (symplOH S T x (lineAt θ τ (compAt θ τ w) t)) := fun τ => by
    refine GlobalTheory.FockTranslate.differentiable_of_char _
      (hc.comp (continuous_const.mul (continuous_symplO S T continuous_const (hL τ).1))) ?_ ?_
    · rw [map_zero, symplOH, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one]
    · intro s t
      rw [map_add, symplOH_add_right, AddChar.map_add_eq_mul]
  have hpsi : ∀ s, ψ (symplOH S T x (Λ s)) = ∏ τ, ψ (symplOH S T x (lineAt θ τ (compAt θ τ w) (s τ))) := by
    intro s
    rw [hΛ]
    let φ : WO S T →+ AF D.host.F :=
      ⟨⟨symplOH S T x, by rw [symplOH, symplO_zero_right, mul_zero]⟩, symplOH_add_right S T x⟩
    have key : ∀ (s' : Finset D.what₂.Tau) (g : D.what₂.Tau → WO S T),
        ψ (φ (∑ τ ∈ s', g τ)) = ∏ τ ∈ s', ψ (φ (g τ)) := by
      intro s' g
      induction s' using Finset.induction_on with
      | empty => rw [Finset.sum_empty, Finset.prod_empty, map_zero, AddChar.map_zero_eq_one]
      | insert a s' ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, map_add, AddChar.map_add_eq_mul, ih]
    exact key Finset.univ _
  have hGd : Differentiable ℝ G := by
    have h1 : Differentiable ℝ fun s : D.what₂.Tau → ℝ => ψ (symplOH S T x (Λ s)) := by
      simp only [hpsi]
      have hp : ∀ s' : Finset D.what₂.Tau, Differentiable ℝ fun s : D.what₂.Tau → ℝ =>
          ∏ τ ∈ s', ψ (symplOH S T x (lineAt θ τ (compAt θ τ w) (s τ))) := by
        intro s'
        induction s' using Finset.induction_on with
        | empty => simp only [Finset.prod_empty]; exact differentiable_const _
        | insert a s' ha ih =>
          simp only [Finset.prod_insert ha]
          have hτ : Differentiable ℝ fun s : D.what₂.Tau → ℝ => s a := differentiable_apply a
          exact ((hχ a).comp hτ).mul ih
      exact hp Finset.univ
    have h2 : Differentiable ℝ fun s : D.what₂.Tau → ℝ => f (x + Λ s) := by
      let e := Fintype.equivFin D.what₂.Tau
      let ℓ : (Fin (Fintype.card D.what₂.Tau) → ℝ) ≃L[ℝ] (D.what₂.Tau → ℝ) :=
        (LinearEquiv.funCongrLeft ℝ ℝ e).toContinuousLinearEquiv
      have hs := hf.smooth _ (Λ.comp (ℓ : (Fin (Fintype.card D.what₂.Tau) → ℝ) →+ (D.what₂.Tau → ℝ)))
        (hΛc.comp ℓ.continuous) (fun t => hΛf _) x
      have : (fun s : D.what₂.Tau → ℝ => f (x + Λ s)) =
          (fun t => f (x + Λ.comp (ℓ : (Fin (Fintype.card D.what₂.Tau) → ℝ) →+ (D.what₂.Tau → ℝ)) t)) ∘ ℓ.symm := by
        funext s
        simp
      rw [this]
      exact (hs.differentiable (by simp)).comp ℓ.symm.differentiable
    exact h1.mul h2
  have hfun : (fun t : ℝ => heisO ψ S T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w) f x) =
      G ∘ (fun t : ℝ => fun _ : D.what₂.Tau => t) := by
    funext t
    simp only [Function.comp, G, hΛ]
    rw [realAd_smul_eq hθ hw t]
  have hdiag : HasDerivAt (fun t : ℝ => (fun _ : D.what₂.Tau => t)) (fun _ => (1 : ℝ)) 0 :=
    hasDerivAt_pi.2 fun _ => hasDerivAt_id 0
  have hG0 : HasFDerivAt G (fderiv ℝ G 0) ((fun t : ℝ => fun _ : D.what₂.Tau => t) 0) := (hGd 0).hasFDerivAt
  have hcomp := hG0.comp_hasDerivAt (0 : ℝ) hdiag
  rw [hfun]
  suffices key : fderiv ℝ G 0 (fun _ => 1) = ∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ w) f x by
    rw [← key]; exact hcomp
  rw [show (fun _ : D.what₂.Tau => (1 : ℝ)) = ∑ τ, Pi.single τ (1 : ℝ) from (Finset.univ_sum_single _).symm, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hline : HasDerivAt (fun t : ℝ => t • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ))
      ((1 : ℝ) • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ)) 0 := (hasDerivAt_id 0).smul_const _
  have hG0' : HasFDerivAt G (fderiv ℝ G 0) ((fun t : ℝ => t • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ)) 0) := by
    simpa using (hGd 0).hasFDerivAt
  have h3 := hG0'.comp_hasDerivAt (0 : ℝ) hline
  rw [one_smul] at h3
  have e : (G ∘ fun t : ℝ => t • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ)) =
      fun t => heisO ψ S T (lineAt θ τ (compAt θ τ w) t) f x := by
    funext t
    simp only [Function.comp, G, hΛ]
    rw [Finset.sum_eq_single τ (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
    simp
  rw [e] at h3
  exact h3.deriv.symm

end GlobalTheory.ArchLineSum
