import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOnto
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTPh
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ModelIdentificationRespectsRealAndFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateEvaluationMapIntertwinesRealPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjIntertwinerPointValueSobolevContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIntertwinerValuesSmoothAutomorphic
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

section Gen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct
open GlobalTheory.ConjRowMult Formalism.L2.SG.EvalTOntoRep

namespace GlobalTheory.ConjEvalAut

/- English proof (translation)
Introduce `τ g hg v w hw`. Take `⟨hfin, -, hreal, -⟩` from `GlobalTheory.T.modelIdentification_respects_real_and_finite D X h θ hθ hιE`. Take `⟨ha2, ha1, -⟩` from `hreal τ g hg`. Use `set a := iotaX X h (atTau θ (D.sp.Y 0) τ g) with ha`. Establish `hvec : vecC X M c (Function.update v τ w) = fun p => X.B.σ p (uMat (a.1 p)) (vecC X M c v p)`.

Use `vecC_eq X M c _ _ fun τ' => ?_` and prove the remaining obligations. Establish `e1 : vecC X M c v (X.pl.symm τ') = c τ' (v τ' : M.H τ')`. Unfold `vecC`. Conclude with `Equiv.piCongrLeft_apply_apply _ _ _ _`. Rewrite using `[e1]`.

Distinguish the cases in `ht' : τ' = τ`. Substitute `ht'` using the available equality. Rewrite using `[Function.update_self, hw, hc τ' g hg]`. Rewrite using `[Function.update_of_ne ht', ha1 (X.pl.symm τ') (fun e => ht' (X.pl.symm.injective e))]`. Establish `h1 : X.B.σ (X.pl.symm τ') 1 = 1` using `(X.ds (X.pl.symm τ')).2.2.1.1.1`.

Establish `h2 : uMat (1 : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ'))) = 1` using `rfl`. Rewrite using `[h2, h1]`. Both sides reduce to the same expression. Establish `htens : X.B.tens (vecC X M c (Function.update v τ w)) = X.B.σs a.1 (X.B.tens (vecC X M c v))`. Rewrite using `[hvec, X.B.tens_spec.2.1]`.

Establish `haeq : ((a.1, 1) : X.B.I.GA) = a` using `Prod.ext rfl ha2.symm`. Take `⟨T, hT, hTΦ⟩` from `Submodule.mem_map.1 hΦ`. Establish `hΦx : ∀ x, Φ x = X.B.Re (T x)` using `fun x => by rw [← hTΦ]; rfl`. Establish `hcomm` using `(GlobalTheory.IdemProj.re_orth_proj X.B).2.1 a.1`. Establish `key : ∀ x, Φ (X.B.σs a.1 x) = X.B.R a (Φ x)`.

Introduce `x`. Rewrite using `[hΦx, hΦx, ← haeq]`. Establish `e1` using `congrArg (fun L => L x) (hT a.1)`. Simplify using `only [ContinuousLinearMap.comp_apply] at e1`. Rewrite using `[e1]`.

Conclude with `congrArg (fun L => L (T x)) hcomm`. Take `⟨ψ, hψ⟩` from `hrep v`. Establish `hψ' : IsContRep X (Φ (X.B.tens (vecC X M c (Function.update v τ w)))) (fun x => ψ (x * a))`. Rewrite using `[htens, key]`. Conclude with `contRep_reg X hψ a`.

Use function extensionality and compare the values at `y`. Rewrite using `[conjMap_apply, contRepL_spec X hψ']`. Use `show _ = conjMap X M c Φ h t v (y * atTau θ (D.sp.Y 0) τ g)`. Rewrite using `[conjMap_apply, contRepL_spec X hψ]`. Use `congr 1`.

Establish `hti : (iotaX X h t⁻¹).1 = 1` using `by rw [map_inv, Prod.fst_inv, (hfin t).1 ht, inv_one]`. Rewrite using `[map_mul, map_mul, map_mul, ← ha, mul_assoc]`. Use `beta_reduce`. Rewrite using `[mul_assoc]`. Use `congr 2`.

Conclude with `Prod.ext (by rw [Prod.fst_mul, Prod.fst_mul, hti, one_mul, mul_one]) (by rw [Prod.snd_mul, Prod.snd_mul, ha2, one_mul, mul_one])`.
-/
theorem equiv_gen {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (θ : InfFam D) {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (t : GA D (D.sp.Y 0))
    (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (hθ : IsInfFam θ) (hιE : ∀ x : X.B.I.E, HEq (X.ιE x) x)
    (ht : t ∈ GfC (D.sp.Y 0))
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w))
    (Φ : X.B.Hs →L[ℂ] L2X X) (hΦ : Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re)
    (hrep : ∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) :
    ∀ τ : D.what₂.Tau, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) = rTr (D.sp.Y 0) (atTau θ (D.sp.Y 0) τ g) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t v) := by
  intro τ g hg v w hw
  obtain ⟨hfin, -, hreal, -⟩ := GlobalTheory.T.modelIdentification_respects_real_and_finite D X h θ hθ hιE
  obtain ⟨ha2, ha1, -⟩ := hreal τ g hg
  set a := iotaX X h (atTau θ (D.sp.Y 0) τ g) with ha
  have hvec : vecC X M c (Function.update v τ w) =
      fun p => X.B.σ p (uMat (a.1 p)) (vecC X M c v p) := by
    refine vecC_eq X M c _ _ fun τ' => ?_
    have e1 : vecC X M c v (X.pl.symm τ') = c τ' (v τ' : M.H τ') := by
      unfold vecC
      exact Equiv.piCongrLeft_apply_apply _ _ _ _
    rw [e1]
    by_cases ht' : τ' = τ
    · subst ht'
      rw [Function.update_self, hw, hc τ' g hg]
    · rw [Function.update_of_ne ht', ha1 (X.pl.symm τ') (fun e => ht' (X.pl.symm.injective e))]
      have h1 : X.B.σ (X.pl.symm τ') 1 = 1 := (X.ds (X.pl.symm τ')).2.2.1.1.1
      have h2 : uMat (1 : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ'))) = 1 := rfl
      rw [h2, h1]
      rfl
  have htens : X.B.tens (vecC X M c (Function.update v τ w)) = X.B.σs a.1 (X.B.tens (vecC X M c v)) := by
    rw [hvec, X.B.tens_spec.2.1]
  have haeq : ((a.1, 1) : X.B.I.GA) = a := Prod.ext rfl ha2.symm
  obtain ⟨T, hT, hTΦ⟩ := Submodule.mem_map.1 hΦ
  have hΦx : ∀ x, Φ x = X.B.Re (T x) := fun x => by rw [← hTΦ]; rfl
  have hcomm := (GlobalTheory.IdemProj.re_orth_proj X.B).2.1 a.1
  have key : ∀ x, Φ (X.B.σs a.1 x) = X.B.R a (Φ x) := by
    intro x
    rw [hΦx, hΦx, ← haeq]
    have e1 := congrArg (fun L => L x) (hT a.1)
    simp only [ContinuousLinearMap.comp_apply] at e1
    rw [e1]
    exact congrArg (fun L => L (T x)) hcomm
  obtain ⟨ψ, hψ⟩ := hrep v
  have hψ' : IsContRep X (Φ (X.B.tens (vecC X M c (Function.update v τ w)))) (fun x => ψ (x * a)) := by
    rw [htens, key]
    exact contRep_reg X hψ a
  funext y
  rw [conjMap_apply, contRepL_spec X hψ']
  show _ = conjMap X M c Φ h t v (y * atTau θ (D.sp.Y 0) τ g)
  rw [conjMap_apply, contRepL_spec X hψ]
  congr 1
  have hti : (iotaX X h t⁻¹).1 = 1 := by rw [map_inv, Prod.fst_inv, (hfin t).1 ht, inv_one]
  rw [map_mul, map_mul, map_mul, ← ha, mul_assoc]
  beta_reduce
  rw [mul_assoc]
  congr 2
  exact Prod.ext (by rw [Prod.fst_mul, Prod.fst_mul, hti, one_mul, mul_one])
    (by rw [Prod.snd_mul, Prod.snd_mul, ha2, one_mul, mul_one])

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `τ₀ v₀ x₀`. Take `⟨_, _, _, _, _, -, _⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (D.sp.Y 0)`. Take `⟨hf, -, hat, -⟩` from `GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h θ hθ hE`. Take `⟨-, hcomm, g, hg, hfix⟩` from `GlobalTheory.IdemProj.re_orth_proj X.B`. Use `X.B.sf` as an intermediate fact.

Use `X.B.haar` as an intermediate fact. Set `T : GA D (D.sp.Y 0) ≃* X.B.I.GA` to `(iotaX X h).toMulEquiv`. Establish `hT : Continuous T` using `(iotaX X h).continuous`. Establish `hT' : Continuous T.symm` using `(iotaX X h).symm.continuous`. Take `⟨μ, ρ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩` from `GlobalTheory.TensRep.exists_transport X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec T hT hT'`.

Take `⟨U, hU, hUg⟩` from `h11 g hg`. Establish `hA : Φ ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R`. Take `⟨A, hA, rfl⟩` from `hΦ`. Introduce `g`. Use `show (X.B.Re.comp A).comp (X.B.σs g) = (X.B.R (g, 1)).comp (X.B.Re.comp A)`.

Rewrite using `[ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g, ContinuousLinearMap.comp_assoc]`. Establish `hlev : ∀ k ∈ X.B.I.Kg g, ∀ w, X.B.R (1, k) (Φ w) = Φ w`. Take `⟨A, -, rfl⟩` from `hΦ`. Introduce `k hk w`. Conclude with `congrArg (fun C : L2X X →L[ℂ] L2X X => C (A w)) (hfix k hk)`.

Take `⟨Ψ, hΨ⟩` from `GlobalTheory.ConjRowCont.exists_conj_multilinear X M c Φ`. Take `⟨N, hN1, hN2, hN3⟩` from `GlobalTheory.TensRep.exists_mmap (ι := fun v x => X.B.I.ext v (T x)) hθ M h1 h2 h5 h6 h7 h8 h9 (fun γ hγ v => h10 γ ((GlobalTheory.ConjRowCont.iotaX_rat_iff X h γ).1 hγ) v) hU Ψ (fun τ a ha y => by`. Take `⟨q1, q2, -⟩` from `hat τ a ha`. Rewrite using `[h3, hΨ, hΨ, GlobalTheory.ConjRowCont.reg_star]`. Use `congr 1`.

Use `GlobalTheory.TensRep.hom_tens X.B.I X.B.tens_spec hA q1 _ _ fun v => ?_` and prove the remaining obligations. Take `⟨τ', rfl⟩` from `X.pl.symm.surjective v`. Rewrite using `[Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]`. Distinguish the cases in `e : τ' = τ`. Substitute `e` using the available equality.

Rewrite using `[Function.update_self]`. Conclude with `hc _ a ha _`. Rewrite using `[Function.update_of_ne e]`. Establish `q : (iotaX X h (atTau θ (D.sp.Y 0) τ a)).1 (X.pl.symm τ') = 1` using `q2 _ (X.pl.symm.injective.ne e)`. Rewrite using `[q]`.

Establish `: X.B.σ (X.pl.symm τ') 1 = 1` using `(X.ds _).2.2.1.1.1`. Use `show _ = X.B.σ (X.pl.symm τ') 1 _`. Rewrite using `[this]`. Use the proof step `rfl)`. Use the proof step `(fun y k hk hk' => by`.

Rewrite using `[h3, hΨ, GlobalTheory.ConjRowCont.reg_star]`. Establish `e : T k = (1, (T k).2)` using `Prod.ext ((hf k).1 hk') rfl`. Rewrite using `[e, hlev _ (hUg k hk)])`. Establish `key : ∀ (u : M.Vec) y, GlobalTheory.ConjRowMult.conjMap X M c Φ h t u y = N u (y * t⁻¹)`. Introduce `u y`.

Establish `r1 : GlobalTheory.Dec.IsContRep X.B (Ψ fun τ => (u τ : M.H τ)) (fun z => N u (T.symm z))`. Use `GlobalTheory.RepSmooth.isContRep_of_ae X.B ((hN2 u).3.comp hT') (fun γ hγ z => ?_) ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `(hN2 u).1 _ ((GlobalTheory.ConjRowCont.iotaX_rat_iff X h _).2 ?_) _` and prove the remaining obligations. Establish `: iotaX X h (T.symm γ) = γ` using `T.apply_symm_apply γ`.

Rewrite using `[this]` and apply the resulting hypothesis. Use `filter_upwards [h4 _ (hN1 u)] with z hz`. Rewrite using `[← hz, T.apply_symm_apply]`. Establish `r2 : Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) (fun z => star (N u (T.symm z)))`. Use `⟨r1.1.star, fun γ hγ z => congrArg star (r1.2.1 γ hγ z), ?_⟩` and prove the remaining obligations.

Establish `r3` using `r1.2.2`. Rewrite `r3` using `[hΨ]`. Use `filter_upwards [r3, Lp.coeFn_star (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)))] with z a1 a2`. Rewrite using `[← a1]`. Conclude with `(star_star _).symm.trans (congrArg star a2.symm)`.

Rewrite using `[GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.contRepL_spec X r2, star_star]`. Conclude with `congrArg (N u) (T.symm_apply_apply _)`. Take `⟨ℓ, hℓ1, hℓ2⟩` from `hN3 τ₀ v₀ (x₀ * t⁻¹)`. Conclude with `⟨ℓ, hℓ1, fun w => (hℓ2 w).trans (key _ _).symm⟩`.
-/
theorem cont_gen {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (θ : InfFam D) {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (t : GA D (D.sp.Y 0))
    (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (hθ : IsInfFam θ) (hE : ∀ x : X.B.I.E, HEq (X.ιE x) x)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w))
    (Φ : X.B.Hs →L[ℂ] L2X X) (hΦ : Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re)
    (hrep : ∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) :
    ∀ (τ : D.what₂.Tau) (v : M.Vec) (x : GA D (D.sp.Y 0)), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt (D.sp.Y 0) τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) x := by
  intro τ₀ v₀ x₀
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (D.sp.Y 0)
  obtain ⟨hf, -, hat, -⟩ := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h θ hθ hE
  obtain ⟨-, hcomm, g, hg, hfix⟩ := GlobalTheory.IdemProj.re_orth_proj X.B
  have := X.B.sf
  have := X.B.haar
  let T : GA D (D.sp.Y 0) ≃* X.B.I.GA := (iotaX X h).toMulEquiv
  have hT : Continuous T := (iotaX X h).continuous
  have hT' : Continuous T.symm := (iotaX X h).symm.continuous
  obtain ⟨μ, ρ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    GlobalTheory.TensRep.exists_transport X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec T hT hT'
  obtain ⟨U, hU, hUg⟩ := h11 g hg
  have hA : Φ ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R := by
    obtain ⟨A, hA, rfl⟩ := hΦ
    intro g
    show (X.B.Re.comp A).comp (X.B.σs g) = (X.B.R (g, 1)).comp (X.B.Re.comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  have hlev : ∀ k ∈ X.B.I.Kg g, ∀ w, X.B.R (1, k) (Φ w) = Φ w := by
    obtain ⟨A, -, rfl⟩ := hΦ
    intro k hk w
    exact congrArg (fun C : L2X X →L[ℂ] L2X X => C (A w)) (hfix k hk)
  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.ConjRowCont.exists_conj_multilinear X M c Φ
  obtain ⟨N, hN1, hN2, hN3⟩ := GlobalTheory.TensRep.exists_mmap (ι := fun v x => X.B.I.ext v (T x)) hθ M h1 h2 h5 h6 h7 h8 h9
    (fun γ hγ v => h10 γ ((GlobalTheory.ConjRowCont.iotaX_rat_iff X h γ).1 hγ) v) hU Ψ
    (fun τ a ha y => by
      obtain ⟨q1, q2, -⟩ := hat τ a ha
      rw [h3, hΨ, hΨ, GlobalTheory.ConjRowCont.reg_star]
      congr 1
      refine GlobalTheory.TensRep.hom_tens X.B.I X.B.tens_spec hA q1 _ _ fun v => ?_
      obtain ⟨τ', rfl⟩ := X.pl.symm.surjective v
      rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]
      by_cases e : τ' = τ
      · subst e
        rw [Function.update_self]
        exact hc _ a ha _
      · rw [Function.update_of_ne e]
        have q : (iotaX X h (atTau θ (D.sp.Y 0) τ a)).1 (X.pl.symm τ') = 1 := q2 _ (X.pl.symm.injective.ne e)
        rw [q]
        have : X.B.σ (X.pl.symm τ') 1 = 1 := (X.ds _).2.2.1.1.1
        show _ = X.B.σ (X.pl.symm τ') 1 _
        rw [this]
        rfl)
    (fun y k hk hk' => by
      rw [h3, hΨ, GlobalTheory.ConjRowCont.reg_star]
      have e : T k = (1, (T k).2) := Prod.ext ((hf k).1 hk') rfl
      rw [e, hlev _ (hUg k hk)])
  have key : ∀ (u : M.Vec) y, GlobalTheory.ConjRowMult.conjMap X M c Φ h t u y = N u (y * t⁻¹) := by
    intro u y
    have r1 : GlobalTheory.Dec.IsContRep X.B (Ψ fun τ => (u τ : M.H τ)) (fun z => N u (T.symm z)) := by
      refine GlobalTheory.RepSmooth.isContRep_of_ae X.B ((hN2 u).3.comp hT') (fun γ hγ z => ?_) ?_
      · rw [map_mul]
        refine (hN2 u).1 _ ((GlobalTheory.ConjRowCont.iotaX_rat_iff X h _).2 ?_) _
        have : iotaX X h (T.symm γ) = γ := T.apply_symm_apply γ
        rwa [this]
      · filter_upwards [h4 _ (hN1 u)] with z hz
        rw [← hz, T.apply_symm_apply]
    have r2 : Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)))
        (fun z => star (N u (T.symm z))) := by
      refine ⟨r1.1.star, fun γ hγ z => congrArg star (r1.2.1 γ hγ z), ?_⟩
      have r3 := r1.2.2
      rw [hΨ] at r3
      filter_upwards [r3, Lp.coeFn_star (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)))] with z a1 a2
      rw [← a1]
      exact (star_star _).symm.trans (congrArg star a2.symm)
    rw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.contRepL_spec X r2, star_star]
    exact congrArg (N u) (T.symm_apply_apply _)
  obtain ⟨ℓ, hℓ1, hℓ2⟩ := hN3 τ₀ v₀ (x₀ * t⁻¹)
  exact ⟨ℓ, hℓ1, fun w => (hℓ2 w).trans (key _ _).symm⟩

set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `he : GlobalTheory.RepSmooth.IsEquiv θ (GlobalTheory.ConjRowMult.conjMap X M c Φ h t)` using `equiv_gen X h θ M t c hθ hid ht hc Φ hΦ hrep`. Establish `hs : GlobalTheory.RepSmooth.IsSob (GlobalTheory.ConjRowMult.conjMap X M c Φ h t)` using `cont_gen X h θ M t c hθ hid hc Φ hΦ hrep`. Take `⟨hrat, hfst, hsnd, hone, hgr⟩` from `GlobalTheory.ConjRowAut.iota_data θ hθ (fun τ Y hY s => GlobalTheory.SmVec.exp_mem_UH (GlobalTheory.SmVec.gram_unit (M.fr_unit τ) (M.fr_gram τ)) hY s) X.B.I h`. Express the relevant statement in the definitionally equal form `∀ k ∈ _, iotaX X h k ∈ _ at hrat`. Express the relevant statement in the definitionally equal form `∀ k ∈ _, (iotaX X h k).1 = 1 at hfst`.

Express the relevant statement in the definitionally equal form `∀ k ∈ _, (iotaX X h k).2 = 1 at hsnd`. Use `choose f hf using hrep`. Establish `hval : ∀ u y, GlobalTheory.ConjRowMult.conjMap X M c Φ h t u y = star (f u (iotaX X h (y * t⁻¹)))` using `fun u y => by`. Rewrite using `[GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.contRepL_spec X (hf u)]`. Establish `hg : 1 ≤ X.B.g`.

Rewrite using `[X.g_eq]`. Conclude with `Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos`. Establish `hlev : ∀ u, ∀ k ∈ X.B.I.Kg X.B.g, ∀ y, f u (y * (1, k)) = f u y`. Introduce `u k hk y`. Take `⟨A, -, hA⟩` from `hΦ`.

Establish `hA' : Φ = X.B.Re.comp A` using `hA.symm`. Establish `h1` using `Formalism.L2.SG.EvalTOntoRep.contRep_reg X (hf u) (1, k)`. Establish `h2 : X.B.R (1, k) (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) = Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))`. Rewrite using `[hA']`. Conclude with `congrArg (fun L : L2X X →L[ℂ] L2X X => L (A (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)))) (GlobalTheory.Dec.CuspFrame.re_fixed X.B k hk)`.

Rewrite `h1` using `[h2]`. Conclude with `congrFun (Formalism.L2.SG.EvalTOntoRep.contRep_unique X h1 (hf u)) y`. Establish `hcomm : ∀ a b : X.B.I.GA, a.1 = 1 → b.2 = 1 → a * b = b * a` using `fun a b ha hb => Prod.ext (by simp [ha]) (by simp [hb])`. Establish `hcont : ∀ u, Continuous (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u)` using `fun u => by`. Establish `: GlobalTheory.ConjRowMult.conjMap X M c Φ h t u = fun y => star (f u (iotaX X h (y * t⁻¹)))` using `funext (hval u)`.

Rewrite using `[this]`. Conclude with `((hf u).1.comp ((iotaX X h).continuous.comp (continuous_mul_right _))).star`. Establish `haut : ∀ u, IsAutFun (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u)`. Introduce `u`. Use `⟨fun γ hγ y => ?_, ?_, hcont u⟩` and prove the remaining obligations.

Rewrite using `[hval, hval, mul_assoc, map_mul, (hf u).2.1 _ (hrat γ hγ)]`. Take `⟨hKo, ⟨K, hK⟩, -⟩` from `(GlobalTheory.CongTop.adelic_topology X.B.I).2.2.2.2.2.2 X.B.g hg`. Use `⟨K.comap ((MonoidHom.snd _ _).comp ((iotaX X h).toMulEquiv.toMonoidHom.comp (MulAut.conj t).toMonoidHom)), ?_, fun k hk hkf y => ?_⟩` and prove the remaining obligations. Rewrite `hKo` using `[← hK]`. Conclude with `hKo.preimage (f := fun k => (iotaX X h (t * k * t⁻¹)).2) (continuous_snd.comp ((iotaX X h).continuous.comp ((continuous_mul_right _).comp (continuous_mul_left _))))`.

Establish `hk' : (iotaX X h (t * k * t⁻¹)).2 ∈ X.B.I.Kg X.B.g` using `by rw [← hK]; exact hk`. Establish `h1 : (iotaX X h (t * k * t⁻¹)).1 = 1` using `hfst _ ((GfC _).mul_mem ((GfC _).mul_mem ht hkf) ((GfC _).inv_mem ht))`. Establish `e : y * k * t⁻¹ = y * t⁻¹ * (t * k * t⁻¹)` using `by group`. Establish `e2 : iotaX X h (t * k * t⁻¹) = (1, (iotaX X h (t * k * t⁻¹)).2)` using `Prod.ext h1 rfl`. Rewrite using `[hval, hval, e, map_mul, e2, hlev u _ hk']`.

Introduce `u`. Use `⟨haut u, GlobalTheory.RepSmooth.smooth hθ he hs hcont u, GlobalTheory.RepSmooth.zfin he hs u, ?_⟩` and prove the remaining obligations. Establish `key : ∃ N : ℕ, ∀ v x, ∃ C : ℝ, ∀ a ∈ GinfC (D.sp.Y 0), ‖GlobalTheory.ConjRowMult.conjMap X M c Φ h t v (x * a)‖ ≤ C * normInf θ (D.sp.Y 0) a ^ N`. Break down `Nat.eq_zero_or_pos (D.sp.Y 0).rank with hn | hn` into its components or cases. Use `⟨0, fun v x => ⟨‖GlobalTheory.ConjRowMult.conjMap X M c Φ h t v x‖, fun a _ => ?_⟩⟩` and prove the remaining obligations.

Establish `: a = 1` using `Subtype.ext (Units.ext (Matrix.ext fun i => (Fin.cast hn i).elim0))`. Rewrite using `[this, mul_one, pow_zero, mul_one]`. Establish `hn' : 1 ≤ X.B.I.n` using `by rw [← rank_eq X h]; exact hn`. Establish `hti : (iotaX X h t⁻¹).1 = 1` using `hfst _ ((GfC _).inv_mem ht)`. Take `⟨m, hm⟩` from `GlobalTheory.T.derivativeClosedClass_bounded_by_inverseLeastSize X.B hn' hg`.

Use `⟨m, fun v x => ?_⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `hm (Set.range f) (by`. Introduce and unpack `_ ⟨u, rfl⟩`. Use `⟨⟨_, hf u⟩, hlev u, fun w E => ?_⟩` and prove the remaining obligations. Take `⟨τ, Y, hY, hι⟩` from `hone w E.1 E.2`.

Use `⟨_, ⟨Function.update u τ (GlobalTheory.RepSmooth.der u τ hY), rfl⟩, fun y => ?_⟩` and prove the remaining obligations. Establish `h1` using `(GlobalTheory.RepSmooth.hasDerivAt_apply he hs τ u hY ((iotaX X h).symm y * t)).star`. Simplify using `only [hval, star_star, mul_inv_cancel_right, ContinuousMulEquiv.apply_symm_apply] at h1`. Use `h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Establish `e1 : iotaX X h (oneP θ (D.sp.Y 0) τ Y s) = GlobalTheory.SobolevBound.onePar X.B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace X.B w E) s` using `GlobalTheory.RepSmooth.eq_onePar X.B w E s (hι s).1 (hι s).2.1 (hι s).2.2`.

Establish `e2 : iotaX X h ((iotaX X h).symm y * t * oneP θ (D.sp.Y 0) τ Y s * t⁻¹) = y * iotaX X h (oneP θ (D.sp.Y 0) τ Y s)`. Establish `h3 : (iotaX X h (oneP θ (D.sp.Y 0) τ Y s)).2 = 1` using `(hι s).1`. Rewrite using `[map_mul, map_mul, mul_assoc, ← hcomm _ _ hti h3, ← mul_assoc, ← map_mul, mul_inv_cancel_right, ContinuousMulEquiv.apply_symm_apply]`. Use `show f u _ = f u _`. Rewrite using `[e2, e1]) _ ⟨v, rfl⟩`.

Use `choose b hb0 hb using hgr hn'`. Establish `hp` using `(GlobalTheory.TauLipschitz.tauLip X.B.I hn').1`. Establish `hB : 0 ≤ ∑ w, b w` using `Finset.sum_nonneg fun w _ => hb0 w`. Use `⟨|C| * ((GlobalTheory.Count.tau1 X.B.I (iotaX X h (x * t⁻¹)))⁻¹ * ∑ w, b w) ^ m, fun a ha => ?_⟩` and prove the remaining obligations. Establish `hN : 0 ≤ normInf θ (D.sp.Y 0) a` using `by unfold normInf; positivity`.

Establish `e : iotaX X h (x * a * t⁻¹) = iotaX X h (x * t⁻¹) * iotaX X h a`. Rewrite using `[map_mul, map_mul, map_mul, mul_assoc, ← hcomm _ _ hti (hsnd a ha), mul_assoc]`. Establish `h2` using `GlobalTheory.TauNorm.inv_tau_mul_le X.B.I hn' (iotaX X h (x * t⁻¹)) (iotaX X h a) (hsnd a ha) ((∑ w, b w) * normInf θ (D.sp.Y 0) a) fun w => (hb w a).trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun w _ => hb0 w) (Finset.mem_univ w)) hN)`. Rewrite using `[hval, norm_star, e]`. Use `(hC _).trans ?_` and prove the remaining obligations.

Establish `h0` using `inv_nonneg.2 (hp (iotaX X h (x * t⁻¹) * iotaX X h a)).le`. Rewrite using `[mul_assoc, ← mul_pow, mul_assoc]`. Conclude with `mul_le_mul (le_abs_self _) (pow_le_pow_left₀ h0 h2 m) (pow_nonneg h0 m) (abs_nonneg _)`. Take `⟨N, hN⟩` from `key`. Use `⟨N, fun l hl x => ?_⟩` and prove the remaining obligations.

Take `⟨v, hv⟩` from `GlobalTheory.RepSmooth.foldr_rder he hs u l hl`. Rewrite using `[hv]`. Conclude with `hN v x`.
-/
theorem conjMap_isAutFunSm_gen {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (θ : InfFam D) {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (t : GA D (D.sp.Y 0))
    (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (hθ : IsInfFam θ) (hid : ∀ x : X.B.I.E, HEq (X.ιE x) x)
    (ht : t ∈ GfC (D.sp.Y 0))
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w))
    (Φ : X.B.Hs →L[ℂ] L2X X) (hΦ : Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re)
    (hrep : ∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) :
    ∀ u : M.Vec, IsAutFunSm θ (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := by
  have he : GlobalTheory.RepSmooth.IsEquiv θ (GlobalTheory.ConjRowMult.conjMap X M c Φ h t) :=
    equiv_gen X h θ M t c hθ hid ht hc Φ hΦ hrep
  have hs : GlobalTheory.RepSmooth.IsSob (GlobalTheory.ConjRowMult.conjMap X M c Φ h t) :=
    cont_gen X h θ M t c hθ hid hc Φ hΦ hrep
  obtain ⟨hrat, hfst, hsnd, hone, hgr⟩ := GlobalTheory.ConjRowAut.iota_data θ hθ
    (fun τ Y hY s => GlobalTheory.SmVec.exp_mem_UH (GlobalTheory.SmVec.gram_unit (M.fr_unit τ) (M.fr_gram τ)) hY s) X.B.I h
  change ∀ k ∈ _, iotaX X h k ∈ _ at hrat
  change ∀ k ∈ _, (iotaX X h k).1 = 1 at hfst
  change ∀ k ∈ _, (iotaX X h k).2 = 1 at hsnd
  choose f hf using hrep
  have hval : ∀ u y, GlobalTheory.ConjRowMult.conjMap X M c Φ h t u y = star (f u (iotaX X h (y * t⁻¹))) := fun u y => by
    rw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.contRepL_spec X (hf u)]
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hlev : ∀ u, ∀ k ∈ X.B.I.Kg X.B.g, ∀ y, f u (y * (1, k)) = f u y := by
    intro u k hk y
    obtain ⟨A, -, hA⟩ := hΦ
    have hA' : Φ = X.B.Re.comp A := hA.symm
    have h1 := Formalism.L2.SG.EvalTOntoRep.contRep_reg X (hf u) (1, k)
    have h2 : X.B.R (1, k) (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) =
        Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)) := by
      rw [hA']
      exact congrArg (fun L : L2X X →L[ℂ] L2X X => L (A (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))))
        (GlobalTheory.Dec.CuspFrame.re_fixed X.B k hk)
    rw [h2] at h1
    exact congrFun (Formalism.L2.SG.EvalTOntoRep.contRep_unique X h1 (hf u)) y
  have hcomm : ∀ a b : X.B.I.GA, a.1 = 1 → b.2 = 1 → a * b = b * a := fun a b ha hb =>
    Prod.ext (by simp [ha]) (by simp [hb])
  have hcont : ∀ u, Continuous (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := fun u => by
    have : GlobalTheory.ConjRowMult.conjMap X M c Φ h t u = fun y => star (f u (iotaX X h (y * t⁻¹))) := funext (hval u)
    rw [this]
    exact ((hf u).1.comp ((iotaX X h).continuous.comp (continuous_mul_right _))).star
  have haut : ∀ u, IsAutFun (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := by
    intro u
    refine ⟨fun γ hγ y => ?_, ?_, hcont u⟩
    · rw [hval, hval, mul_assoc, map_mul, (hf u).2.1 _ (hrat γ hγ)]
    · obtain ⟨hKo, ⟨K, hK⟩, -⟩ := (GlobalTheory.CongTop.adelic_topology X.B.I).2.2.2.2.2.2 X.B.g hg
      refine ⟨K.comap ((MonoidHom.snd _ _).comp ((iotaX X h).toMulEquiv.toMonoidHom.comp
        (MulAut.conj t).toMonoidHom)), ?_, fun k hk hkf y => ?_⟩
      · rw [← hK] at hKo
        exact hKo.preimage (f := fun k => (iotaX X h (t * k * t⁻¹)).2)
          (continuous_snd.comp ((iotaX X h).continuous.comp
            ((continuous_mul_right _).comp (continuous_mul_left _))))
      · have hk' : (iotaX X h (t * k * t⁻¹)).2 ∈ X.B.I.Kg X.B.g := by rw [← hK]; exact hk
        have h1 : (iotaX X h (t * k * t⁻¹)).1 = 1 :=
          hfst _ ((GfC _).mul_mem ((GfC _).mul_mem ht hkf) ((GfC _).inv_mem ht))
        have e : y * k * t⁻¹ = y * t⁻¹ * (t * k * t⁻¹) := by group
        have e2 : iotaX X h (t * k * t⁻¹) = (1, (iotaX X h (t * k * t⁻¹)).2) := Prod.ext h1 rfl
        rw [hval, hval, e, map_mul, e2, hlev u _ hk']
  intro u
  refine ⟨haut u, GlobalTheory.RepSmooth.smooth hθ he hs hcont u, GlobalTheory.RepSmooth.zfin he hs u, ?_⟩
  have key : ∃ N : ℕ, ∀ v x, ∃ C : ℝ, ∀ a ∈ GinfC (D.sp.Y 0),
      ‖GlobalTheory.ConjRowMult.conjMap X M c Φ h t v (x * a)‖ ≤ C * normInf θ (D.sp.Y 0) a ^ N := by
    rcases Nat.eq_zero_or_pos (D.sp.Y 0).rank with hn | hn
    · refine ⟨0, fun v x => ⟨‖GlobalTheory.ConjRowMult.conjMap X M c Φ h t v x‖, fun a _ => ?_⟩⟩
      have : a = 1 := Subtype.ext (Units.ext (Matrix.ext fun i => (Fin.cast hn i).elim0))
      rw [this, mul_one, pow_zero, mul_one]
    have hn' : 1 ≤ X.B.I.n := by rw [← rank_eq X h]; exact hn
    have hti : (iotaX X h t⁻¹).1 = 1 := hfst _ ((GfC _).inv_mem ht)
    obtain ⟨m, hm⟩ := GlobalTheory.T.derivativeClosedClass_bounded_by_inverseLeastSize X.B hn' hg
    refine ⟨m, fun v x => ?_⟩
    obtain ⟨C, hC⟩ := hm (Set.range f) (by
      rintro _ ⟨u, rfl⟩
      refine ⟨⟨_, hf u⟩, hlev u, fun w E => ?_⟩
      obtain ⟨τ, Y, hY, hι⟩ := hone w E.1 E.2
      refine ⟨_, ⟨Function.update u τ (GlobalTheory.RepSmooth.der u τ hY), rfl⟩, fun y => ?_⟩
      have h1 := (GlobalTheory.RepSmooth.hasDerivAt_apply he hs τ u hY ((iotaX X h).symm y * t)).star
      simp only [hval, star_star, mul_inv_cancel_right, ContinuousMulEquiv.apply_symm_apply] at h1
      refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      have e1 : iotaX X h (oneP θ (D.sp.Y 0) τ Y s) =
          GlobalTheory.SobolevBound.onePar X.B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace X.B w E) s :=
        GlobalTheory.RepSmooth.eq_onePar X.B w E s (hι s).1 (hι s).2.1 (hι s).2.2
      have e2 : iotaX X h ((iotaX X h).symm y * t * oneP θ (D.sp.Y 0) τ Y s * t⁻¹) =
          y * iotaX X h (oneP θ (D.sp.Y 0) τ Y s) := by
        have h3 : (iotaX X h (oneP θ (D.sp.Y 0) τ Y s)).2 = 1 := (hι s).1
        rw [map_mul, map_mul, mul_assoc, ← hcomm _ _ hti h3, ← mul_assoc, ← map_mul, mul_inv_cancel_right,
          ContinuousMulEquiv.apply_symm_apply]
      show f u _ = f u _
      rw [e2, e1]) _ ⟨v, rfl⟩
    choose b hb0 hb using hgr hn'
    have hp := (GlobalTheory.TauLipschitz.tauLip X.B.I hn').1
    have hB : 0 ≤ ∑ w, b w := Finset.sum_nonneg fun w _ => hb0 w
    refine ⟨|C| * ((GlobalTheory.Count.tau1 X.B.I (iotaX X h (x * t⁻¹)))⁻¹ * ∑ w, b w) ^ m, fun a ha => ?_⟩
    have hN : 0 ≤ normInf θ (D.sp.Y 0) a := by unfold normInf; positivity
    have e : iotaX X h (x * a * t⁻¹) = iotaX X h (x * t⁻¹) * iotaX X h a := by
      rw [map_mul, map_mul, map_mul, mul_assoc, ← hcomm _ _ hti (hsnd a ha), mul_assoc]
    have h2 := GlobalTheory.TauNorm.inv_tau_mul_le X.B.I hn' (iotaX X h (x * t⁻¹)) (iotaX X h a) (hsnd a ha)
      ((∑ w, b w) * normInf θ (D.sp.Y 0) a) fun w => (hb w a).trans
        (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun w _ => hb0 w) (Finset.mem_univ w)) hN)
    rw [hval, norm_star, e]
    refine (hC _).trans ?_
    have h0 := inv_nonneg.2 (hp (iotaX X h (x * t⁻¹) * iotaX X h a)).le
    rw [mul_assoc, ← mul_pow, mul_assoc]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ h0 h2 m) (pow_nonneg h0 m) (abs_nonneg _)
  obtain ⟨N, hN⟩ := key
  refine ⟨N, fun l hl x => ?_⟩
  obtain ⟨v, hv⟩ := GlobalTheory.RepSmooth.foldr_rder he hs u l hl
  rw [hv]
  exact hN v x

end GlobalTheory.ConjEvalAut
end Gen

/- English proof (translation)
Introduce `_ _ _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t hid _ _ hinf _ hsee c hc Φ hΦ hrep u`. Conclude with `GlobalTheory.ConjEvalAut.conjMap_isAutFunSm_gen X h R.θ (MP R) t c hinf hid hsee.fin hc Φ hΦ hrep u`.
-/
theorem GlobalTheory.ConjEvalAut.conjMap_isAutFunSm_see : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, IsAutFunSm R.θ (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u) := by
  intro _ _ _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t hid _ _ hinf _ hsee c hc Φ hΦ hrep u
  exact GlobalTheory.ConjEvalAut.conjMap_isAutFunSm_gen X h R.θ (MP R) t c hinf hid hsee.fin hc Φ hΦ hrep u

end
