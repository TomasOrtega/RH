import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOnto
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ModelIdentificationRespectsRealAndFinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureSecond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RegUnitary

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjRowCont

/- English proof (translation)
Use `X.B.sf` as an intermediate fact. Use `X.B.haar` as an intermediate fact. Use `Formalism.MainNotions.LeviCoordinates.rr_muA_left X.B.I X.B.μf` as an intermediate fact. Take `⟨-, hr, -⟩` from `GlobalTheory.AdelicUnimod.adelic_unimodular X.B.I X.B.μf`. Establish `hP : ∀ a : X.B.I.GA, Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) a` using `fun a => ⟨measurable_mul_const a, hr a⟩`.

Take `⟨h1, h2⟩` from `Formalism.L2.SG.Pf.rp_map (Formalism.MainNotions.LeviCoordinates.rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec) (hP g) (hP g⁻¹)`. Establish `e1` using `X.B.R_spec g (star φ)`. Establish `e2` using `X.B.R_spec g φ`. Establish `e3 : ∀ᵐ x ∂(muX X), ((star φ : L2X X) : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * g)) = star ((φ : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * g)))`. Use `ae_of_ae_map (p := fun y => ((star φ : L2X X) : X.B.I.GA → ℂ) y = star ((φ : X.B.I.GA → ℂ) y)) h1 ?_` and prove the remaining obligations.

Rewrite using `[h2]`. Use `filter_upwards [Lp.coeFn_star φ] with y hy`. Rewrite using `[hy]`. Both sides reduce to the same expression. Apply `Lp.ext` to reduce the goal to its premises.

Use `filter_upwards [e1, e2, e3, Lp.coeFn_star (X.B.R g φ)] with x a1 a2 a3 a4`. Rewrite using `[a1, a4, Pi.star_apply, a2]`. Conclude with `a3`.
-/
theorem reg_star {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (g : X.B.I.GA) (φ : L2X X) :
    X.B.R g (star φ) = star (X.B.R g φ) := by
  have := X.B.sf
  have := X.B.haar
  have := Formalism.MainNotions.LeviCoordinates.rr_muA_left X.B.I X.B.μf
  obtain ⟨-, hr, -⟩ := GlobalTheory.AdelicUnimod.adelic_unimodular X.B.I X.B.μf
  have hP : ∀ a : X.B.I.GA, Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) a := fun a => ⟨measurable_mul_const a, hr a⟩
  obtain ⟨h1, h2⟩ := Formalism.L2.SG.Pf.rp_map (Formalism.MainNotions.LeviCoordinates.rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec) (hP g) (hP g⁻¹)
  have e1 := X.B.R_spec g (star φ)
  have e2 := X.B.R_spec g φ
  have e3 : ∀ᵐ x ∂(muX X), ((star φ : L2X X) : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * g)) =
      star ((φ : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * g))) := by
    refine ae_of_ae_map (p := fun y => ((star φ : L2X X) : X.B.I.GA → ℂ) y = star ((φ : X.B.I.GA → ℂ) y)) h1 ?_
    rw [h2]
    filter_upwards [Lp.coeFn_star φ] with y hy
    rw [hy]
    rfl
  apply Lp.ext
  filter_upwards [e1, e2, e3, Lp.coeFn_star (X.B.R g φ)] with x a1 a2 a3 a4
  rw [a1, a4, Pi.star_apply, a2]
  exact a3

/- English proof (translation)
Establish `k : ∀ {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA), x ∈ I.GFset ↔ castGA e x ∈ I'.GFset`. Introduce `I I' e x`. Substitute `e` using the available equality. Both sides reduce to the same expression. Conclude with `(Formalism.IndefR.RationalEmbedding.iota_rat D g).trans (k h.symm _)`.
-/
theorem iotaX_rat_iff {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (g : GA D (D.sp.Y 0)) : g ∈ GQ (D.sp.Y 0) ↔ iotaX X h g ∈ X.B.I.GFset := by
  have k : ∀ {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA), x ∈ I.GFset ↔ castGA e x ∈ I'.GFset := by
    intro I I' e x
    subst e; rfl
  exact (Formalism.IndefR.RationalEmbedding.iota_rat D g).trans (k h.symm _)

/- English proof (translation)
Take `⟨m, hm, -⟩` from `GlobalTheory.exists_continuousMultilinearMap_of_inner_prod (H := X.B.H) X.B.tens X.B.tens_spec.1 X.B.tens_spec.2.2`. Set `C : (∀ τ, M.H τ) → ∀ v, X.B.H v` to `fun y => Equiv.piCongrLeft X.B.H X.pl.symm (fun τ => c τ (y τ))`. Establish `hC : ∀ y τ, C y (X.pl.symm τ) = c τ (y τ)` using `fun y τ => Equiv.piCongrLeft_apply_apply _ _ _ _`. Establish `hCu : ∀ y τ a, C (Function.update y τ a) = Function.update (C y) (X.pl.symm τ) (c τ a)`. Introduce `y τ a`.

Rewrite using `[← GlobalTheory.ConjRowMult.piCongrLeft_update]`. Use `congrArg (Equiv.piCongrLeft X.B.H X.pl.symm) (funext fun τ' => ?_)` and prove the remaining obligations. Conclude with `Function.apply_update (fun i (s : M.H i) => c i s) y τ a τ'`. Establish `hCc : Continuous C`. Use `continuous_pi fun v => ?_` and prove the remaining obligations.

Take `⟨τ, rfl⟩` from `X.pl.symm.surjective v`. Simplify using `only [hC]`. Conclude with `(c τ).continuous.comp (continuous_apply τ)`. Set `Ψ₀ : MultilinearMap ℂ M.H (L2X X)` to `MultilinearMap.mk' (fun y => conjL (muX X) (Φ (m (C y)))) (fun y τ a b => by rw [hCu, hCu, hCu, map_add, m.map_update_add, map_add, map_add]) (fun y τ a b => by`. Rewrite using `[hCu, hCu, LinearIsometryEquiv.map_smulₛₗ, m.map_update_smul, map_smul, LinearIsometryEquiv.map_smulₛₗ, starRingEnd_self_apply])`.

Use `⟨⟨Ψ₀, (conjL (muX X)).continuous.comp (Φ.continuous.comp (m.cont.comp hCc))⟩, fun y => ?_⟩` and prove the remaining obligations. Use `show star (Φ (m (C y))) = _`. Rewrite using `[hm]`.
-/
theorem exists_conj_multilinear {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {S : D.what₂.Tau → SPar}
    (M : DSModel (D.sp.Y 0) S) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (Φ : X.B.Hs →L[ℂ] L2X X) :
    ∃ Ψ : ContinuousMultilinearMap ℂ M.H (L2X X), ∀ y,
      Ψ y = star (Φ (X.B.tens (Equiv.piCongrLeft X.B.H X.pl.symm fun τ => c τ (y τ)))) := by
  obtain ⟨m, hm, -⟩ := GlobalTheory.exists_continuousMultilinearMap_of_inner_prod (H := X.B.H) X.B.tens
    X.B.tens_spec.1 X.B.tens_spec.2.2
  let C : (∀ τ, M.H τ) → ∀ v, X.B.H v := fun y => Equiv.piCongrLeft X.B.H X.pl.symm (fun τ => c τ (y τ))
  have hC : ∀ y τ, C y (X.pl.symm τ) = c τ (y τ) := fun y τ => Equiv.piCongrLeft_apply_apply _ _ _ _
  have hCu : ∀ y τ a, C (Function.update y τ a) = Function.update (C y) (X.pl.symm τ) (c τ a) := by
    intro y τ a
    rw [← GlobalTheory.ConjRowMult.piCongrLeft_update]
    refine congrArg (Equiv.piCongrLeft X.B.H X.pl.symm) (funext fun τ' => ?_)
    exact Function.apply_update (fun i (s : M.H i) => c i s) y τ a τ'
  have hCc : Continuous C := by
    refine continuous_pi fun v => ?_
    obtain ⟨τ, rfl⟩ := X.pl.symm.surjective v
    simp only [hC]
    exact (c τ).continuous.comp (continuous_apply τ)
  let Ψ₀ : MultilinearMap ℂ M.H (L2X X) := MultilinearMap.mk' (fun y => conjL (muX X) (Φ (m (C y))))
    (fun y τ a b => by rw [hCu, hCu, hCu, map_add, m.map_update_add, map_add, map_add])
    (fun y τ a b => by
      rw [hCu, hCu, LinearIsometryEquiv.map_smulₛₗ, m.map_update_smul, map_smul, LinearIsometryEquiv.map_smulₛₗ,
        starRingEnd_self_apply])
  refine ⟨⟨Ψ₀, (conjL (muX X)).continuous.comp (Φ.continuous.comp (m.cont.comp hCc))⟩, fun y => ?_⟩
  show star (Φ (m (C y))) = _
  rw [hm]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `_ D X h θ S M J χ t c _ hθ _ hE _ hc Φ hΦ hrep τ₀ v₀ x₀`. Take `⟨_, _, _, _, _, -, _⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (D.sp.Y 0)`. Take `⟨hf, -, hat, -⟩` from `GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h θ hθ hE`. Take `⟨-, hcomm, g, hg, hfix⟩` from `GlobalTheory.IdemProj.re_orth_proj X.B`. Use `X.B.sf` as an intermediate fact.

Use `X.B.haar` as an intermediate fact. Set `T : GA D (D.sp.Y 0) ≃* X.B.I.GA` to `(iotaX X h).toMulEquiv`. Establish `hT : Continuous T` using `(iotaX X h).continuous`. Establish `hT' : Continuous T.symm` using `(iotaX X h).symm.continuous`. Take `⟨μ, ρ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩` from `GlobalTheory.TensRep.exists_transport X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec T hT hT'`.

Take `⟨U, hU, hUg⟩` from `h11 g hg`. Establish `hA : Φ ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R`. Take `⟨A, hA, rfl⟩` from `hΦ`. Introduce `g`. Use `show (X.B.Re.comp A).comp (X.B.σs g) = (X.B.R (g, 1)).comp (X.B.Re.comp A)`.

Rewrite using `[ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g, ContinuousLinearMap.comp_assoc]`. Establish `hlev : ∀ k ∈ X.B.I.Kg g, ∀ w, X.B.R (1, k) (Φ w) = Φ w`. Take `⟨A, -, rfl⟩` from `hΦ`. Introduce `k hk w`. Conclude with `congrArg (fun C : L2X X →L[ℂ] L2X X => C (A w)) (hfix k hk)`.

Take `⟨Ψ, hΨ⟩` from `exists_conj_multilinear X M c Φ`. Take `⟨N, hN1, hN2, hN3⟩` from `GlobalTheory.TensRep.exists_mmap (ι := fun v x => X.B.I.ext v (T x)) hθ M h1 h2 h5 h6 h7 h8 h9 (fun γ hγ v => h10 γ ((iotaX_rat_iff X h γ).1 hγ) v) hU Ψ (fun τ a ha y => by`. Take `⟨q1, q2, -⟩` from `hat τ a ha`. Rewrite using `[h3, hΨ, hΨ, reg_star]`. Use `congr 1`.

Use `GlobalTheory.TensRep.hom_tens X.B.I X.B.tens_spec hA q1 _ _ fun v => ?_` and prove the remaining obligations. Take `⟨τ', rfl⟩` from `X.pl.symm.surjective v`. Rewrite using `[Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]`. Distinguish the cases in `e : τ' = τ`. Substitute `e` using the available equality.

Rewrite using `[Function.update_self]`. Conclude with `hc _ a ha _`. Rewrite using `[Function.update_of_ne e]`. Establish `q : (iotaX X h (atTau θ (D.sp.Y 0) τ a)).1 (X.pl.symm τ') = 1` using `q2 _ (X.pl.symm.injective.ne e)`. Rewrite using `[q]`.

Establish `: X.B.σ (X.pl.symm τ') 1 = 1` using `(X.ds _).2.2.1.1.1`. Use `show _ = X.B.σ (X.pl.symm τ') 1 _`. Rewrite using `[this]`. Use the proof step `rfl)`. Use the proof step `(fun y k hk hk' => by`.

Rewrite using `[h3, hΨ, reg_star]`. Establish `e : T k = (1, (T k).2)` using `Prod.ext ((hf k).1 hk') rfl`. Rewrite using `[e, hlev _ (hUg k hk)])`. Establish `key : ∀ (u : M.Vec) y, GlobalTheory.ConjRowMult.conjMap X M c Φ h t u y = N u (y * t⁻¹)`. Introduce `u y`.

Establish `r1 : GlobalTheory.Dec.IsContRep X.B (Ψ fun τ => (u τ : M.H τ)) (fun z => N u (T.symm z))`. Use `GlobalTheory.RepSmooth.isContRep_of_ae X.B ((hN2 u).3.comp hT') (fun γ hγ z => ?_) ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `(hN2 u).1 _ ((iotaX_rat_iff X h _).2 ?_) _` and prove the remaining obligations. Establish `: iotaX X h (T.symm γ) = γ` using `T.apply_symm_apply γ`.

Rewrite using `[this]` and apply the resulting hypothesis. Use `filter_upwards [h4 _ (hN1 u)] with z hz`. Rewrite using `[← hz, T.apply_symm_apply]`. Establish `r2 : Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) (fun z => star (N u (T.symm z)))`. Use `⟨r1.1.star, fun γ hγ z => congrArg star (r1.2.1 γ hγ z), ?_⟩` and prove the remaining obligations.

Establish `r3` using `r1.2.2`. Rewrite `r3` using `[hΨ]`. Use `filter_upwards [r3, Lp.coeFn_star (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)))] with z a1 a2`. Rewrite using `[← a1]`. Conclude with `(star_star _).symm.trans (congrArg star a2.symm)`.

Rewrite using `[GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.contRepL_spec X r2, star_star]`. Conclude with `congrArg (N u) (T.symm_apply_apply _)`. Take `⟨ℓ, hℓ1, hℓ2⟩` from `hN3 τ₀ v₀ (x₀ * t⁻¹)`. Conclude with `⟨ℓ, hℓ1, fun w => (hℓ2 w).trans (key _ _).symm⟩`.
-/
theorem conjMap_cont : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ (τ : D.what₂.Tau) (v : M.Vec) (x : GA D (D.sp.Y 0)), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt (D.sp.Y 0) τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) x := by
  intro _ D X h θ S M J χ t c _ hθ _ hE _ hc Φ hΦ hrep τ₀ v₀ x₀
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
  obtain ⟨Ψ, hΨ⟩ := exists_conj_multilinear X M c Φ
  obtain ⟨N, hN1, hN2, hN3⟩ := GlobalTheory.TensRep.exists_mmap (ι := fun v x => X.B.I.ext v (T x)) hθ M h1 h2 h5 h6 h7 h8 h9
    (fun γ hγ v => h10 γ ((iotaX_rat_iff X h γ).1 hγ) v) hU Ψ
    (fun τ a ha y => by
      obtain ⟨q1, q2, -⟩ := hat τ a ha
      rw [h3, hΨ, hΨ, reg_star]
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
      rw [h3, hΨ, reg_star]
      have e : T k = (1, (T k).2) := Prod.ext ((hf k).1 hk') rfl
      rw [e, hlev _ (hUg k hk)])
  have key : ∀ (u : M.Vec) y, GlobalTheory.ConjRowMult.conjMap X M c Φ h t u y = N u (y * t⁻¹) := by
    intro u y
    have r1 : GlobalTheory.Dec.IsContRep X.B (Ψ fun τ => (u τ : M.H τ)) (fun z => N u (T.symm z)) := by
      refine GlobalTheory.RepSmooth.isContRep_of_ae X.B ((hN2 u).3.comp hT') (fun γ hγ z => ?_) ?_
      · rw [map_mul]
        refine (hN2 u).1 _ ((iotaX_rat_iff X h _).2 ?_) _
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

end GlobalTheory.ConjRowCont

end
