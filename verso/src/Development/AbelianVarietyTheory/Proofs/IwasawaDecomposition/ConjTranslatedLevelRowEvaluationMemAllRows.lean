import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjTranslatedEvaluationMemAllRowsSpace
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefWeightedLocUncond
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

open GlobalTheory.Core.Mi GlobalTheory.Core.Mi.SeeHH in

/- English proof (translation)
Introduce `hDS hP hUq hRF D G' _ _ Pl0 T A Ks _ _ _ R F X h t hIdE hG hLev hinf hν hSee c v₀ hc1 hc2 S hS φ hφ`. Establish `hθ : IsInfFam R.θ` using `hinf`. Establish `hMat : Matches X h (JR R F) (chiR R F) t` using `⟨hSee.fin, hSee.conj⟩`. Establish `hCV : ConjVec X h R.θ (MP R) v₀` using `⟨c, hc1, hc2⟩`. Establish `hL : ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε` using `X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)) := fun v => by`.

Establish `h1` using `Formalism.L2.SG.WuDecayPf.coef_integrable_of_weighted X (Formalism.L2.SG.Pf.WuDec.coefWeighted_of_gap X GlobalTheory.Sloc.CoefWeighted.coefWeightedLoc_uncond hG) v`. Establish `hs : Integrable (fun g => star (Formalism.L2.SG.WuDecayPf.coefV X v g)) (Formalism.REAL.muG (X.B.I.ε v))` using `h1.mono (continuous_star.comp_aestronglyMeasurable h1.1) (ae_of_all _ fun g => le_of_eq (norm_star _))`. Conclude with `hs.const_mul ((X.dv v : ℝ) : ℂ)`. Establish `hR` using `GlobalTheory.T.modelIdentification_respects_real_and_finite D X h R.θ hθ hIdE`. Establish `hT : PiTensorProduct.lift S ∈ MultT R.θ (MP R) (JR R F) (chiR R F)`.

Use `(mem_multT R.θ (MP R) (JR R F) (chiR R F) _).2 ?_` and prove the remaining obligations. Rewrite using `[LinearEquiv.symm_apply_apply]`. Conclude with `hS`. Take `⟨hRow, hMem⟩` from `GlobalTheory.T.translateToSecondModel_cuspFormMap_value_automorphic hP D X h R.θ _ (MP R) (JR R F) (chiR R F) t hθ hMat _ hT (PiTensorProduct.tprod ℂ v₀)`. Establish `hfx : ∀ x, evS X h t (PiTensorProduct.lift S (PiTensorProduct.tprod ℂ v₀)) x = S v₀ ((iotaX X h).symm x * t)` using `fun x => by`.

Simplify using `only [evS, PiTensorProduct.lift.tprod]`. Generalize the expression as in `evS X h t (PiTensorProduct.lift S (PiTensorProduct.tprod ℂ v₀)) = f at hRow hMem hfx`. Establish `hφ2 : (φ : X.B.I.GA → ℂ) =ᵐ[muX X] f` using `hφ.trans (Filter.Eventually.of_forall fun x => (hfx x).symm)`. Establish `hφ' : φ = hMem.toLp f` using `Lp.ext (hφ2.trans hMem.coeFn_toLp.symm)`. Establish `hRe` using `re_fix_of_row X hRow hMem`.

Establish `hι : ∀ g, g ∈ GQ (D.sp.Y 0) ↔ iotaX X h g ∈ X.B.I.GFset`. Introduce `g`. Rewrite using `[Formalism.IndefR.RationalEmbedding.iota_rat]`. Conclude with `GlobalTheory.Mem.SJ.SchurMove.castGA_mem_GFset _ _`. Take `⟨κ, hκ⟩` from `GlobalTheory.Mem.SJ.HaarMove.schur_of_bridge (MP R) R.θ (JR R F) (chiR R F) (fun μ 𝓕 => GlobalTheory.MultFinite.schurMult hP μ 𝓕) hθ X.B.I X.B.μf X.B.fund X.B.fund_spec (iotaX X h) hι t S hS S hS`.

Establish `hv₀ : ∏ τ, ⟪(v₀ τ : (MP R).H τ), (v₀ τ : (MP R).H τ)⟫_ℂ = 1`. Use `Finset.prod_eq_one fun τ _ => ?_` and prove the remaining obligations. Establish `hn : ‖(v₀ τ : (MP R).H τ)‖ = 1`. Rewrite using `[← (c τ).norm_map, hc2 τ]`. Conclude with `(X.low _).1`.

Rewrite using `[inner_self_eq_norm_sq_to_K, hn]`. Simplify using the standard rewrite rules. Establish `hs : MemLp (fun x => star (f x)) 2 (muX X)` using `hMem.star`. Establish `hinv : ∀ γ ∈ X.B.I.GFset, ∀ y, star (f (γ * y)) = star (f y)` using `fun γ hγ y => by`. Rewrite using `[hRow.left γ hγ y]`.

Establish `hnorm : (((‖hs.toLp (fun x => star (f x))‖ ^ 2 : ℝ)) : ℂ) = κ`. Rewrite using `[Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp hs, ← integral_complex_ofReal]`. Establish `e` using `hκ v₀ v₀`. Rewrite `e` using `[hv₀, mul_one]`. Rewrite using `[← e]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[norm_star, hfx x, ← starRingEnd_apply, Complex.conj_mul']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hRph : X.Rph (star (hMem.toLp f)) = star (hMem.toLp f)`. Rewrite using `[star_toLp_eq X hMem hs]`. Use `Formalism.L2.SG.EvalTRph.rph_fix_of_coef X hL _ (fun g => ?_)` and prove the remaining obligations. Take `⟨a, ha, hb, w, hw, hsh⟩` from `real_shift X h R.θ (MP R) (JR R F) (chiR R F) t hMat.1 hR v₀ g`. Establish `hco` using `coef_eq X h R.θ (MP R) v₀ hCV g a ha hb w hw`.

Establish `hRg` using `Formalism.L2.SG.EvalTReg.reg_toLp_X X (fun x => star (f x)) hinv hs (g, 1)`. Establish `hpair : ⟪hs.toLp (fun x => star (f x)), X.B.R (g, 1) (hs.toLp (fun x => star (f x)))⟫_ℂ = ∫ x, star (S w ((iotaX X h).symm x * t)) * S v₀ ((iotaX X h).symm x * t) ∂(muX X)`. Rewrite using `[MeasureTheory.L2.inner_def]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hs.coeFn_toLp, hRg] with x a1 a2`.

Rewrite using `[a1, a2]`. Simplify using `only [RCLike.inner_apply, hfx]`. Rewrite using `[hsh S hS x, starRingEnd_apply, star_star, mul_comm]`. Rewrite using `[hpair, hκ w v₀, hco, hnorm]`. Rewrite using `[hφ']`.

Use `⟨star (hMem.toLp f), ?_⟩` and prove the remaining obligations. Use `show X.B.Re (X.Rph _) = _`. Rewrite using `[hRph, hRe]`.
-/
theorem GlobalTheory.Mem.SRe.conj_ev_mem_HHX : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ S ∈ MultR R F, ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) → star φ ∈ HHX X := by
  intro hDS hP hUq hRF D G' _ _ Pl0 T A Ks _ _ _ R F X h t hIdE hG hLev hinf hν hSee c v₀ hc1 hc2 S hS φ hφ
  have hθ : IsInfFam R.θ := hinf
  have hMat : Matches X h (JR R F) (chiR R F) t := ⟨hSee.fin, hSee.conj⟩
  have hCV : ConjVec X h R.θ (MP R) v₀ := ⟨c, hc1, hc2⟩
  have hL : ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v))
      (Formalism.REAL.muG (X.B.I.ε v)) := fun v => by
    have h1 := Formalism.L2.SG.WuDecayPf.coef_integrable_of_weighted X
      (Formalism.L2.SG.Pf.WuDec.coefWeighted_of_gap X GlobalTheory.Sloc.CoefWeighted.coefWeightedLoc_uncond hG) v
    have hs : Integrable (fun g => star (Formalism.L2.SG.WuDecayPf.coefV X v g)) (Formalism.REAL.muG (X.B.I.ε v)) :=
      h1.mono (continuous_star.comp_aestronglyMeasurable h1.1) (ae_of_all _ fun g => le_of_eq (norm_star _))
    exact hs.const_mul ((X.dv v : ℝ) : ℂ)
  have hR := GlobalTheory.T.modelIdentification_respects_real_and_finite D X h R.θ hθ hIdE
  have hT : PiTensorProduct.lift S ∈ MultT R.θ (MP R) (JR R F) (chiR R F) := by
    refine (mem_multT R.θ (MP R) (JR R F) (chiR R F) _).2 ?_
    rw [LinearEquiv.symm_apply_apply]; exact hS
  obtain ⟨hRow, hMem⟩ := GlobalTheory.T.translateToSecondModel_cuspFormMap_value_automorphic hP D X h R.θ _ (MP R) (JR R F) (chiR R F) t hθ hMat _ hT
    (PiTensorProduct.tprod ℂ v₀)
  have hfx : ∀ x, evS X h t (PiTensorProduct.lift S (PiTensorProduct.tprod ℂ v₀)) x =
      S v₀ ((iotaX X h).symm x * t) := fun x => by
    simp only [evS, PiTensorProduct.lift.tprod]
  generalize evS X h t (PiTensorProduct.lift S (PiTensorProduct.tprod ℂ v₀)) = f at hRow hMem hfx
  have hφ2 : (φ : X.B.I.GA → ℂ) =ᵐ[muX X] f := hφ.trans (Filter.Eventually.of_forall fun x => (hfx x).symm)
  have hφ' : φ = hMem.toLp f := Lp.ext (hφ2.trans hMem.coeFn_toLp.symm)
  have hRe := re_fix_of_row X hRow hMem
  have hι : ∀ g, g ∈ GQ (D.sp.Y 0) ↔ iotaX X h g ∈ X.B.I.GFset := by
    intro g
    rw [Formalism.IndefR.RationalEmbedding.iota_rat]
    exact GlobalTheory.Mem.SJ.SchurMove.castGA_mem_GFset _ _
  obtain ⟨κ, hκ⟩ := GlobalTheory.Mem.SJ.HaarMove.schur_of_bridge (MP R) R.θ (JR R F) (chiR R F)
    (fun μ 𝓕 => GlobalTheory.MultFinite.schurMult hP μ 𝓕) hθ
    X.B.I X.B.μf X.B.fund X.B.fund_spec (iotaX X h) hι t S hS S hS
  have hv₀ : ∏ τ, ⟪(v₀ τ : (MP R).H τ), (v₀ τ : (MP R).H τ)⟫_ℂ = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    have hn : ‖(v₀ τ : (MP R).H τ)‖ = 1 := by
      rw [← (c τ).norm_map, hc2 τ]
      exact (X.low _).1
    rw [inner_self_eq_norm_sq_to_K, hn]
    simp
  have hs : MemLp (fun x => star (f x)) 2 (muX X) := hMem.star
  have hinv : ∀ γ ∈ X.B.I.GFset, ∀ y, star (f (γ * y)) = star (f y) := fun γ hγ y => by
    rw [hRow.left γ hγ y]
  have hnorm : (((‖hs.toLp (fun x => star (f x))‖ ^ 2 : ℝ)) : ℂ) = κ := by
    rw [Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp hs, ← integral_complex_ofReal]
    have e := hκ v₀ v₀
    rw [hv₀, mul_one] at e
    rw [← e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [norm_star, hfx x, ← starRingEnd_apply, Complex.conj_mul']
    push_cast
    ring
  have hRph : X.Rph (star (hMem.toLp f)) = star (hMem.toLp f) := by
    rw [star_toLp_eq X hMem hs]
    refine Formalism.L2.SG.EvalTRph.rph_fix_of_coef X hL _ (fun g => ?_)
    obtain ⟨a, ha, hb, w, hw, hsh⟩ := real_shift X h R.θ (MP R) (JR R F) (chiR R F) t hMat.1 hR v₀ g
    have hco := coef_eq X h R.θ (MP R) v₀ hCV g a ha hb w hw
    have hRg := Formalism.L2.SG.EvalTReg.reg_toLp_X X (fun x => star (f x)) hinv hs (g, 1)
    have hpair : ⟪hs.toLp (fun x => star (f x)), X.B.R (g, 1) (hs.toLp (fun x => star (f x)))⟫_ℂ =
        ∫ x, star (S w ((iotaX X h).symm x * t)) * S v₀ ((iotaX X h).symm x * t) ∂(muX X) := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hs.coeFn_toLp, hRg] with x a1 a2
      rw [a1, a2]
      simp only [RCLike.inner_apply, hfx]
      rw [hsh S hS x, starRingEnd_apply, star_star, mul_comm]
    rw [hpair, hκ w v₀, hco, hnorm]
  rw [hφ']
  refine ⟨star (hMem.toLp f), ?_⟩
  show X.B.Re (X.Rph _) = _
  rw [hRph, hRe]
