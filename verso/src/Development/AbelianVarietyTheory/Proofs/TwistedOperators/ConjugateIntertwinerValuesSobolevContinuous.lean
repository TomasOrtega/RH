import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIdentificationRespectsRealFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLeftInvariantRepConjugateTensor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureSecond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantMultilinearMapsSmoothVectorsIntertwin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedHolomorphicFormEqMultiplicitySpaceValue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open scoped ContDiff

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.L2.Pj Formalism.IndefR.Datum GlobalTheory.HolDict
open scoped TensorProduct

namespace GlobalTheory.ConjRowCont

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S)

def vecF (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (y : ∀ τ, M.H τ) : ∀ v, X.B.H v :=
  Equiv.piCongrLeft X.B.H X.pl.symm (fun τ => c τ (y τ))

/- English proof (translation)
The claim follows from `Equiv.piCongrLeft_apply_apply _ _ _ _`.
-/
theorem vecF_apply (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (y : ∀ τ, M.H τ) (τ : D.what₂.Tau) :
    vecF X M c y (X.pl.symm τ) = c τ (y τ) :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

/- English proof (translation)
Unfold `vecF`. Rewrite using `[← GlobalTheory.ConjRowMult.piCongrLeft_update]`. Use `congr 1`. Use function extensionality and compare the values at `τ'`. Conclude with `Function.apply_update (fun i (s : M.H i) => c i s) y τ z τ'`.
-/
theorem vecF_update (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (y : ∀ τ, M.H τ) (τ : D.what₂.Tau)
    (z : M.H τ) :
    vecF X M c (Function.update y τ z) = Function.update (vecF X M c y) (X.pl.symm τ) (c τ z) := by
  unfold vecF
  rw [← GlobalTheory.ConjRowMult.piCongrLeft_update]
  congr 1
  funext τ'
  exact Function.apply_update (fun i (s : M.H i) => c i s) y τ z τ'

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons p l ih`. Establish `hl' : ∀ q ∈ l, q.2 ∈ lieAt V q.1` using `fun q hq => hl q (List.mem_cons_of_mem _ hq)`. Rewrite using `[List.foldr_cons, ih hl']`.

Use `hF (fun τ => ⟨_, GlobalTheory.BackForm.word_mem hsm _ (GlobalTheory.BackForm.lettersAt_mem hl') (y τ)⟩) p.1 p.2 (hl p List.mem_cons_self)` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `τ`. Distinguish the cases in `h : τ = p.1`.

Substitute `h` using the available equality. Simplify using `[GlobalTheory.BackForm.lettersAt]`. Establish `h' : ¬ p.1 = τ` using `fun e => h e.symm`. Simplify using `[GlobalTheory.BackForm.lettersAt, Function.update_of_ne h, List.filter_cons, h']`.
-/
theorem word_fun {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (F : (∀ τ, M.H τ) → K)
    (hsm : ∀ τ, ∀ Y ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) Y (w : M.H τ) ∈ M.sm τ)
    (hF : ∀ (v : M.Vec) τ, ∀ Y ∈ lieAt V τ, GlobalTheory.HolDict.dL2 θ V ρ (τ, Y) (F fun τ => (v τ : M.H τ)) =
      F (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) Y (v τ))))
    (l : List (D.what₂.Tau × Mt V.rank)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) (y : M.Vec) :
    l.foldr (GlobalTheory.HolDict.dL2 θ V ρ) (F fun τ => (y τ : M.H τ)) =
      F fun τ => (GlobalTheory.BackForm.lettersAt τ l).foldr (dRep (M.rep τ)) (y τ : M.H τ) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hl' : ∀ q ∈ l, q.2 ∈ lieAt V q.1 := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    rw [List.foldr_cons, ih hl']
    have := hF (fun τ => ⟨_, GlobalTheory.BackForm.word_mem hsm _ (GlobalTheory.BackForm.lettersAt_mem hl') (y τ)⟩) p.1 p.2
      (hl p List.mem_cons_self)
    refine this.trans ?_
    congr 1
    funext τ
    by_cases h : τ = p.1
    · subst h; simp [GlobalTheory.BackForm.lettersAt]
    · have h' : ¬ p.1 = τ := fun e => h e.symm
      simp [GlobalTheory.BackForm.lettersAt, Function.update_of_ne h, List.filter_cons, h']

end GlobalTheory.ConjRowCont

namespace GlobalTheory.ConjRowCont

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Take `⟨_, _, _, _, _, -, _⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (D.sp.Y 0)`. Take `⟨-, hcomm, g, hg, hfix⟩` from `GlobalTheory.IdemProj.re_orth_proj X.B`. Use `X.B.sf` as an intermediate fact. Use `X.B.haar` as an intermediate fact. Set `T : GA D (D.sp.Y 0) ≃* X.B.I.GA` to `(iotaX X h).toMulEquiv`.

Establish `hT : Continuous T` using `(iotaX X h).continuous`. Establish `hT' : Continuous T.symm` using `(iotaX X h).symm.continuous`. Take `⟨μ, ρ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩` from `GlobalTheory.TensRep.exists_transport X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec T hT hT'`. Take `⟨U, hU, hUg⟩` from `h11 g hg`. Establish `hA : Φ ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R`.

Take `⟨A, hA, rfl⟩` from `hΦ`. Introduce `g`. Use `show (X.B.Re.comp A).comp (X.B.σs g) = (X.B.R (g, 1)).comp (X.B.Re.comp A)`. Rewrite using `[ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g, ContinuousLinearMap.comp_assoc]`. Establish `hlev : ∀ k ∈ X.B.I.Kg g, ∀ w, X.B.R (1, k) (Φ w) = Φ w`.

Take `⟨A, -, rfl⟩` from `hΦ`. Introduce `k hk w`. Conclude with `congrArg (fun C : L2X X →L[ℂ] L2X X => C (A w)) (hfix k hk)`. Take `⟨m, hm, hn⟩` from `GlobalTheory.exists_continuousMultilinearMap_of_inner_prod (H := X.B.H) X.B.tens X.B.tens_spec.1 X.B.tens_spec.2.2`. Establish `hCd : ContDiff ℝ ∞ (vecF X M c)`.

Use `contDiff_pi.2 fun v => ?_` and prove the remaining obligations. Take `⟨τ, rfl⟩` from `X.pl.symm.surjective v`. Simplify using `only [vecF_apply]`. Conclude with `(GlobalTheory.ConjRowRep.contDiff_anti (c τ)).comp (contDiff_pi.1 contDiff_id τ)`. Set `F : (∀ τ, M.H τ) → L2X X` to `fun y => Φ (X.B.tens (vecF X M c y))`.

Establish `hF : ContDiff ℝ ∞ F`. Establish `e : F = fun y => (Φ.compContinuousMultilinearMap m) (vecF X M c y)`. Use function extensionality and compare the values at `y`. Use `show Φ (X.B.tens (vecF X M c y)) = Φ (m (vecF X M c y))`. Rewrite using `[hm]`.

Rewrite using `[e]`. Conclude with `(((Φ.compContinuousMultilinearMap m).contDiff (n := ∞)).restrict_scalars ℝ).comp hCd`. Establish `he : ∀ τ, ∀ a ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ y, F (Function.update y τ (M.rep τ a (y τ))) = ρ (atTau θ (D.sp.Y 0) τ a) (F y)`. Introduce `τ a ha y`. Take `⟨q1, q2⟩` from `hat τ a ha`.

Rewrite using `[h3]`. Use `GlobalTheory.TensRep.hom_tens X.B.I X.B.tens_spec hA q1 _ _ fun v => ?_` and prove the remaining obligations. Take `⟨τ', rfl⟩` from `X.pl.symm.surjective v`. Rewrite using `[vecF_apply, vecF_apply]`. Distinguish the cases in `e : τ' = τ`.

Substitute `e` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `hc _ a ha _`. Rewrite using `[Function.update_of_ne e]`. Establish `q : (iotaX X h (atTau θ (D.sp.Y 0) τ a)).1 (X.pl.symm τ') = 1` using `q2 _ (X.pl.symm.injective.ne e)`.

Rewrite using `[q]`. Establish `: X.B.σ (X.pl.symm τ') 1 = 1` using `(X.ds _).2.2.1.1.1`. Use `show _ = X.B.σ (X.pl.symm τ') 1 _`. Rewrite using `[this]`. Both sides reduce to the same expression.

Take `⟨Rr, L, hL, hR, hb⟩` from `GlobalTheory.TensRep.exists_adelic_rep (ι := fun v x => X.B.I.ext v (T x)) hθ h1 h2 h5 h6 h7 h8 h9 hU`. Establish `hp : ∀ y : M.Vec, Continuous (Rr (F fun τ => (y τ : M.H τ))) ∧ (fun z => X.B.I.ext (F fun τ => (y τ : M.H τ)) (T z)) =ᵐ[μ] Rr (F fun τ => (y τ : M.H τ))` using `fun y => hR _ (GlobalTheory.ConjRowRep.smooth_of_contDiff θ M ρ F hF he y) (fun k hk hk' => by`. Rewrite using `[h3]`. Establish `e : T k = (1, (T k).2)` using `Prod.ext (hf k hk') rfl`. Rewrite using `[e]`.

Conclude with `hlev _ (hUg k hk) _)`. Establish `hrepr : ∀ y : M.Vec, Formalism.L2.SG.EvalTOntoRep.IsContRep X (F fun τ => (y τ : M.H τ)) (fun z => Rr (F fun τ => (y τ : M.H τ)) (T.symm z))`. Introduce `y`. Take `⟨p1, p2⟩` from `hp y`. Use `GlobalTheory.RepSmooth.isContRep_of_ae X.B (p1.comp hT') (fun γ hγ x => ?_) ?_` and prove the remaining obligations.

Establish `e : (fun x => Rr (F fun τ => (y τ : M.H τ)) (T.symm γ * x)) = Rr (F fun τ => (y τ : M.H τ))` using `((p1.comp (continuous_const_mul _)).ae_eq_iff_eq μ p1).1 (Filter.EventuallyEq.trans (((measurePreserving_mul_left μ _).quasiMeasurePreserving.ae p2).mono fun _ hy => hy.symm) ((h10 (T.symm γ) (by rw [T.apply_symm_apply]; exact hγ) _).trans p2))`. Rewrite using `[map_mul]`. Conclude with `congrFun e _`. Use `filter_upwards [h4 _ p2] with x hx`. Rewrite using `[← hx, T.apply_symm_apply]`.

Establish `hval : ∀ u : M.Vec, GlobalTheory.ConjRowMult.conjMap X M c Φ h t u x = star (Rr (F fun τ => (u τ : M.H τ)) (x * t⁻¹))`. Introduce `u`. Rewrite using `[GlobalTheory.ConjRowMult.conjMap_apply]`. Establish `e` using `GlobalTheory.ConjRowMult.contRepL_spec X (hrepr u)`. Use `show star (GlobalTheory.ConjRowMult.contRepL X (F fun τ => (u τ : M.H τ)) (T (x * t⁻¹))) = _`.

Rewrite using `[e]`. Simplify using `only [MulEquiv.symm_apply_apply]`. Use `haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D (D.sp.Y 0) S M τ).1`. Establish `hH : ∀ τ, (gramAt D (D.sp.Y 0) τ).IsHermitian` using `GlobalTheory.SmoothAutCheck.gramAt_herm (D.sp.Y 0)`. Establish `hdet : ∀ τ, (gramAt D (D.sp.Y 0) τ).det ≠ 0` using `fun τ => (GlobalTheory.SmoothAutCheck.gramAt_unit (D.sp.Y 0) τ).ne_zero`.

Establish `hsv` using `fun τ => GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv (D.sp.Y 0).rank (gramAt D (D.sp.Y 0) τ) (M.H τ) (M.rep τ) (hH τ) (hdet τ) (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D (D.sp.Y 0) S M τ).2.1`. Establish `hsm : ∀ τ, ∀ Y ∈ lieAt (D.sp.Y 0) τ, ∀ w : M.sm τ, dRep (M.rep τ) Y (w : M.H τ) ∈ M.sm τ` using `fun τ Y hY w => Submodule.subset_span (((hsv τ).2 w ((hsv τ).1 w w.2)).2.1 Y hY).1`. Establish `hder : ∀ (y : M.Vec) τ', ∀ Y ∈ lieAt (D.sp.Y 0) τ', GlobalTheory.HolDict.dL2 θ (D.sp.Y 0) ρ (τ', Y) (F fun σ => (y σ : M.H σ)) = F (Function.update (fun σ => (y σ : M.H σ)) τ' (dRep (M.rep τ') Y (y τ')))`. Introduce `y τ' Y hY`. Set `Lc : M.H τ' →L[ℝ] X.B.H (X.pl.symm τ')` to `{ toFun := c τ' map_add' := (c τ').map_add map_smul' := fun r z => by`.

Rewrite using `[← Complex.coe_smul, (c τ').map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul]`. Both sides reduce to the same expression. Use `cont := (c τ').continuous }`. Set `Sl : M.H τ' →L[ℝ] L2X X` to `(Φ.restrictScalars ℝ).comp (((m.toContinuousLinearMap (vecF X M c fun σ => (y σ : M.H σ)) (X.pl.symm τ')).restrictScalars ℝ).comp Lc)`. Establish `hSl : ∀ z, Sl z = F (Function.update (fun σ => (y σ : M.H σ)) τ' z)`.

Introduce `z`. Use `show Φ (m (Function.update (vecF X M c fun σ => (y σ : M.H σ)) (X.pl.symm τ') (c τ' z))) = Φ (X.B.tens (vecF X M c (Function.update (fun σ => (y σ : M.H σ)) τ' z)))`. Rewrite using `[vecF_update, hm]`. Establish `e : (fun s : ℝ => ρ (oneP θ (D.sp.Y 0) τ' Y s) (F fun σ => (y σ : M.H σ))) = fun s => Sl (M.rep τ' (NormedSpace.exp (s • Y)) (y τ'))`. Use function extensionality and compare the values at `s`.

Rewrite using `[hSl]`. Conclude with `(he τ' _ (GlobalTheory.SmoothMultilinear.exp_mem _ _ hY s) _).symm`. Unfold `GlobalTheory.HolDict.dL2`. Simplify using `only`. Rewrite using `[e, ← hSl]`.

Establish `h1'` using `GlobalTheory.SmoothMultilinear.hasDerivAt_of_smooth _ _ _ (GlobalTheory.SmoothMultilinear.smooth_of_span _ _ _ (y τ').2) Y hY`. Conclude with `(Sl.hasFDerivAt.comp_hasDerivAt 0 h1').deriv`. Establish `hbd : ∀ (y : ∀ σ, M.H σ) (τ' : D.what₂.Tau) (z : M.H τ'), ‖F (Function.update y τ' z)‖ ≤ (‖Φ‖ * ∏ σ ∈ Finset.univ.erase τ', ‖y σ‖) * ‖z‖`. Introduce `y τ' z`. Establish `e2 : ∏ v, ‖vecF X M c (Function.update y τ' z) v‖ = ∏ σ, ‖Function.update y τ' z σ‖` using `(Fintype.prod_equiv X.pl.symm (fun σ => ‖Function.update y τ' z σ‖) (fun v => ‖vecF X M c (Function.update y τ' z) v‖) fun σ => by`.

Simplify using `only [vecF_apply, LinearIsometryEquiv.norm_map]).symm`. Establish `e3 : ∏ σ, ‖Function.update y τ' z σ‖ = ‖z‖ * ∏ σ ∈ Finset.univ.erase τ', ‖y σ‖`. Rewrite using `[← Finset.mul_prod_erase Finset.univ (fun σ => ‖Function.update y τ' z σ‖) (Finset.mem_univ τ')]`. Simplify using `only [Function.update_self]`. Use `congr 1`.

Conclude with `Finset.prod_congr rfl fun σ hσ => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hσ)]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨c0, hc0⟩` from `hb (x * t⁻¹)`. Take `⟨ℓ, hℓ⟩` from `LinearMap.exists_extend ((LinearMap.proj x : (GA D (D.sp.Y 0) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (GlobalTheory.ConjRowMult.conjMap X M c Φ h t).toLinearMap v τ)`. Establish `hℓ' : ∀ w : M.sm τ, ℓ w = GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) x` using `fun w => LinearMap.congr_fun hℓ w`.

Use `⟨ℓ, ?_, hℓ'⟩` and prove the remaining obligations. Take `⟨C', hC', hbd'⟩` from `GlobalTheory.BackForm.sum_bound (fun l (w : M.sm τ) => ‖l.foldr (GlobalTheory.HolDict.dL2 θ (D.sp.Y 0) ρ) (F fun σ => ((Function.update v τ w σ : M.sm σ) : M.H σ))‖) (fun l (w : M.sm τ) => ‖(GlobalTheory.BackForm.lettersAt τ l).foldr (dRep (M.rep τ)) (w : M.H τ)‖) (fun _ _ => nor …`. Introduce `l hl`. Use `⟨‖Φ‖ * ∏ σ ∈ Finset.univ.erase τ, ‖(GlobalTheory.BackForm.lettersAt σ l).foldr (dRep (M.rep σ)) (v σ : M.H σ)‖, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[word_fun ρ F hsm hder l (hL l hl)]`.

Establish `e : (fun σ => (GlobalTheory.BackForm.lettersAt σ l).foldr (dRep (M.rep σ)) ((Function.update v τ w σ : M.sm σ) : M.H σ)) = Function.update (fun σ => (GlobalTheory.BackForm.lettersAt σ l).foldr (dRep (M.rep σ)) (v σ : M.H σ)) τ ((GlobalTheory.BackForm.lettersAt τ l).foldr (dRep (M …`. Use function extensionality and compare the values at `σ`. Distinguish the cases in `hσ : σ = τ`. Substitute `hσ` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Function.update_of_ne hσ]`. Rewrite using `[e]`. Conclude with `hbd _ τ _)`. Use `⟨L.map (GlobalTheory.BackForm.lettersAt τ), |c0| * C', ?_, fun w hw => ?_⟩` and prove the remaining obligations. Introduce `l hl`.

Take `⟨l', h', rfl⟩` from `List.mem_map.1 hl`. Conclude with `GlobalTheory.BackForm.lettersAt_mem (hL l' h')`. Establish `hw' : w ∈ M.sm τ` using `Submodule.subset_span hw`. Establish `h1` using `hℓ' ⟨w, hw'⟩`. Establish `h2` using `hbd' ⟨w, hw'⟩`.

Establish `h3` using `hc0 (F fun σ => ((Function.update v τ ⟨w, hw'⟩ σ : M.sm σ) : M.H σ))`. Rewrite using `[List.map_map, mul_assoc]`. Simplify using `only at h1`. Rewrite using `[h1, hval, norm_star]`. Use `h3.trans ((mul_le_mul_of_nonneg_right (le_abs_self c0) (List.sum_nonneg ?_)).trans (mul_le_mul_of_nonneg_left h2 (abs_nonneg c0)))` and prove the remaining obligations.

Introduce `z hz`. Take `⟨q, -, rfl⟩` from `List.mem_map.1 hz`. Conclude with `norm_nonneg _`.
-/
theorem sobCont_conjMap {D : D7} {S : D.what₂.Tau → SPar} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (θ : InfFam D) (M : DSModel (D.sp.Y 0) S) (t : GA D (D.sp.Y 0))
    (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (hθ : IsInfFam θ)
    (hf : ∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) → (iotaX X h k).1 = 1)
    (hat : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau θ (D.sp.Y 0) τ g)).2 = 1 ∧
      ∀ v, v ≠ X.pl.symm τ → (iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 v = 1)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) =
      X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w))
    (Φ : X.B.Hs →L[ℂ] L2X X) (hΦ : Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re)
    (τ : D.what₂.Tau) (v : M.Vec) (x : GA D (D.sp.Y 0)) :
    ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt (D.sp.Y 0) τ) (M.rep τ) ℓ ∧
      ∀ w : M.sm τ, ℓ w = GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) x := by
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (D.sp.Y 0)
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
  obtain ⟨m, hm, hn⟩ := GlobalTheory.exists_continuousMultilinearMap_of_inner_prod (H := X.B.H) X.B.tens
    X.B.tens_spec.1 X.B.tens_spec.2.2
  have hCd : ContDiff ℝ ∞ (vecF X M c) := by
    refine contDiff_pi.2 fun v => ?_
    obtain ⟨τ, rfl⟩ := X.pl.symm.surjective v
    simp only [vecF_apply]
    exact (GlobalTheory.ConjRowRep.contDiff_anti (c τ)).comp (contDiff_pi.1 contDiff_id τ)
  let F : (∀ τ, M.H τ) → L2X X := fun y => Φ (X.B.tens (vecF X M c y))
  have hF : ContDiff ℝ ∞ F := by
    have e : F = fun y => (Φ.compContinuousMultilinearMap m) (vecF X M c y) := by
      funext y
      show Φ (X.B.tens (vecF X M c y)) = Φ (m (vecF X M c y))
      rw [hm]
    rw [e]
    exact (((Φ.compContinuousMultilinearMap m).contDiff (n := ∞)).restrict_scalars ℝ).comp hCd
  have he : ∀ τ, ∀ a ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ y,
      F (Function.update y τ (M.rep τ a (y τ))) = ρ (atTau θ (D.sp.Y 0) τ a) (F y) := by
    intro τ a ha y
    obtain ⟨q1, q2⟩ := hat τ a ha
    rw [h3]
    refine GlobalTheory.TensRep.hom_tens X.B.I X.B.tens_spec hA q1 _ _ fun v => ?_
    obtain ⟨τ', rfl⟩ := X.pl.symm.surjective v
    rw [vecF_apply, vecF_apply]
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
      rfl
  obtain ⟨Rr, L, hL, hR, hb⟩ := GlobalTheory.TensRep.exists_adelic_rep (ι := fun v x => X.B.I.ext v (T x)) hθ h1 h2 h5 h6
    h7 h8 h9 hU
  have hp : ∀ y : M.Vec, Continuous (Rr (F fun τ => (y τ : M.H τ))) ∧
      (fun z => X.B.I.ext (F fun τ => (y τ : M.H τ)) (T z)) =ᵐ[μ] Rr (F fun τ => (y τ : M.H τ)) := fun y =>
    hR _ (GlobalTheory.ConjRowRep.smooth_of_contDiff θ M ρ F hF he y) (fun k hk hk' => by
      rw [h3]
      have e : T k = (1, (T k).2) := Prod.ext (hf k hk') rfl
      rw [e]
      exact hlev _ (hUg k hk) _)
  have hrepr : ∀ y : M.Vec, Formalism.L2.SG.EvalTOntoRep.IsContRep X (F fun τ => (y τ : M.H τ))
      (fun z => Rr (F fun τ => (y τ : M.H τ)) (T.symm z)) := by
    intro y
    obtain ⟨p1, p2⟩ := hp y
    refine GlobalTheory.RepSmooth.isContRep_of_ae X.B (p1.comp hT') (fun γ hγ x => ?_) ?_
    · have e : (fun x => Rr (F fun τ => (y τ : M.H τ)) (T.symm γ * x)) = Rr (F fun τ => (y τ : M.H τ)) :=
        ((p1.comp (continuous_const_mul _)).ae_eq_iff_eq μ p1).1
          (Filter.EventuallyEq.trans
            (((measurePreserving_mul_left μ _).quasiMeasurePreserving.ae p2).mono fun _ hy => hy.symm)
            ((h10 (T.symm γ) (by rw [T.apply_symm_apply]; exact hγ) _).trans p2))
      rw [map_mul]
      exact congrFun e _
    · filter_upwards [h4 _ p2] with x hx
      rw [← hx, T.apply_symm_apply]
  have hval : ∀ u : M.Vec, GlobalTheory.ConjRowMult.conjMap X M c Φ h t u x =
      star (Rr (F fun τ => (u τ : M.H τ)) (x * t⁻¹)) := by
    intro u
    rw [GlobalTheory.ConjRowMult.conjMap_apply]
    have e := GlobalTheory.ConjRowMult.contRepL_spec X (hrepr u)
    show star (GlobalTheory.ConjRowMult.contRepL X (F fun τ => (u τ : M.H τ)) (T (x * t⁻¹))) = _
    rw [e]
    simp only [MulEquiv.symm_apply_apply]
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D (D.sp.Y 0) S M τ).1
  have hH : ∀ τ, (gramAt D (D.sp.Y 0) τ).IsHermitian := GlobalTheory.SmoothAutCheck.gramAt_herm (D.sp.Y 0)
  have hdet : ∀ τ, (gramAt D (D.sp.Y 0) τ).det ≠ 0 := fun τ => (GlobalTheory.SmoothAutCheck.gramAt_unit (D.sp.Y 0) τ).ne_zero
  have hsv := fun τ => GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv (D.sp.Y 0).rank (gramAt D (D.sp.Y 0) τ) (M.H τ) (M.rep τ) (hH τ) (hdet τ)
    (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D (D.sp.Y 0) S M τ).2.1
  have hsm : ∀ τ, ∀ Y ∈ lieAt (D.sp.Y 0) τ, ∀ w : M.sm τ, dRep (M.rep τ) Y (w : M.H τ) ∈ M.sm τ :=
    fun τ Y hY w => Submodule.subset_span (((hsv τ).2 w ((hsv τ).1 w w.2)).2.1 Y hY).1
  have hder : ∀ (y : M.Vec) τ', ∀ Y ∈ lieAt (D.sp.Y 0) τ',
      GlobalTheory.HolDict.dL2 θ (D.sp.Y 0) ρ (τ', Y) (F fun σ => (y σ : M.H σ)) =
        F (Function.update (fun σ => (y σ : M.H σ)) τ' (dRep (M.rep τ') Y (y τ'))) := by
    intro y τ' Y hY
    let Lc : M.H τ' →L[ℝ] X.B.H (X.pl.symm τ') :=
      { toFun := c τ'
        map_add' := (c τ').map_add
        map_smul' := fun r z => by
          rw [← Complex.coe_smul, (c τ').map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul]; rfl
        cont := (c τ').continuous }
    let Sl : M.H τ' →L[ℝ] L2X X := (Φ.restrictScalars ℝ).comp
      (((m.toContinuousLinearMap (vecF X M c fun σ => (y σ : M.H σ)) (X.pl.symm τ')).restrictScalars ℝ).comp Lc)
    have hSl : ∀ z, Sl z = F (Function.update (fun σ => (y σ : M.H σ)) τ' z) := by
      intro z
      show Φ (m (Function.update (vecF X M c fun σ => (y σ : M.H σ)) (X.pl.symm τ') (c τ' z))) =
        Φ (X.B.tens (vecF X M c (Function.update (fun σ => (y σ : M.H σ)) τ' z)))
      rw [vecF_update, hm]
    have e : (fun s : ℝ => ρ (oneP θ (D.sp.Y 0) τ' Y s) (F fun σ => (y σ : M.H σ))) =
        fun s => Sl (M.rep τ' (NormedSpace.exp (s • Y)) (y τ')) := by
      funext s
      rw [hSl]
      exact (he τ' _ (GlobalTheory.SmoothMultilinear.exp_mem _ _ hY s) _).symm
    unfold GlobalTheory.HolDict.dL2
    simp only
    rw [e, ← hSl]
    have h1' := GlobalTheory.SmoothMultilinear.hasDerivAt_of_smooth _ _ _
      (GlobalTheory.SmoothMultilinear.smooth_of_span _ _ _ (y τ').2) Y hY
    exact (Sl.hasFDerivAt.comp_hasDerivAt 0 h1').deriv
  have hbd : ∀ (y : ∀ σ, M.H σ) (τ' : D.what₂.Tau) (z : M.H τ'),
      ‖F (Function.update y τ' z)‖ ≤ (‖Φ‖ * ∏ σ ∈ Finset.univ.erase τ', ‖y σ‖) * ‖z‖ := by
    intro y τ' z
    have e2 : ∏ v, ‖vecF X M c (Function.update y τ' z) v‖ = ∏ σ, ‖Function.update y τ' z σ‖ :=
      (Fintype.prod_equiv X.pl.symm (fun σ => ‖Function.update y τ' z σ‖)
        (fun v => ‖vecF X M c (Function.update y τ' z) v‖) fun σ => by
          simp only [vecF_apply, LinearIsometryEquiv.norm_map]).symm
    have e3 : ∏ σ, ‖Function.update y τ' z σ‖ = ‖z‖ * ∏ σ ∈ Finset.univ.erase τ', ‖y σ‖ := by
      rw [← Finset.mul_prod_erase Finset.univ (fun σ => ‖Function.update y τ' z σ‖) (Finset.mem_univ τ')]
      simp only [Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun σ hσ => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hσ)]
    calc ‖F (Function.update y τ' z)‖ ≤ ‖Φ‖ * ‖X.B.tens (vecF X M c (Function.update y τ' z))‖ := Φ.le_opNorm _
      _ = _ := by rw [hn, e2, e3]; ring
  obtain ⟨c0, hc0⟩ := hb (x * t⁻¹)
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ((LinearMap.proj x : (GA D (D.sp.Y 0) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
    (GlobalTheory.ConjRowMult.conjMap X M c Φ h t).toLinearMap v τ)
  have hℓ' : ∀ w : M.sm τ, ℓ w = GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) x :=
    fun w => LinearMap.congr_fun hℓ w
  refine ⟨ℓ, ?_, hℓ'⟩
  obtain ⟨C', hC', hbd'⟩ := GlobalTheory.BackForm.sum_bound
    (fun l (w : M.sm τ) => ‖l.foldr (GlobalTheory.HolDict.dL2 θ (D.sp.Y 0) ρ)
      (F fun σ => ((Function.update v τ w σ : M.sm σ) : M.H σ))‖)
    (fun l (w : M.sm τ) => ‖(GlobalTheory.BackForm.lettersAt τ l).foldr (dRep (M.rep τ)) (w : M.H τ)‖)
    (fun _ _ => norm_nonneg _) L (by
      intro l hl
      refine ⟨‖Φ‖ * ∏ σ ∈ Finset.univ.erase τ,
        ‖(GlobalTheory.BackForm.lettersAt σ l).foldr (dRep (M.rep σ)) (v σ : M.H σ)‖, fun w => ?_⟩
      rw [word_fun ρ F hsm hder l (hL l hl)]
      have e : (fun σ => (GlobalTheory.BackForm.lettersAt σ l).foldr (dRep (M.rep σ))
          ((Function.update v τ w σ : M.sm σ) : M.H σ)) =
          Function.update (fun σ => (GlobalTheory.BackForm.lettersAt σ l).foldr (dRep (M.rep σ)) (v σ : M.H σ)) τ
            ((GlobalTheory.BackForm.lettersAt τ l).foldr (dRep (M.rep τ)) (w : M.H τ)) := by
        funext σ
        by_cases hσ : σ = τ
        · subst hσ; simp
        · simp [Function.update_of_ne hσ]
      rw [e]
      exact hbd _ τ _)
  refine ⟨L.map (GlobalTheory.BackForm.lettersAt τ), |c0| * C', ?_, fun w hw => ?_⟩
  · intro l hl
    obtain ⟨l', h', rfl⟩ := List.mem_map.1 hl
    exact GlobalTheory.BackForm.lettersAt_mem (hL l' h')
  · have hw' : w ∈ M.sm τ := Submodule.subset_span hw
    have h1 := hℓ' ⟨w, hw'⟩
    have h2 := hbd' ⟨w, hw'⟩
    have h3 := hc0 (F fun σ => ((Function.update v τ ⟨w, hw'⟩ σ : M.sm σ) : M.H σ))
    rw [List.map_map, mul_assoc]
    simp only at h1
    rw [h1, hval, norm_star]
    refine h3.trans ((mul_le_mul_of_nonneg_right (le_abs_self c0) (List.sum_nonneg ?_)).trans
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg c0)))
    intro z hz
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hz
    exact norm_nonneg _

end GlobalTheory.ConjRowCont

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `_ D G _ _ Pl0 T A Ks _ _ _ R F X h hlev hgrp hmod _ hιE t c _ _ hc Φ hΦ _ τ v x`. Take `⟨hf, hat, -⟩` from `GlobalTheory.IotaReal.iotaX_real_finite R F X h hlev hgrp hmod hιE`. Conclude with `GlobalTheory.ConjRowCont.sobCont_conjMap X h R.θ (MP R) t c hmod.inf (fun k hk => (hf k).1 hk) (fun τ g hg => ⟨(hat τ g hg).1, (hat τ g hg).2.1⟩) hc Φ hΦ τ v x`.
-/
theorem GlobalTheory.ConjRowCont.conjMap_sobCont : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ (τ : D.what₂.Tau) (v : (MP R).Vec) (x : GA D (Yc D 0)), ∃ ℓ : (MP R).H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt (Yc D 0) τ) ((MP R).rep τ) ℓ ∧ ∀ w : (MP R).sm τ, ℓ w = GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t (Function.update v τ w) x := by
  intro _ D G _ _ Pl0 T A Ks _ _ _ R F X h hlev hgrp hmod _ hιE t c _ _ hc Φ hΦ _ τ v x
  obtain ⟨hf, hat, -⟩ := GlobalTheory.IotaReal.iotaX_real_finite R F X h hlev hgrp hmod hιE
  exact GlobalTheory.ConjRowCont.sobCont_conjMap X h R.θ (MP R) t c hmod.inf (fun k hk => (hf k).1 hk)
    (fun τ g hg => ⟨(hat τ g hg).1, (hat τ g hg).2.1⟩) hc Φ hΦ τ v x

end
