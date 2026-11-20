import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime

import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalMatchingOfHoweDualityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleMatchExistenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainFrameTripleHaarIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainFrameTripleHaarIdentityTwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTowerStageFiniteCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageSeesawDictionaryFramesSignatures
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StageSmallNz

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Pf, φ y ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hc)`. Introduce `h0`.

Use `congrArg ((TensorProduct.rid ℂ Pr).toLinearMap ∘ₗ LinearMap.lTensor Pr φ) h0` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_zero] at this`. Conclude with `hx ((smul_eq_zero.1 this).resolve_left hφ)`.
-/
theorem tmul_ne_zero {Pr Pf : Type} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf] {x : Pr} {y : Pf}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Pf, φ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hc)
  intro h0
  have := congrArg ((TensorProduct.rid ℂ Pr).toLinearMap ∘ₗ LinearMap.lTensor Pr φ) h0
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_zero] at this
  exact hx ((smul_eq_zero.1 this).resolve_left hφ)

/- English proof (translation)
Assume the negation of the conclusion as `hP0`. Rewrite `hP0` using `[not_nontrivial_iff_subsingleton]`. Establish `hz : ∀ z : Pr ⊗[ℂ] Pf, z = 0` using `fun z => by`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rfl`.

Consider the case `tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]`. Consider the case `add x y hx hy => rw [hx, hy, add_zero]`. Take `⟨u, v, huv⟩` from `exists_pair_ne Pi`. Conclude with `huv (by rw [← e.apply_symm_apply u, ← e.apply_symm_apply v, hz (e.symm u), hz (e.symm v)])`.
-/
theorem nontrivial_left {Pr Pf Pi : Type} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf]
    [AddCommGroup Pi] [Module ℂ Pi] [Nontrivial Pi] (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi) : Nontrivial Pr := by
  by_contra hP0
  rw [not_nontrivial_iff_subsingleton] at hP0
  have hz : ∀ z : Pr ⊗[ℂ] Pf, z = 0 := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  obtain ⟨u, v, huv⟩ := exists_pair_ne Pi
  exact huv (by rw [← e.apply_symm_apply u, ← e.apply_symm_apply v, hz (e.symm u), hz (e.symm v)])

/- English proof (translation)
Introduce `hP hK hL`. Establish `hH` using `hP.howeDualityReal`. Establish `hLM` using `GlobalTheory.T.local_matching_of_howe_duality hH hP hK hL`. Take `⟨c, hc⟩` from `GlobalTheory.SqTop.Model.gBig_and GlobalTheory.T.towerStage_seesawDictionary_framesSignatures (GlobalTheory.T.square_tower_stage_finite_compat hP hK hL)`. Use `⟨c, fun ε CF hCF => ?_⟩` and prove the remaining obligations.

Take `⟨C0, x0, h⟩` from `hc ε CF hCF`. Use `⟨C0, x0, fun C hC D large₂ a b r T Lc μ hLc G W S hW hN i j p A A' WW X hX hint => ?_⟩` and prove the remaining obligations. Take `⟨hd, h3⟩` from `h C hC D large₂ a b r T Lc μ hLc G`. Take `⟨FA, FA', FW, ea, eb, -, hsA', -, hD⟩` from `hd W i j p 0 A A' WW X hX`. Establish `hdef : ∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0` using `fun τ => by simpa using hsA' τ`.

Establish `hIs` using `hX.2.2.2.2.2.2.2`. Take `⟨Pr, q, q', hq, hq', hLMt⟩` from `hLM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW ea eb`. Establish `key : ∀ t, ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi) (pm : (WO A WW → ℂ) →ₗ[ℂ] Pi) (pm' : (WO A' WW → ℂ) →ₗ[ℂ] Pi), GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc. …`. Introduce `t`. Take `⟨hTr, hInf, hf, hf', -, -⟩` from `hD t`.

Take `⟨hex, hfac⟩` from `hLMt _ _ hTr hInf`. Take `⟨Pm, rf, rl, pm, pm', hm⟩` from `GlobalTheory.T.triple_match_existence hH hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hex (X.ω t) (X.ω' t) (hIs.weil t) (hIs.weil' t)`. Take `⟨Pf, rr, rr', e, -, -, hr, hr'⟩` from `hfac _ _ _ _ _ _ _ hm`. Establish `hy` using `h3 W i j p 0 A A' WW X hX FA FA' FW t hf hf' Pm rf rl pm pm' hm Pr Pf q q' rr rr' e hq hq' hr hr'`. Use `haveI : Nontrivial Pm := hm.irred.1`.

Use `⟨Pm, rf, rl, pm, pm', hm, nontrivial_left e, fun P' hP' => ?_⟩` and prove the remaining obligations. Rewrite using `[hr' _ hf']`. Conclude with `e.map_ne_zero_iff.2 (tmul_ne_zero hP' hy)`. Distinguish the cases in `hT : Nonempty T`. Take `⟨t0⟩` from `hT haveI : Nontrivial Pr := (key t0).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1`.

Take `⟨x, hx⟩` from `exists_ne (0 : Pr)`. Take `⟨P0, rfl⟩` from `hq' x`. Use `⟨P0, fun t h0 => ?_⟩` and prove the remaining obligations. Take `⟨hTr, -, -, hf', -, hk'⟩` from `hD t`. Take `⟨Pm, rf, rl, pm, pm', hm, -, hne⟩` from `key t`.

Establish `memF : ∀ P', GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ GlobalTheory.SquareComm.algF W.ψ W.θ false FA' FW` using `fun P' => Submodule.subset_span ⟨_, P', hf', rfl⟩`. Establish `eI' : GlobalTheory.SquareComm.thetaInt (X.ω' t) X.m' X.fd' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P0) = X.I' W.ψ W.θ t P0`. Use function extensionality and compare the values at `h`. Simplify using `only [GlobalTheory.SquareComm.thetaInt, Tri.I', hk']`. Take `⟨Φ, hΦ, hΦ0⟩` from `GlobalTheory.T.chain_frame_triple_haar_identity_two hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hdef X.m' X.fd' hIs.meas' _ _ _ _ _ _ _ hm`.

Conclude with `hΦ0 (GlobalTheory.T.chain_frame_triple_haar_identity hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hdef X.m X.fd X.m' X.fd' hIs.meas hIs.meas' _ _ _ _ _ _ _ hm _ (memF P0) (hne P0 hx) (by rw [eI']; exact h0) Φ hΦ)`. Conclude with `⟨0, fun t => (hT ⟨t⟩).elim⟩`.
-/
theorem stage_small_nonzero_zero : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p 0 X →
      (∀ t P' h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') →
      ∃ P' : PolF D WW.rank A'.rank, ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  intro hP hK hL
  have hH := hP.howeDualityReal
  have hLM := GlobalTheory.T.local_matching_of_howe_duality hH hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and GlobalTheory.T.towerStage_seesawDictionary_framesSignatures (GlobalTheory.T.square_tower_stage_finite_compat hP hK hL)
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hLc G W S hW hN i j p A A' WW X hX hint => ?_⟩
  obtain ⟨hd, h3⟩ := h C hC D large₂ a b r T Lc μ hLc G
  obtain ⟨FA, FA', FW, ea, eb, -, hsA', -, hD⟩ := hd W i j p 0 A A' WW X hX
  have hdef : ∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0 := fun τ => by simpa using hsA' τ
  have hIs := hX.2.2.2.2.2.2.2
  obtain ⟨Pr, q, q', hq, hq', hLMt⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW ea eb

  have key : ∀ t, ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi)
      (pm : (WO A WW → ℂ) →ₗ[ℂ] Pi) (pm' : (WO A' WW → ℂ) →ₗ[ℂ] Pi),
      GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
        (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl pm pm' ∧ Nontrivial Pr ∧
      ∀ P', q' P' ≠ 0 → pm' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P') ≠ 0 := by
    intro t
    obtain ⟨hTr, hInf, hf, hf', -, -⟩ := hD t
    obtain ⟨hex, hfac⟩ := hLMt _ _ hTr hInf
    obtain ⟨Pm, rf, rl, pm, pm', hm⟩ := GlobalTheory.T.triple_match_existence hH hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hex
      (X.ω t) (X.ω' t) (hIs.weil t) (hIs.weil' t)
    obtain ⟨Pf, rr, rr', e, -, -, hr, hr'⟩ := hfac _ _ _ _ _ _ _ hm
    have hy := h3 W i j p 0 A A' WW X hX FA FA' FW t hf hf' Pm rf rl pm pm' hm Pr Pf q q' rr rr' e hq hq' hr hr'
    haveI : Nontrivial Pm := hm.irred.1
    refine ⟨Pm, rf, rl, pm, pm', hm, nontrivial_left e, fun P' hP' => ?_⟩
    rw [hr' _ hf']
    exact e.map_ne_zero_iff.2 (tmul_ne_zero hP' hy)
  by_cases hT : Nonempty T
  · obtain ⟨t0⟩ := hT
    haveI : Nontrivial Pr := (key t0).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1
    obtain ⟨x, hx⟩ := exists_ne (0 : Pr)
    obtain ⟨P0, rfl⟩ := hq' x
    refine ⟨P0, fun t h0 => ?_⟩
    obtain ⟨hTr, -, -, hf', -, hk'⟩ := hD t
    obtain ⟨Pm, rf, rl, pm, pm', hm, -, hne⟩ := key t
    have memF : ∀ P', GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ GlobalTheory.SquareComm.algF W.ψ W.θ false FA' FW :=
      fun P' => Submodule.subset_span ⟨_, P', hf', rfl⟩
    have eI' : GlobalTheory.SquareComm.thetaInt (X.ω' t) X.m' X.fd' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P0) =
        X.I' W.ψ W.θ t P0 := by
      funext h; simp only [GlobalTheory.SquareComm.thetaInt, Tri.I', hk']
    obtain ⟨Φ, hΦ, hΦ0⟩ := GlobalTheory.T.chain_frame_triple_haar_identity_two hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hdef X.m' X.fd' hIs.meas'
      _ _ _ _ _ _ _ hm
    exact hΦ0 (GlobalTheory.T.chain_frame_triple_haar_identity hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hdef X.m X.fd X.m' X.fd' hIs.meas hIs.meas'
      _ _ _ _ _ _ _ hm _ (memF P0) (hne P0 hx) (by rw [eI']; exact h0) Φ hΦ)
  · exact ⟨0, fun t => (hT ⟨t⟩).elim⟩

end GlobalTheory.StageSmallNz

end
