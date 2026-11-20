import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStageTriangleTransferStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStageTrianglePolynomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageThetaDictionaryExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareCommutativityProjection

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StageKer

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Pf, φ y ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hc)`. Introduce `h0`.

Use `congrArg ((TensorProduct.rid ℂ Pr).toLinearMap ∘ₗ LinearMap.lTensor Pr φ) h0` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_zero] at this`. Conclude with `hx ((smul_eq_zero.1 this).resolve_left hφ)`.
-/
theorem tmul_ne_zero_of_ne {Pr Pf : Type} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf] {x : Pr} {y : Pf}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Pf, φ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hc)
  intro h0
  have := congrArg ((TensorProduct.rid ℂ Pr).toLinearMap ∘ₗ LinearMap.lTensor Pr φ) h0
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_zero] at this
  exact hx ((smul_eq_zero.1 this).resolve_left hφ)

end GlobalTheory.StageKer

/- English proof (translation)
Introduce `hP hK hL`. Take `⟨c, hc⟩` from `GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and GlobalTheory.T.towerStage_thetaDictionary_exists (GlobalTheory.T.exists_stage_triangle_transfer hP hK hL)) (GlobalTheory.T.exists_stage_triangle_polynomial hP hK hL)`. Use `⟨c, fun ε CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨C0, x0, h⟩` from `hc ε CF hCF`. Use `⟨C0, x0, fun C hC D large₂ a b r T Lc μ hLc G W S hW hN i j p q A A' WW X hX => ?_⟩` and prove the remaining obligations.

Take `⟨⟨h1, h3⟩, h4⟩` from `h C hC D large₂ a b r T Lc μ hLc G`. Take `⟨FA, FA', FW, ea, eb, hD⟩` from `h1 W S hW hN i j p q A A' WW X hX`. Take `⟨lam, s, hlam, hs⟩` from `h3 W S hW hN i j p q A A' WW X hX`. Take `⟨P0, hc0, hne0⟩` from `h4 W S hW hN i j p q A A' WW X hX`. Take `⟨Pr, qP, hq⟩` from `GlobalTheory.T.exists_square_commutativity_projection hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW ea eb`.

Establish `hIs` using `hX.2.2.2.2.2.2.2`. Establish `key : ∀ t P, X.I W.ψ W.θ t P = 0 ↔ qP P = 0`. Introduce `t`. Take `⟨hTr, hInf, hf, -, hk, -⟩` from `hD t`. Take `⟨Pf, y, J, hJ, hI⟩` from `hq _ _ hTr hInf X.m X.fd hIs.meas (X.ω t) (hIs.weil t) (X.f t) hf`.

Establish `eI : ∀ P, X.I W.ψ W.θ t P = J (qP P ⊗ₜ y)` using `fun P => by`. Rewrite using `[← hI P]`. Use function extensionality and compare the values at `h`. Simplify using `only [GlobalTheory.SquareComm.thetaInt, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.I, hk]`. Establish `hne : X.I W.ψ W.θ t (s P0) ≠ 0`.

Rewrite using `[hs t P0 (hc0 t)]`. Conclude with `smul_ne_zero (hlam t) (hne0 t)`. Establish `hy : y ≠ 0`. Introduce and unpack `rfl`. Apply `hne` to reduce the goal to its premises.

Rewrite using `[eI, TensorProduct.tmul_zero, map_zero]`. Establish `hJi : Function.Injective J` using `hJ.resolve_left (by`. Introduce `hJ0`. Apply `hne` to reduce the goal to its premises. Rewrite using `[eI, hJ0]`.

Use the proof step `rfl)`. Introduce `P`. Rewrite using `[eI, map_eq_zero_iff J hJi]`. Prove the components needed by the constructor for the conclusion. Introduce `h0`.

Assume the negation of the conclusion as `hq0`. Conclude with `GlobalTheory.StageKer.tmul_ne_zero_of_ne hq0 hy h0`. Introduce `h0`. Rewrite using `[h0, TensorProduct.zero_tmul]`. Introduce `t t' P h0`.

Conclude with `(key t' P).2 ((key t P).1 h0)`.
-/
theorem GlobalTheory.StageKer.kern_stage : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∀ t t' P, X.I W.ψ W.θ t P = 0 → X.I W.ψ W.θ t' P = 0 := by
  intro hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and GlobalTheory.T.towerStage_thetaDictionary_exists (GlobalTheory.T.exists_stage_triangle_transfer hP hK hL)) (GlobalTheory.T.exists_stage_triangle_polynomial hP hK hL)
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hLc G W S hW hN i j p q A A' WW X hX => ?_⟩
  obtain ⟨⟨h1, h3⟩, h4⟩ := h C hC D large₂ a b r T Lc μ hLc G
  obtain ⟨FA, FA', FW, ea, eb, hD⟩ := h1 W S hW hN i j p q A A' WW X hX
  obtain ⟨lam, s, hlam, hs⟩ := h3 W S hW hN i j p q A A' WW X hX
  obtain ⟨P0, hc0, hne0⟩ := h4 W S hW hN i j p q A A' WW X hX
  obtain ⟨Pr, qP, hq⟩ := GlobalTheory.T.exists_square_commutativity_projection hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW ea eb
  have hIs := hX.2.2.2.2.2.2.2
  have key : ∀ t P, X.I W.ψ W.θ t P = 0 ↔ qP P = 0 := by
    intro t
    obtain ⟨hTr, hInf, hf, -, hk, -⟩ := hD t
    obtain ⟨Pf, y, J, hJ, hI⟩ := hq _ _ hTr hInf X.m X.fd hIs.meas (X.ω t) (hIs.weil t) (X.f t) hf
    have eI : ∀ P, X.I W.ψ W.θ t P = J (qP P ⊗ₜ y) := fun P => by
      rw [← hI P]; funext h; simp only [GlobalTheory.SquareComm.thetaInt, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.I, hk]
    have hne : X.I W.ψ W.θ t (s P0) ≠ 0 := by
      rw [hs t P0 (hc0 t)]; exact smul_ne_zero (hlam t) (hne0 t)
    have hy : y ≠ 0 := by
      rintro rfl; apply hne; rw [eI, TensorProduct.tmul_zero, map_zero]
    have hJi : Function.Injective J := hJ.resolve_left (by
      intro hJ0; apply hne; rw [eI, hJ0]; rfl)
    intro P
    rw [eI, map_eq_zero_iff J hJi]
    constructor
    · intro h0; by_contra hq0; exact GlobalTheory.StageKer.tmul_ne_zero_of_ne hq0 hy h0
    · intro h0; rw [h0, TensorProduct.zero_tmul]
  intro t t' P h0
  exact (key t' P).2 ((key t P).1 h0)

end
