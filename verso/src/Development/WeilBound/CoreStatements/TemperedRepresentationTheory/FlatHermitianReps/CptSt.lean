import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.IrredSt

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

namespace MainStatements.Flath2

/- English proof (translation)
Introduce `hCT D V μ _ _ H _ _ _ π hπ hm f hf`. Establish `c` using `GlobalTheory.Orb.continuous_of_mem_ccAd hf`. Rewrite `hm` using `[GlobalTheory.AutMult.mCusp_eq_Rcusp, Ne, GlobalTheory.AutMult.multIn_eq_zero_iff]`. Take `⟨T, hT, hT0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hm`. Establish `hρ` using `GlobalTheory.Cusp.isUnitaryRep_Rcusp V μ`.

Establish `hb0 : GlobalTheory.AutMult.be T T ≠ 0` using `fun e => by`. Establish `h` using `GlobalTheory.AutMult.be_self_pos hπ hρ hT hT0`. Rewrite `h` using `[e]`. Simplify using `at h`. Establish `key : ∀ x, T.adjoint (T x) = GlobalTheory.AutMult.be T T • x` using `fun x => ext_inner_left ℂ fun y => by`.

Rewrite using `[ContinuousLinearMap.adjoint_inner_right, inner_smul_right (𝕜 := ℂ) (E := H)]`. Conclude with `GlobalTheory.AutMult.inner_eq_be hπ hρ hT hT x y`. Establish `hcomm : T ∘L repOp π μ f = GlobalTheory.Cusp.RcuspOp V μ f ∘L T` using `hπ.unitary.comp_repOp hρ c.1 c.2 T hT.2`. Establish `hR : IsCompactOperator (GlobalTheory.Cusp.RcuspOp V μ f)` using `GlobalTheory.DiscreteSum.isCompactOperator_of_isHilbertSchmidt (hCT D V μ f hf).isHilbertSchmidt`. Establish `hv : ∀ v, T (repOp π μ f v) = GlobalTheory.Cusp.RcuspOp V μ f (T v)` using `fun v => DFunLike.congr_fun hcomm v`.

Establish `e : ⇑(repOp π μ f) = (GlobalTheory.AutMult.be T T)⁻¹ • (⇑T.adjoint ∘ (⇑(GlobalTheory.Cusp.RcuspOp V μ f) ∘ ⇑T))` using `funext fun v => by show repOp π μ f v = (GlobalTheory.AutMult.be T T)⁻¹ • T.adjoint (GlobalTheory.Cusp.RcuspOp V μ f (T v))`. Establish `k : T.adjoint (GlobalTheory.Cusp.RcuspOp V μ f (T v)) = GlobalTheory.AutMult.be T T • repOp π μ f v` using `(congrArg T.adjoint (hv v)).symm.trans (key (repOp π μ f v))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e]`. Conclude with `((hR.comp_clm T).clm_comp T.adjoint).smul (GlobalTheory.AutMult.be T T)⁻¹`.
-/
theorem cptSt : CptSt := by
  intro hCT D V μ _ _ H _ _ _ π hπ hm f hf
  have c := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  rw [GlobalTheory.AutMult.mCusp_eq_Rcusp, Ne, GlobalTheory.AutMult.multIn_eq_zero_iff] at hm
  obtain ⟨T, hT, hT0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  have hρ := GlobalTheory.Cusp.isUnitaryRep_Rcusp V μ
  have hb0 : GlobalTheory.AutMult.be T T ≠ 0 := fun e => by
    have h := GlobalTheory.AutMult.be_self_pos hπ hρ hT hT0
    rw [e] at h
    simp at h
  have key : ∀ x, T.adjoint (T x) = GlobalTheory.AutMult.be T T • x := fun x =>
    ext_inner_left ℂ fun y => by
      rw [ContinuousLinearMap.adjoint_inner_right, inner_smul_right (𝕜 := ℂ) (E := H)]
      exact GlobalTheory.AutMult.inner_eq_be hπ hρ hT hT x y
  have hcomm : T ∘L repOp π μ f = GlobalTheory.Cusp.RcuspOp V μ f ∘L T :=
    hπ.unitary.comp_repOp hρ c.1 c.2 T hT.2
  have hR : IsCompactOperator (GlobalTheory.Cusp.RcuspOp V μ f) :=
    GlobalTheory.DiscreteSum.isCompactOperator_of_isHilbertSchmidt (hCT D V μ f hf).isHilbertSchmidt
  have hv : ∀ v, T (repOp π μ f v) = GlobalTheory.Cusp.RcuspOp V μ f (T v) := fun v =>
    DFunLike.congr_fun hcomm v
  have e : ⇑(repOp π μ f) =
      (GlobalTheory.AutMult.be T T)⁻¹ • (⇑T.adjoint ∘ (⇑(GlobalTheory.Cusp.RcuspOp V μ f) ∘ ⇑T)) := funext fun v => by
    show repOp π μ f v = (GlobalTheory.AutMult.be T T)⁻¹ • T.adjoint (GlobalTheory.Cusp.RcuspOp V μ f (T v))
    have k : T.adjoint (GlobalTheory.Cusp.RcuspOp V μ f (T v)) = GlobalTheory.AutMult.be T T • repOp π μ f v :=
      (congrArg T.adjoint (hv v)).symm.trans (key (repOp π μ f v))
    calc repOp π μ f v = (GlobalTheory.AutMult.be T T)⁻¹ • (GlobalTheory.AutMult.be T T • repOp π μ f v) :=
          (inv_smul_smul₀ hb0 _).symm
      _ = (GlobalTheory.AutMult.be T T)⁻¹ • T.adjoint (GlobalTheory.Cusp.RcuspOp V μ f (T v)) := congrArg _ k.symm
  rw [e]
  exact ((hR.comp_clm T).clm_comp T.adjoint).smul (GlobalTheory.AutMult.be T T)⁻¹

end MainStatements.Flath2
