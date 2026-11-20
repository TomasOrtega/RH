import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

open MeasureTheory

noncomputable section

namespace GlobalTheory.ThKKer

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM Ψ hΨ`. Establish `hT` using `hM.triple`. Establish `hdec` using `(GlobalTheory.T.theta_kernel_decay hKP F E σ B a a' G X om om' hT).2`. Establish `pres : ∀ x, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), om' x Φ ∈ schA F (Fin a' × Fin (a + a'))` using `fun x Φ hΦ => (IsUWeilPair.isUSplitting hT.weil').pres x Φ hΦ`. Establish `hPol : PolData B G.M' ≤ schA F (Fin a' × Fin (a + a'))`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, -, φ, hSB, hev, rfl⟩`. Conclude with `GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2)`. Establish `key : ∀ Ψ ∈ (Submodule.span ℂ {Ψ | Ψ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ ∧ G.M'.I om' Ψ = 0}), Ψ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ ∧ G.M'.I om' Ψ = 0`. Introduce `Ψ hΨ`.

Proceed by induction on `hΨ using Submodule.span_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `zero`. Use `⟨Submodule.zero_mem _, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `h`.

Simplify using `[Model.I, theta, thetaSum]`. Consider the case `add x y _ _ ihx ihy`. Take `⟨hxD, hx0⟩` from `ihx`. Take `⟨hyD, hy0⟩` from `ihy`. Use `⟨Submodule.add_mem _ hxD hyD, ?_⟩` and prove the remaining obligations.

Establish `hxS` using `hPol hxD.1`. Establish `hyS` using `hPol hyD.1`. Use function extensionality and compare the values at `h`. Establish `e : ∀ g, theta om' (x + y) g h = theta om' x g h + theta om' y g h` using `fun g => by`. Simplify using `only [theta, map_add]`.

Conclude with `thetaSum_add F (pres _ x hxS) (pres _ y hyS)`. Establish `ix` using `(hdec x hxD.2).2.1 h`. Establish `iy` using `(hdec y hyD.2).2.1 h`. Establish `hx1` using `congrFun hx0 h`. Establish `hy1` using `congrFun hy0 h`.

Simplify using `only [Model.I, Pi.zero_apply] at hx1 hy1 ⊢`. Rewrite using `[show (fun g => theta om' (x + y) g h) = fun g => theta om' x g h + theta om' y g h from funext e, integral_add ix iy, hx1, hy1, add_zero]`. Consider the case `smul c x _ ih`. Take `⟨hxD, hx0⟩` from `ih`. Use `⟨Submodule.smul_mem _ c hxD, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `h`. Establish `hx1` using `congrFun hx0 h`. Simplify using `only [Model.I, Pi.zero_apply] at hx1 ⊢`. Establish `e : ∀ g, theta om' (c • x) g h = c * theta om' x g h` using `fun g => by`. Simplify using `only [theta, map_smul]`.

Conclude with `thetaSum_smul F c _`. Simplify using `only [e, integral_const_mul, hx1, mul_zero]`. Conclude with `(key Ψ hΨ).2`.
-/
theorem kerZero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Ψ ∈ (Submodule.span ℂ {Ψ | Ψ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ ∧ G.M'.I om' Ψ = 0}), G.M'.I om' Ψ = 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM Ψ hΨ
  have hT := hM.triple
  have hdec := (GlobalTheory.T.theta_kernel_decay hKP F E σ B a a' G X om om' hT).2
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), om' x Φ ∈ schA F (Fin a' × Fin (a + a')) :=
    fun x Φ hΦ => (IsUWeilPair.isUSplitting hT.weil').pres x Φ hΦ
  have hPol : PolData B G.M' ≤ schA F (Fin a' × Fin (a + a')) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, -, φ, hSB, hev, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2)
  have key : ∀ Ψ ∈ (Submodule.span ℂ {Ψ | Ψ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ ∧ G.M'.I om' Ψ = 0}),
      Ψ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ ∧ G.M'.I om' Ψ = 0 := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      refine ⟨Submodule.zero_mem _, ?_⟩
      funext h
      simp [Model.I, theta, thetaSum]
    | add x y _ _ ihx ihy =>
      obtain ⟨hxD, hx0⟩ := ihx
      obtain ⟨hyD, hy0⟩ := ihy
      refine ⟨Submodule.add_mem _ hxD hyD, ?_⟩
      have hxS := hPol hxD.1
      have hyS := hPol hyD.1
      funext h
      have e : ∀ g, theta om' (x + y) g h = theta om' x g h + theta om' y g h := fun g => by
        simp only [theta, map_add]
        exact thetaSum_add F (pres _ x hxS) (pres _ y hyS)
      have ix := (hdec x hxD.2).2.1 h
      have iy := (hdec y hyD.2).2.1 h
      have hx1 := congrFun hx0 h
      have hy1 := congrFun hy0 h
      simp only [Model.I, Pi.zero_apply] at hx1 hy1 ⊢
      rw [show (fun g => theta om' (x + y) g h) = fun g => theta om' x g h + theta om' y g h from funext e,
        integral_add ix iy, hx1, hy1, add_zero]
    | smul c x _ ih =>
      obtain ⟨hxD, hx0⟩ := ih
      refine ⟨Submodule.smul_mem _ c hxD, ?_⟩
      funext h
      have hx1 := congrFun hx0 h
      simp only [Model.I, Pi.zero_apply] at hx1 ⊢
      have e : ∀ g, theta om' (c • x) g h = c * theta om' x g h := fun g => by
        simp only [theta, map_smul]
        exact thetaSum_smul F c _
      simp only [e, integral_const_mul, hx1, mul_zero]
  exact (key Ψ hΨ).2

end GlobalTheory.ThKKer
