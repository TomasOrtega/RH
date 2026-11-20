import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfOrbitAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermCarrierStability.TermStableHolds

noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
open Formalism.L2.SG.HidaSetting Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

section TermCarSec

def RatIsoC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (γ : X.B.I.GA), γ ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I →
    ∃ σ : (VS D).V ≃ₗ[D.host.E] (VS D).V, RatLink X γ σ ∧ σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT

def ModGOfAtC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (g1 : X.B.I.Gf) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    (∀ y, y ∈ Λ ↔ X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf) →
    ∀ v, InAt X.B.I X.B.g X.B.g (X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd v)) → ModG (VS D) Λ (gS D) v

def FrameCongC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (ρ : (Y.cs u).Cl) (ρ' : (Y.cs u').Cl) (γ : X.B.I.GA) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    RatLink X γ σ → kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) γ ∈ X.K2 →
    ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E),
      (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧
      ∀ b, InAt X.B.I X.B.g X.B.g (X.B.I.fmat (aC (Y.cs u) ρ)⁻¹ *ᵥ
        incl X.B.I (X.crd (σ (frame (lf D (X.Fu u')) b) - frameAct (frame (lf D (X.Fu u))) ξ b)))

section Tr2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
  {γ : S.V ≃ₗ[E] S.V} {T' : E} {x F₂ : LFlag S r T'}

/- English proof (translation)
The claim follows from `PI.TCS.Tr.inf hΛ (PI.TCS.trE_Xsp he).toO`.
-/
theorem transport_x_lattice (Λ₂ Λ : Submodule (𝓞 E) S.V) (hΛ : PI.TCS.Tr γ Λ₂ Λ) (he : ∀ k, F₂.fl.e k = γ (x.fl.e k)) :
    PI.TCS.Tr γ (XLam Λ₂ F₂) (XLam Λ x) :=
  PI.TCS.Tr.inf hΛ (PI.TCS.trE_Xsp he).toO

/- English proof (translation)
The claim follows from `PI.TCS.Tr.inf (PI.TCS.Tr.sup (PI.TCS.Tr.inf hΛ ((PI.TCS.trE_Xsp he).perp hiso).toO) (PI.TCS.trE_Xsp he).toO) ((PI.TCS.trE_Xsp he).perp hiso).toO`.
-/
theorem transport_lattice_sub (Λ₂ Λ : Submodule (𝓞 E) S.V) (hΛ : PI.TCS.Tr γ Λ₂ Λ) (he : ∀ k, F₂.fl.e k = γ (x.fl.e k))
    (hiso : ∀ a b, S.hT (γ a) (γ b) = S.hT a b) : PI.TCS.Tr γ (Lsub Λ₂ F₂) (Lsub Λ x) :=
  PI.TCS.Tr.inf (PI.TCS.Tr.sup (PI.TCS.Tr.inf hΛ ((PI.TCS.trE_Xsp he).perp hiso).toO) (PI.TCS.trE_Xsp he).toO)
    ((PI.TCS.trE_Xsp he).perp hiso).toO

/- English proof (translation)
Use `⟨fun P => ?_, fun c hc => ?_⟩` and prove the remaining obligations. Take `⟨c, hc0, hc1, heq⟩` from `hx.1 P`. Use `⟨c, hc0, hc1, ?_⟩` and prove the remaining obligations. Use `P.isPrime` as an intermediate fact. Use `PI.TCS.Tr.eq (transport_x_lattice Λ₂ Λ hΛ he).localization₂ (PI.TCS.Tr.span ?_).localization₂ heq` and prove the remaining obligations.

Rewrite using `[← Set.range_comp]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using `[he a, map_smul]`. Apply `hx.2 c` to reduce the goal to its premises.

Use `((transport_lattice_sub Λ₂ Λ hΛ he hiso) _).mp hc` as an intermediate fact. Simplify `this` using `[hz, map_smul]`.
-/
theorem fixed_conv_transport (Λ₂ Λ : Submodule (𝓞 E) S.V) (g : ℕ) (hΛ : PI.TCS.Tr γ Λ₂ Λ)
    (he : ∀ k, F₂.fl.e k = γ (x.fl.e k)) (hz : F₂.fl.z = γ x.fl.z) (hiso : ∀ a b, S.hT (γ a) (γ b) = S.hT a b)
    (hx : IsFixedConv Λ g x) : IsFixedConv Λ₂ g F₂ := by
  refine ⟨fun P => ?_, fun c hc => ?_⟩
  · obtain ⟨c, hc0, hc1, heq⟩ := hx.1 P
    refine ⟨c, hc0, hc1, ?_⟩
    have := P.isPrime
    refine PI.TCS.Tr.eq (transport_x_lattice Λ₂ Λ hΛ he).localization₂ (PI.TCS.Tr.span ?_).localization₂ heq
    rw [← Set.range_comp]
    congr 1
    funext a
    simp [he a, map_smul]
  · apply hx.2 c
    have := ((transport_lattice_sub Λ₂ Λ hΛ he hiso) _).mp hc
    simpa [hz, map_smul] using this

end Tr2

section Main

variable {D : D7}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fixed_conv_transport Λ₂ Λ (gS D) hΛ he hz hiso hx.1, PI.TCS.Tr.eq (transport_x_lattice Λ₂ Λ hΛ he) (PI.TCS.tr_XS D he) hx.2⟩`.
-/
theorem frame_ok_transport {T' : D.host.E} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {x F₂ : LFlag (VS D) D.R.rS T'} (Λ₂ Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : PI.TCS.Tr γ Λ₂ Λ)
    (he : ∀ k, F₂.fl.e k = γ (x.fl.e k)) (hz : F₂.fl.z = γ x.fl.z)
    (hiso : ∀ a b, (VS D).hT (γ a) (γ b) = (VS D).hT a b) (hx : FrameOK D Λ x) : FrameOK D Λ₂ F₂ :=
  ⟨fixed_conv_transport Λ₂ Λ (gS D) hΛ he hz hiso hx.1, PI.TCS.Tr.eq (transport_x_lattice Λ₂ Λ hΛ he) (PI.TCS.tr_XS D he) hx.2⟩

/- English proof (translation)
Establish `hmap : mapLF σ F' = ⟨mapFlag σ hiso F'.fl, σ F'.zt⟩`. Unfold `mapLF`. Rewrite using `[dif_pos hiso]`. Establish `hisoT : ∀ a b, (VS D).hT (σ a) (σ b) = (VS D).hT a b` using `fun a b => hiso a b`. Establish `hfr : ∀ b, frame (mapLF σ F') b = σ (frame F' b)` using `Formalism.L2.SG.NormCut.frame_mapLF hiso F'`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hmap]`. Use `⟨(hTr _).mpr ?_, ?_⟩` and prove the remaining obligations. Use `show σ.symm (σ F'.fl.z) ∈ Λ'`. Simplify using `using hL.1`.

Use `show σ F'.zt = σ F'.fl.z`. Rewrite using `[hL.2]`. Take `⟨ξ, hl, hd, hc⟩` from `hA`. Use `⟨ξ, hl, hd, fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[hfr b]`.

Conclude with `hc b`. Rewrite using `[hmap]`. Conclude with `frame_ok_transport Λ Λ' hTr (fun j => rfl) rfl hisoT hOK`.
-/
theorem pd_of_tr {T : D.host.E} (u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hiso : σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hTr : PI.TCS.Tr σ Λ Λ')
    (hL : IsLift Λ' F') (hOK : FrameOK D Λ' F')
    (hA : ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E),
      (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧
      ∀ b, ModG (VS D) Λ (gS D) (σ (frame F' b) - frameAct (frame F) ξ b)) :
    TermDef.PD D Λ F u' (mapLF σ F') := by
  have hmap : mapLF σ F' = ⟨mapFlag σ hiso F'.fl, σ F'.zt⟩ := by
    unfold mapLF; rw [dif_pos hiso]
  have hisoT : ∀ a b, (VS D).hT (σ a) (σ b) = (VS D).hT a b := fun a b => hiso a b
  have hfr : ∀ b, frame (mapLF σ F') b = σ (frame F' b) := Formalism.L2.SG.NormCut.frame_mapLF hiso F'
  refine ⟨?_, ?_, ?_⟩
  · rw [hmap]
    refine ⟨(hTr _).mpr ?_, ?_⟩
    · show σ.symm (σ F'.fl.z) ∈ Λ'
      simpa using hL.1
    · show σ F'.zt = σ F'.fl.z
      rw [hL.2]
  · obtain ⟨ξ, hl, hd, hc⟩ := hA
    refine ⟨ξ, hl, hd, fun b => ?_⟩
    rw [hfr b]
    exact hc b
  · rw [hmap]
    exact frame_ok_transport Λ Λ' hTr (fun j => rfl) rfl hisoT hOK

/- English proof (translation)
Introduce `D X Y u u' hH ρ ρ' γ hγ`. Take `⟨hγr, hk⟩` from `hγ`. Take `⟨σ, hRL, hiso⟩` from `h1 D X γ hγr`. Establish `hK` using `Y.hK`. Use `set k := kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) γ with hkdef`.

Establish `hkK : k ∈ X.B.I.Kset` using `hk.1`. Establish `hkK' : k⁻¹ ∈ X.B.I.Kset` using `(hK.2.2.1 k hk).1`. Establish `hTr : PI.TCS.Tr σ ((Y.cs u).lamOf ρ) ((Y.cs u').lamOf ρ')`. Introduce `v`. Rewrite using `[(Y.cs u).lat_eq ρ v, (Y.cs u').lat_eq ρ' (σ.symm v), ← LatDictK.ratLink_incl_inv X hRL v, mulVec_mulVec, ← LatDictK.fmatK_mul]`.

Establish `e : (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * γ.2⁻¹ = k⁻¹ * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹`. Rewrite using `[hkdef]`. Unfold `kOf`. Use `group`. Rewrite using `[e, LatDictK.fmatK_mul, ← mulVec_mulVec]`.

Prove the components needed by the constructor for the conclusion. Introduce `hw`. Conclude with `unitaryCongruence.K_mv X.B.I hkK' hw`. Introduce `hw`. Use `unitaryCongruence.K_mv X.B.I hkK hw` as an intermediate fact.

Rewrite using `[mulVec_mulVec, ← LatDictK.fmatK_mul, mul_inv_cancel, show X.B.I.fmat 1 = 1 by` and apply the resulting hypothesis. Simplify using `[AutInst.fmat], one_mulVec] at this`. Establish `hgm : Formalism.HermitianLatticesTheory.gmap σ ((Y.cs u').lamOf ρ') = (Y.cs u).lamOf ρ`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `(hTr _).mpr (by simpa using hy)`. Introduce `hv`. Conclude with `⟨σ.symm v, (hTr v).mp hv, by simp⟩`. Take `⟨-, ⟨-, -, hLift, hFC⟩, hXL⟩` from `(Y.rowsOK u').1 _ ((Y.cs u').lam_mem ρ')`.

Use `⟨⟨(γ, σ), hRL, hiso, hgm, ?_⟩, rfl⟩` and prove the remaining obligations. Use `pd_of_tr u' _ _ (lf D (X.Fu u)) (lf D (X.Fu u')) σ hiso hTr hLift ⟨hFC, hXL⟩ ?_` and prove the remaining obligations. Take `⟨ξ, hl, hd, hc⟩` from `h3 D X Y u u' ρ ρ' γ σ hRL hk`. Conclude with `⟨ξ, hl, hd, fun b => h2 D X (aC (Y.cs u) ρ) _ ((Y.cs u).lat_eq ρ) _ (hc b)⟩`.
-/
theorem termCarC_of (h1 : RatIsoC) (h2 : ModGOfAtC) (h3 : FrameCongC) : TermCarC := by
  intro D X Y u u' hH ρ ρ' γ hγ
  obtain ⟨hγr, hk⟩ := hγ
  obtain ⟨σ, hRL, hiso⟩ := h1 D X γ hγr
  have hK := Y.hK
  set k := kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) γ with hkdef
  have hkK : k ∈ X.B.I.Kset := hk.1
  have hkK' : k⁻¹ ∈ X.B.I.Kset := (hK.2.2.1 k hk).1

  have hTr : PI.TCS.Tr σ ((Y.cs u).lamOf ρ) ((Y.cs u').lamOf ρ') := by
    intro v
    rw [(Y.cs u).lat_eq ρ v, (Y.cs u').lat_eq ρ' (σ.symm v), ← LatDictK.ratLink_incl_inv X hRL v,
      mulVec_mulVec, ← LatDictK.fmatK_mul]
    have e : (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * γ.2⁻¹ =
        k⁻¹ * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ := by
      rw [hkdef]; unfold kOf; group
    rw [e, LatDictK.fmatK_mul, ← mulVec_mulVec]
    constructor
    · intro hw
      exact unitaryCongruence.K_mv X.B.I hkK' hw
    · intro hw
      have := unitaryCongruence.K_mv X.B.I hkK hw
      rwa [mulVec_mulVec, ← LatDictK.fmatK_mul, mul_inv_cancel, show X.B.I.fmat 1 = 1 by
        simp [AutInst.fmat], one_mulVec] at this
  have hgm : Formalism.HermitianLatticesTheory.gmap σ ((Y.cs u').lamOf ρ') = (Y.cs u).lamOf ρ := by
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hTr _).mpr (by simpa using hy)
    · intro hv
      exact ⟨σ.symm v, (hTr v).mp hv, by simp⟩

  obtain ⟨-, ⟨-, -, hLift, hFC⟩, hXL⟩ := (Y.rowsOK u').1 _ ((Y.cs u').lam_mem ρ')
  refine ⟨⟨(γ, σ), hRL, hiso, hgm, ?_⟩, rfl⟩
  refine pd_of_tr u' _ _ (lf D (X.Fu u)) (lf D (X.Fu u')) σ hiso hTr hLift ⟨hFC, hXL⟩ ?_
  obtain ⟨ξ, hl, hd, hc⟩ := h3 D X Y u u' ρ ρ' γ σ hRL hk
  exact ⟨ξ, hl, hd, fun b => h2 D X (aC (Y.cs u) ρ) _ ((Y.cs u).lat_eq ρ) _ (hc b)⟩

end Main

end TermCarSec

end Formalism.L2.SG.Pf.RegroupPf
