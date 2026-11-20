import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalResolutionOpenStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hctx w hw`. Establish `hT` using `GlobalTheory.T.frameData_local_resolution_open K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hctx w hw`. Establish `hc2` using `hctx`. Unfold `GlobalTheory.CompanionTheory.Ar.PB.PFl.IsPCtx at hc2`. Take `⟨-, -, hframe, hchart, -⟩` from `hc2`.

Unfold `GlobalTheory.CompanionTheory.Ar.PB.WMan.IsBaseChart at hchart`. Establish `hwV : pB ε w ∈ V` using `hw`. Take `⟨hmem, hnorm, hgood, -⟩` from `hchart.2.2.2.2 (pB ε w) hwV`. Establish `hbase : basePart M.blk (GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w)) = bl (pB ε w)`. Use function extensionality and compare the values at `q`.

Take `⟨⟨k, hk⟩, m⟩` from `q`. Unfold `GlobalTheory.CompanionTheory.Ar.PB.basePart GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ`. Use `split`. Use `next hex => exact absurd hex (fun ⟨p, hp⟩ => hk p hp)`. Use `next hex => rfl`.

Use `⟨GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w), ?_, rfl, hbase⟩` and prove the remaining obligations. Establish `hmain` using `(GlobalTheory.CompanionTheory.Ar.PB.CPts.main K ι Φ y Ψ N j M).2.2 F hframe (GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w)) (by rw [hbase]; exact hmem) (by rw [hbase]; exact hgood) (by rw [hbase]; exact hnorm)`. Use `hmain.2 ⟨fun τ => pH keep h ε τ w, ?_⟩` and prove the remaining obligations. Use `⟨fun k => by rw [hbase]; exact hnorm k, fun τ => hT.1 τ, ?_⟩` and prove the remaining obligations. Introduce `p k hp`.

Use `⟨1, one_ne_zero, fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[one_mul, hbase]`. Unfold `GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ`. Use `split`. Use `next hex =>`.

Establish `hc : hex.choose = p` using `M.blk_inj _ _ k hex.choose_spec hp`. Rewrite using `[hc]`. Use `next hex => exact absurd ⟨p, hp⟩ hex`.
-/
theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ w ∈ pD ε V, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = pPhi M F keep v bl h ε w ∧ basePart M.blk z = bl (pB ε w) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hctx w hw
  have hT := GlobalTheory.T.frameData_local_resolution_open K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hctx w hw
  have hc2 := hctx
  unfold GlobalTheory.CompanionTheory.Ar.PB.PFl.IsPCtx at hc2
  obtain ⟨-, -, hframe, hchart, -⟩ := hc2
  unfold GlobalTheory.CompanionTheory.Ar.PB.WMan.IsBaseChart at hchart
  have hwV : pB ε w ∈ V := hw
  obtain ⟨hmem, hnorm, hgood, -⟩ := hchart.2.2.2.2 (pB ε w) hwV
  have hbase : basePart M.blk (GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w)) =
      bl (pB ε w) := by
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    unfold GlobalTheory.CompanionTheory.Ar.PB.basePart GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ
    split
    next hex => exact absurd hex (fun ⟨p, hp⟩ => hk p hp)
    next hex => rfl
  refine ⟨GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w), ?_, rfl, hbase⟩
  have hmain := (GlobalTheory.CompanionTheory.Ar.PB.CPts.main K ι Φ y Ψ N j M).2.2 F hframe
    (GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w))
    (by rw [hbase]; exact hmem) (by rw [hbase]; exact hgood) (by rw [hbase]; exact hnorm)
  refine hmain.2 ⟨fun τ => pH keep h ε τ w, ?_⟩
  refine ⟨fun k => by rw [hbase]; exact hnorm k, fun τ => hT.1 τ, ?_⟩
  intro p k hp
  refine ⟨1, one_ne_zero, fun m => ?_⟩
  rw [one_mul, hbase]
  unfold GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ
  split
  next hex =>
    have hc : hex.choose = p := M.blk_inj _ _ k hex.choose_spec hp
    rw [hc]
  next hex => exact absurd ⟨p, hp⟩ hex

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext
