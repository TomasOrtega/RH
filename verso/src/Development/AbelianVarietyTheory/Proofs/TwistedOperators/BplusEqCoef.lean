import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRational
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

/- English proof (translation)
Simplify using `only [Bplus, besInt, GlobalTheory.Mem.TrueRecord.coef, ← integral_const_mul, mul_assoc]`.
-/
theorem bplus_eq_coef {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)
    (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)) :
    Bplus W M φ F = ∫ h in M.fd (.top 0), φ h *
      GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M.νN M.fdN F (embTop G h) ∂M.ν (.top 0) := by
  simp only [Bplus, besInt, GlobalTheory.Mem.TrueRecord.coef, ← integral_const_mul, mul_assoc]

/- English proof (translation)
Take `⟨i1, i2, i3, i4, i5, -, -⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))`. Establish `h1` using `hM.top`. Establish `h2` using `hM'.top`. Unfold `Vol.IsAt at h1 h2`. Establish `hz : Node.neg D.R.m (Node.top 0) = 0` using `rfl`.

Rewrite `h1`, `h2` using `[if_pos hz]`. Use `haveI := h1.1.1`. Use `haveI := h2.1.1`. Establish `e` using `Measure.isMulLeftInvariant_eq_smul (M.ν (.top 0)) (M'.ν (.top 0))`. Establish `a1` using `GlobalTheory.Mass.Levels.measure_comap_finE h1.1`.

Establish `a2` using `GlobalTheory.Mass.Levels.measure_comap_finE h2.1`. Establish `hc : Measure.haarScalarFactor (M.ν (.top 0)) (M'.ν (.top 0)) = 1`. Rewrite `a1` using `[e, Measure.smul_apply, a2]`. Simplify using `using a1`. Rewrite using `[e, hc, one_smul]`.
-/
theorem nu_top_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {M M' : Vol G}
    (hM : M.IsRow) (hM' : M'.IsRow) : M.ν (.top 0) = M'.ν (.top 0) := by
  obtain ⟨i1, i2, i3, i4, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  have h1 := hM.top
  have h2 := hM'.top
  unfold Vol.IsAt at h1 h2
  have hz : Node.neg D.R.m (Node.top 0) = 0 := rfl
  rw [if_pos hz] at h1 h2
  haveI := h1.1.1
  haveI := h2.1.1
  have e := Measure.isMulLeftInvariant_eq_smul (M.ν (.top 0)) (M'.ν (.top 0))
  have a1 := GlobalTheory.Mass.Levels.measure_comap_finE h1.1
  have a2 := GlobalTheory.Mass.Levels.measure_comap_finE h2.1
  have hc : Measure.haarScalarFactor (M.ν (.top 0)) (M'.ν (.top 0)) = 1 := by
    rw [e, Measure.smul_apply, a2] at a1
    simpa using a1
  rw [e, hc, one_smul]

/- English proof (translation)
Introduce `D T L sc G W M M' hM hM' φ F hφ hF`. Establish `hψ` using `W.ψ_std`. Establish `hι` using `(G.rowDec 0 (by have := D.R.two_le_m; omega)).isom`. Establish `hF' : ∀ γ ∈ GQ (G.V (.grid D.R.m 0)), ∀ g, F (γ * g) = F g` using `hF.1`. Establish `hN` using `hM.unip`.

Establish `hN'` using `hM'.unip`. Rewrite using `[bplus_eq_coef, bplus_eq_coef]`. Establish `ec : ∀ g, GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M.νN M.fdN F g = GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M'.νN M'.fdN F g` using `fun g => GlobalTheory.Mem.TrueRecord.coef_eq hψ hι G.besTop hN.1 hN.2.1 hN.2.2 hN'.1 hN'.2.1 hN'.2.2 hF' g`. Simplify using `only [ec]`. Take `⟨i1, i2, i3, i4, i5, -, i7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))`.

Establish `hf1` using `(hM.top.haar_fund).2`. Establish `hf2` using `hM'.top.haar_fund`. Rewrite `hf1`, the goal using `[nu_top_eq hM hM']`. Use `haveI := hf2.1`. Use `set d := G.rowDec 0 (by have := D.R.two_le_m; omega)`.

Establish `e0 : ∀ h, embTop G h = stabilizerEmbedding d h` using `fun h => rfl`. Establish `e1 : stabilizerEmbedding d 1 = 1`. Use `GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d 1 1` as an intermediate fact. Rewrite `this` using `[one_mul]`. Conclude with `left_eq_mul.mp this`.

Use `hf1.setIntegral_eq hf2.2 fun γ h => ?_` and prove the remaining obligations. Establish `hγ : (γ : GA D (G.V (.top 0))) ∈ GQ (G.V (.top 0))` using `γ.2`. Establish `hinv : stabilizerEmbedding d (γ : GA D (G.V (.top 0)))⁻¹ = (stabilizerEmbedding d γ)⁻¹`. Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Rewrite using `[← GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul, inv_mul_cancel, e1]`.

Establish `r1 : EmbRel _ _ d.ι (stabilizerEmbedding d γ) γ` using `(embRel_iff d _ _).2 rfl`. Establish `r2 : EmbRel _ _ d.ι (stabilizerEmbedding d γ)⁻¹ (γ : GA D (G.V (.top 0)))⁻¹` using `hinv ▸ (embRel_iff d _ _).2 rfl`. Express the relevant statement in the definitionally equal form `φ ((γ : GA D (G.V (.top 0))) * h) * GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M'.νN M'.fdN F (embTop G ((γ : GA D (G.V (.top 0))) * h)) = _`. Rewrite using `[hφ.1 _ hγ, e0, e0, GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul, GlobalTheory.Mem.TrueRecord.coef_left hψ hι G.besTop hN'.1 hN'.2.1 hN'.2.2 hF' (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational d _ hγ) r1 r2]`.
-/
theorem bplus_indep : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (W : G.Weil) (M M' : Vol G),
    M.IsRow → M'.IsRow → ∀ φ F, GlobalTheory.Unf.IsContAut _ φ → GlobalTheory.Unf.IsContAut _ F → Bplus W M φ F = Bplus W M' φ F := by
  intro D T L sc G W M M' hM hM' φ F hφ hF
  have hψ := W.ψ_std
  have hι := (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have hF' : ∀ γ ∈ GQ (G.V (.grid D.R.m 0)), ∀ g, F (γ * g) = F g := hF.1
  have hN := hM.unip
  have hN' := hM'.unip
  rw [bplus_eq_coef, bplus_eq_coef]
  have ec : ∀ g, GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M.νN M.fdN F g =
      GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M'.νN M'.fdN F g := fun g =>
    GlobalTheory.Mem.TrueRecord.coef_eq hψ hι G.besTop hN.1 hN.2.1 hN.2.2 hN'.1 hN'.2.1 hN'.2.2 hF' g
  simp only [ec]
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  have hf1 := (hM.top.haar_fund).2
  have hf2 := hM'.top.haar_fund
  rw [nu_top_eq hM hM'] at hf1 ⊢
  haveI := hf2.1
  set d := G.rowDec 0 (by have := D.R.two_le_m; omega)
  have e0 : ∀ h, embTop G h = stabilizerEmbedding d h := fun h => rfl
  have e1 : stabilizerEmbedding d 1 = 1 := by
    have := GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d 1 1
    rw [one_mul] at this
    exact left_eq_mul.mp this
  refine hf1.setIntegral_eq hf2.2 fun γ h => ?_
  have hγ : (γ : GA D (G.V (.top 0))) ∈ GQ (G.V (.top 0)) := γ.2
  have hinv : stabilizerEmbedding d (γ : GA D (G.V (.top 0)))⁻¹ = (stabilizerEmbedding d γ)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul, inv_mul_cancel, e1]
  have r1 : EmbRel _ _ d.ι (stabilizerEmbedding d γ) γ := (embRel_iff d _ _).2 rfl
  have r2 : EmbRel _ _ d.ι (stabilizerEmbedding d γ)⁻¹ (γ : GA D (G.V (.top 0)))⁻¹ := hinv ▸ (embRel_iff d _ _).2 rfl
  change φ ((γ : GA D (G.V (.top 0))) * h) *
      GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M'.νN M'.fdN F (embTop G ((γ : GA D (G.V (.top 0))) * h)) = _
  rw [hφ.1 _ hγ, e0, e0, GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul,
    GlobalTheory.Mem.TrueRecord.coef_left hψ hι G.besTop hN'.1 hN'.2.1 hN'.2.2 hF' (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational d _ hγ) r1 r2]

end GlobalTheory.RowVal
