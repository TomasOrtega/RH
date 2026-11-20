import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicLinearIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCuspFormsFullLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CnormMapConjMulVec
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.GoodWCore

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hl`.
-/
theorem fullLat_congr {K Rg : Type} [Field K] [NumberField K] [CommRing Rg] [Algebra K Rg] [Algebra (𝓞 K) Rg]
    [IsScalarTower (𝓞 K) K Rg] {C C' : Submodule K Rg} (h : C = C')
    {Vs : HeightOneSpectrum (𝓞 K) → Set (Rg → EReal)} {hV : ∀ la, ∀ v ∈ Vs la, IsVal la v}
    (hl : FullLat C Vs hV) : FullLat C' Vs hV := by
  subst h
  exact hl

set_option maxHeartbeats 8000000 in

/- English proof (translation)
Establish `hl' : FullLat (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ (wtA w) w.n)) (valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c)) fun la => isVal_valSet la` using `fullLat_congr (cuspW_wtZ _ _).symm hl`. Use `⟨?_, hl'.fg, hl'.span_eq_top⟩` and prove the remaining obligations. Use `haveI : FiniteDimensional T.Q.c.F (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ (wtA w) w.n)) := by`. Take `⟨s, hs⟩` from `hl'.fg`. Use `⟨⟨s, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[← hl'.span_eq_top, ← hs, Submodule.span_span_of_tower]`. Use `GlobalTheory.HSApp.hasGram_of_inner _ _ _ fun v => ?_` and prove the remaining obligations. Use `set σ := goodOf T.Q.c v.embedding with hσdef`. Establish `hσ : GoodEmb T.Q.c σ` using `goodEmb_goodOf _ _`. Establish `hD : Dom (wtA w) w.n` using `dom_wtA w`.

Set `ι` to `LinearEquiv.ofEq _ _ (cuspW_wtZ (Xo := T.Q.Xo j) (c := T.Q.c) (U := T.U j) (wtA w) w.n)`. Set `cf : ℝ` to `lieFac (T.Q.Dw j) (xiR D) (wtA w)`. Establish `hcf : 0 < cf` using `lieFac_pos _ _ _`. Set `J` to `uniformisationL2 (T.V j σ) σ (rdC (T.U j) σ (wtA w) w.n) (T.dict j σ) (T.mu j σ) (hT.cuspidalL2Subspace j hj σ hσ (wtA w) w.n hD)`. Set `Φ : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ (wtA w) w.n) →+ MeasureTheory.Lp ℂ 2 (muQ1 (T.V j σ))` to `AddMonoidHom.mk' (fun f => (cf : ℂ) • J (ι f)) (fun f g => by rw [map_add, map_add, smul_add])`.

Establish `hΦ : ∀ f, Φ f = (cf : ℂ) • J (ι f)` using `fun _ => rfl`. Establish `hs : ∀ (a : T.Q.c.F) f, Φ (a • f) = σ a • Φ f` using `fun a f => by`. Rewrite using `[hΦ, hΦ, map_smul, map_smulₛₗ]`. Conclude with `smul_comm _ _ _`. Use `⟨_, inferInstance, inferInstance, Φ, ?_, ?_, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hg : GoodEmb T.Q.c v.embedding`. Use `left`. Introduce `a f`. Establish `e' : σ a = v.embedding a`. Rewrite using `[hσdef]`.

Unfold `goodOf`. Rewrite using `[if_pos hg]`. Rewrite using `[hs, e']`. Use `right`. Introduce `a f`.

Establish `e' : σ a = starRingEnd ℂ (v.embedding a)`. Rewrite using `[hσdef]`. Unfold `goodOf`. Rewrite using `[if_neg hg]`. Both sides reduce to the same expression.

Rewrite using `[hs, e']`. Introduce `f`. Establish `hf : (f : Rul (T.Q.Xo j) T.Q.c) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n` using `(ι f).2`. Establish `e1 : normW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ (wtA w) w.n) v.embedding f = petAt (T.U j σ) (xiR D) (T.V j σ) (T.dict j σ) (muQ1 (T.V j σ)) (wtZ (wtA w) w.n) f` using `rfl`. Rewrite using `[e1, petAt_wtZ (T.U j) (xiR D) (T.V j σ) (T.dict j σ) (T.mu j σ) (hT.muUnit j hj σ hσ) _ _ (hT.cuspidalL2Subspace j hj σ hσ (wtA w) w.n hD) hf, l2C, dif_pos hf, hΦ, norm_smul, Complex.norm_real, Real.norm_of_nonneg hcf.le]`.

Both sides reduce to the same expression. Introduce `m e he`. Establish `hi : LinearIndependent T.Q.c.F fun k => ι (e k)` using `he.map' ι.toLinearMap ι.ker`. Establish `h1` using `(GlobalTheory.VolPairExists.adelic_linearIndependent D T hT j hj σ hσ (wtA w) w.n hD).2 m _ hi`. Rewrite `h1`, the goal using `[Fintype.linearIndependent_iff]`.

Introduce `c hc`. Use `h1 c ?_` and prove the remaining obligations. Establish `: (cf : ℂ) • ∑ k, c k • J (ι (e k)) = 0`. Rewrite using `[Finset.smul_sum]`. Use `Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hc` and prove the remaining obligations.

Rewrite using `[hΦ]`. Conclude with `smul_comm _ _ _`. Conclude with `(smul_eq_zero.1 this).resolve_left (Complex.ofReal_ne_zero.2 hcf.ne')`.
-/
theorem goodW_core {D : D7} (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j)
    (hl : FullLat (T.cuspA j (wtA w) w.n) (valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c))
      fun la => isVal_valSet la) :
    GoodW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ (wtA w) w.n) := by
  have hl' : FullLat (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ (wtA w) w.n))
      (valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c)) fun la => isVal_valSet la :=
    fullLat_congr (cuspW_wtZ _ _).symm hl
  refine ⟨?_, hl'.fg, hl'.span_eq_top⟩
  haveI : FiniteDimensional T.Q.c.F (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ (wtA w) w.n)) := by
    obtain ⟨s, hs⟩ := hl'.fg
    refine ⟨⟨s, ?_⟩⟩
    rw [← hl'.span_eq_top, ← hs, Submodule.span_span_of_tower]
  refine GlobalTheory.HSApp.hasGram_of_inner _ _ _ fun v => ?_
  set σ := goodOf T.Q.c v.embedding with hσdef
  have hσ : GoodEmb T.Q.c σ := goodEmb_goodOf _ _
  have hD : Dom (wtA w) w.n := dom_wtA w
  let ι := LinearEquiv.ofEq _ _ (cuspW_wtZ (Xo := T.Q.Xo j) (c := T.Q.c) (U := T.U j) (wtA w) w.n)
  let cf : ℝ := lieFac (T.Q.Dw j) (xiR D) (wtA w)
  have hcf : 0 < cf := lieFac_pos _ _ _
  let J := uniformisationL2 (T.V j σ) σ (rdC (T.U j) σ (wtA w) w.n) (T.dict j σ) (T.mu j σ)
    (hT.cuspidalL2Subspace j hj σ hσ (wtA w) w.n hD)
  let Φ : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ (wtA w) w.n) →+ MeasureTheory.Lp ℂ 2 (muQ1 (T.V j σ)) :=
    AddMonoidHom.mk' (fun f => (cf : ℂ) • J (ι f)) (fun f g => by rw [map_add, map_add, smul_add])
  have hΦ : ∀ f, Φ f = (cf : ℂ) • J (ι f) := fun _ => rfl
  have hs : ∀ (a : T.Q.c.F) f, Φ (a • f) = σ a • Φ f := fun a f => by
    rw [hΦ, hΦ, map_smul, map_smulₛₗ]
    exact smul_comm _ _ _
  refine ⟨_, inferInstance, inferInstance, Φ, ?_, ?_, ?_⟩
  · by_cases hg : GoodEmb T.Q.c v.embedding
    · left
      intro a f
      have e' : σ a = v.embedding a := by
        rw [hσdef]; unfold goodOf; rw [if_pos hg]
      rw [hs, e']
    · right
      intro a f
      have e' : σ a = starRingEnd ℂ (v.embedding a) := by
        rw [hσdef]; unfold goodOf; rw [if_neg hg]; rfl
      rw [hs, e']
  · intro f
    have hf : (f : Rul (T.Q.Xo j) T.Q.c) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := (ι f).2
    have e1 : normW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ (wtA w) w.n) v.embedding f =
        petAt (T.U j σ) (xiR D) (T.V j σ) (T.dict j σ) (muQ1 (T.V j σ)) (wtZ (wtA w) w.n) f := rfl
    rw [e1, petAt_wtZ (T.U j) (xiR D) (T.V j σ) (T.dict j σ) (T.mu j σ) (hT.muUnit j hj σ hσ) _ _
      (hT.cuspidalL2Subspace j hj σ hσ (wtA w) w.n hD) hf, l2C, dif_pos hf, hΦ, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hcf.le]
    rfl
  · intro m e he
    have hi : LinearIndependent T.Q.c.F fun k => ι (e k) := he.map' ι.toLinearMap ι.ker
    have h1 := (GlobalTheory.VolPairExists.adelic_linearIndependent D T hT j hj σ hσ (wtA w) w.n hD).2 m _ hi
    rw [Fintype.linearIndependent_iff] at h1 ⊢
    intro c hc
    refine h1 c ?_
    have : (cf : ℂ) • ∑ k, c k • J (ι (e k)) = 0 := by
      rw [Finset.smul_sum]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hc
      rw [hΦ]
      exact smul_comm _ _ _
    exact (smul_eq_zero.1 this).resolve_left (Complex.ofReal_ne_zero.2 hcf.ne')

end GlobalTheory.CovTop.GoodWCore

namespace GlobalTheory.CovTop

/- English proof (translation)
Introduce `p _ _ i` and use `GoodWCore.goodW_core p.T p.fw.laws _ ⟨Nat.le_add_left _ _, i.2⟩ (p.κ i) (GlobalTheory.GoodLat.Obj.latFull p.T p.fw.laws p.fw.kap i)`.
-/
theorem goodW_at : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz),
    p.Rows → RecTied D L → ∀ i : Fin D.R.m,
      GoodW (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i) :=
  fun p _ _ i => GoodWCore.goodW_core p.T p.fw.laws _ ⟨Nat.le_add_left _ _, i.2⟩ (p.κ i)
    (GlobalTheory.GoodLat.Obj.latFull p.T p.fw.laws p.fw.kap i)

end GlobalTheory.CovTop
