import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions

set_option synthInstance.maxHeartbeats 400000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.CovTop.MeasRd

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

/- English proof (translation)
Establish `hc : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ` using `RingHom.ext fun a => ComplexEmbedding.conjugate_coe_eq σ a`. Unfold `sgAt`. Use `split_ifs with h`. Break down `InfinitePlace.mk_eq_iff.1 h with h1 | h1` into its components or cases. Conclude with `Or.inl h1.symm`.

Use `right`. Rewrite using `[← h1, hc]`. Break down `InfinitePlace.embedding_mk_eq σ with h1 | h1` into its components or cases. Conclude with `Or.inl h1`. Use `right`.

Rewrite using `[h1, hc]`.
-/
theorem sgAt_mk_eq {K : Type} [Field K] (σ₀ σ : K →+* ℂ) :
    sgAt σ₀ (InfinitePlace.mk σ) = σ ∨ sgAt σ₀ (InfinitePlace.mk σ) = (starRingEnd ℂ).comp σ := by
  have hc : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
    RingHom.ext fun a => ComplexEmbedding.conjugate_coe_eq σ a
  unfold sgAt
  split_ifs with h
  · rcases InfinitePlace.mk_eq_iff.1 h with h1 | h1
    · exact Or.inl h1.symm
    · right; rw [← h1, hc]
  · rcases InfinitePlace.embedding_mk_eq σ with h1 | h1
    · exact Or.inl h1
    · right; rw [h1, hc]

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem phiC_congr {T : CoreJ D} {j : ℕ} {σ₁ σ₂ : T.Q.c.F →+* ℂ} (e : σ₁ = σ₂) {W : Formalism.BasicNotions.TH.HSp D}
    (h₁ : T.V j σ₁ = W) (h₂ : T.V j σ₂ = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC T h₁ a f = phiC T h₂ a f := by
  subst e; rfl

end GlobalTheory.CovTop.MeasRd

namespace GlobalTheory.CovTop.MeasRd

open GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes in

/- English proof (translation)
Introduce `σ f`. Establish `hTau : Nonempty D.what₂.Tau` using `⟨D.eTau.symm 1⟩`. Establish `hk : p.κ = kapTop D` using `KapIs.eq (κ := p.κ) p.fw.kap hTau`. Establish `ha : wtA (p.κ i) = wtA (kapTop D i)` using `by rw [hk]`. Establish `hn : (p.κ i).n = (kapTop D i).n` using `by rw [hk]`.

Establish `hG : Gk p i = GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i` using `by unfold Gk GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW; rw [hk]`. Take `⟨-, hd, h2⟩` from `hM _ p.R.toRealDat.toLevCh _ p.charW.base.lev i p.R.toRealDat.triv`. Establish `hmod` using `p.charW.base.models`. Take `⟨h0, ht, he, -⟩` from `h2 _ _ (hmod.νW i)`. Take `⟨s, hs_def⟩ : ∃ s, s = sgAt D.what₂.embLL (InfinitePlace.mk σ)` from `⟨_, rfl⟩`.

Establish `hs` using `sgAt_mk_eq D.what₂.embLL σ`. Rewrite `hs` using `[← hs_def]`. Use `show ‖(p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) _‖ = _`. Rewrite using `[← hs_def]`. Establish `hgd : goodOf p.T.Q.c (res p.T s) = goodOf p.T.Q.c (res p.T σ)`.

Break down `hs with h | h` into its components or cases. Rewrite using `[h]`. Rewrite using `[h]`. Conclude with `GlobalTheory.CompHt.goodOf_conj (c := p.T.Q.c) (res p.T σ)`. Establish `hgood` using `goodEmb_goodOf p.T.Q.c (res p.T s)`.

Establish `hV : p.T.V ((i : ℕ) + 1) (gd p.T s) = Wc D i` using `p.fw.laws.spaceW _ (inR i) _ hgood`. Take `⟨-, hrange, hip⟩` from `hmod.HW i s`. Distinguish the cases in `hf0 : f = 0`. Substitute `hf0` using the available equality. Establish `hy : ((p.fw.e i 0 : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL) = 0`.

Rewrite using `[map_zero]`. Both sides reduce to the same expression. Establish `hz` using `petW_smul (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i) (σ.comp (algebraMap p.T.Q.c.F D.what₂.LL)) 0 0`. Rewrite `hz` using `[map_zero, norm_zero, zero_mul, zero_smul]`. Rewrite using `[hy, map_zero, norm_zero, ZeroMemClass.coe_zero, hz, mul_zero]`.

Use `set y : Fin (p.R.toRealDat.nW i) → D.what₂.LL := ((p.fw.e i f : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL) with hy`. Establish `hy0 : y ≠ 0` using `fun h => hf0 ((p.fw.e i).map_eq_zero_iff.1 (Subtype.ext h))`. Use `set x := (p.R.toRealDat.FW i).j s y with hx_def`. Establish `hx : (p.R.toRealDat.HW i s).e x ∈ p.R.toRealDat.Wall i s` using `hrange ▸ LinearMap.mem_range_self _ x`. Use `set f' := rdU (p.T.U ((i : ℕ) + 1) (gd p.T s)) (f : p.T.R ((i : ℕ) + 1)) with hf'_def`.

Establish `hf' : f' ∈ scalarForms p.T i (gd p.T s)`. Use `((mem_cusp _ _ _ _ _ _).1 f.2).2 _ hgood` as an intermediate fact. Use `show f' ∈ holSub _ (modelWt _ (wtZ (wtA (kapTop D i)) (kapTop D i).n))`. Rewrite using `[modelWt_wtZ, ← ha, ← hn]`. Conclude with `this`.

Establish `hc : Corr p.T i s hV ((p.R.toRealDat.HW i s).e x) f'`. Distinguish the cases in `hgs : GoodEmb p.T.Q.c (res p.T s)`. Establish `hgd' : gd p.T s = res p.T s` using `by show goodOf _ _ = _; rw [goodOf, if_pos hgs]`. Establish `hV' : p.T.V ((i : ℕ) + 1) (res p.T s) = Wc D i` using `p.fw.laws.spaceW _ (inR i) _ hgs`. Establish `hpre : ∃ j' : (Fin (p.R.toRealDat.nW i) → D.what₂.LL) →ₛₗ[s] (p.R.toRealDat.HW i s).H, ∀ g : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n, ((p.R.toRealDat.HW i s).e (j' ((p.fw.e i g : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL))) (p.v₀ i s) = hV' ▸ p.T.ph …`.

Assume the negation of the conclusion as `hne`. Establish `hj0` using `p.fw.ev0 i s hgs hV' hne`. Establish `hli` using `(hp.prim.unif i s).1 1 (fun _ => y) (linearIndependent_unique_iff.2 hy0)`. Rewrite `hli` using `[hj0]`. Conclude with `hli.ne_zero 0 (LinearMap.zero_apply _)`.

Use `Or.inl ⟨hgs, p.v₀ i s, (p.fw.hv₀ i s).1, ?_⟩` and prove the remaining obligations. Rewrite using `[hf'_def, adFun_rdU]`. Use `(p.fw.ev i s hgs hV' hpre f).trans ?_` and prove the remaining obligations. Use `show phiC p.T hV' (wtA (p.κ i)) _ = _`. Generalize the expression as in `(f : p.T.R ((i : ℕ) + 1)) = F0`.

Rewrite using `[ha]`. Conclude with `phiC_congr hgd'.symm _ _ _ _`. Establish `hgd' : gd p.T s = resC p.T s` using `by show goodOf _ _ = _; rw [goodOf, if_neg hgs]`. Establish `hVc : p.T.V ((i : ℕ) + 1) (resC p.T s) = Wc D i` using `p.fw.laws.spaceW _ (inR i) _ (good_resC p.T hgs)`. Take `⟨v, hv, hvf⟩` from `(p.bar i s hgs hVc).1 (hp.jEvBar i s hgs hVc)`.

Use `Or.inr ⟨hgs, v, hv, ?_⟩` and prove the remaining obligations. Rewrite using `[hf'_def, adFun_rdU]`. Use `(hvf f).trans (funext fun g => ?_)` and prove the remaining obligations. Use `show starRingEnd ℂ (phiC p.T hVc (wtA (p.κ i)) _ g) = _`. Generalize the expression as in `(f : p.T.R ((i : ℕ) + 1)) = F0`.

Rewrite using `[ha, phiC_congr hgd' hV hVc]`. Establish `e` using `(he p.T p.fw.laws p.fw.alg_eq p.R.toRealDat.θ hmod.inf s (p.R.toRealDat.MW i s) hV _ hx f' hf' hc).2`. Rewrite `e` using `[← hip, inner_self_eq_norm_sq_to_K]`. Establish `e' : ‖x‖ ^ 2 = ratio D i (p.R.toRealDat.νW i) (p.R.toRealDat.fdW i) * probSq p.T i (gd p.T s) f'`. Establish `: (((‖x‖ ^ 2 : ℝ)) : ℂ) = _` using `(Complex.ofReal_pow _ _).trans e`.

Conclude with `this` after adjusting the coercions. Rewrite `e'` using `[hf'_def, probSq_rdU]`. Unfold `petW`. Rewrite using `[← hgd, hG, ← Real.sqrt_sq (norm_nonneg x), e', Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (petAt_nonneg _ _ _ _ _ _ _)]`. Both sides reduce to the same expression.
-/
theorem exactAt_of_rows {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (hp : p.Rows) (hM : OneMeasure D) (i : Fin D.R.m) : ExactAt p i := by
  intro σ f
  have hTau : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hk : p.κ = kapTop D := KapIs.eq (κ := p.κ) p.fw.kap hTau
  have ha : wtA (p.κ i) = wtA (kapTop D i) := by rw [hk]
  have hn : (p.κ i).n = (kapTop D i).n := by rw [hk]
  have hG : Gk p i = GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i := by unfold Gk GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW; rw [hk]
  obtain ⟨-, hd, h2⟩ := hM _ p.R.toRealDat.toLevCh _ p.charW.base.lev i p.R.toRealDat.triv
  have hmod := p.charW.base.models
  obtain ⟨h0, ht, he, -⟩ := h2 _ _ (hmod.νW i)
  obtain ⟨s, hs_def⟩ : ∃ s, s = sgAt D.what₂.embLL (InfinitePlace.mk σ) := ⟨_, rfl⟩
  have hs := sgAt_mk_eq D.what₂.embLL σ
  rw [← hs_def] at hs
  show ‖(p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) _‖ = _
  rw [← hs_def]

  have hgd : goodOf p.T.Q.c (res p.T s) = goodOf p.T.Q.c (res p.T σ) := by
    rcases hs with h | h
    · rw [h]
    · rw [h]; exact GlobalTheory.CompHt.goodOf_conj (c := p.T.Q.c) (res p.T σ)
  have hgood := goodEmb_goodOf p.T.Q.c (res p.T s)
  have hV : p.T.V ((i : ℕ) + 1) (gd p.T s) = Wc D i := p.fw.laws.spaceW _ (inR i) _ hgood
  obtain ⟨-, hrange, hip⟩ := hmod.HW i s
  by_cases hf0 : f = 0
  · subst hf0
    have hy : ((p.fw.e i 0 : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL) = 0 := by
      rw [map_zero]; rfl
    have hz := petW_smul (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i)
      (σ.comp (algebraMap p.T.Q.c.F D.what₂.LL)) 0 0
    rw [map_zero, norm_zero, zero_mul, zero_smul] at hz
    rw [hy, map_zero, norm_zero, ZeroMemClass.coe_zero, hz, mul_zero]
  set y : Fin (p.R.toRealDat.nW i) → D.what₂.LL := ((p.fw.e i f : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL)
    with hy
  have hy0 : y ≠ 0 := fun h => hf0 ((p.fw.e i).map_eq_zero_iff.1 (Subtype.ext h))
  set x := (p.R.toRealDat.FW i).j s y with hx_def
  have hx : (p.R.toRealDat.HW i s).e x ∈ p.R.toRealDat.Wall i s := hrange ▸ LinearMap.mem_range_self _ x
  set f' := rdU (p.T.U ((i : ℕ) + 1) (gd p.T s)) (f : p.T.R ((i : ℕ) + 1)) with hf'_def
  have hf' : f' ∈ scalarForms p.T i (gd p.T s) := by
    have := ((mem_cusp _ _ _ _ _ _).1 f.2).2 _ hgood
    show f' ∈ holSub _ (modelWt _ (wtZ (wtA (kapTop D i)) (kapTop D i).n))
    rw [modelWt_wtZ, ← ha, ← hn]
    exact this
  have hc : Corr p.T i s hV ((p.R.toRealDat.HW i s).e x) f' := by
    by_cases hgs : GoodEmb p.T.Q.c (res p.T s)
    · have hgd' : gd p.T s = res p.T s := by show goodOf _ _ = _; rw [goodOf, if_pos hgs]
      have hV' : p.T.V ((i : ℕ) + 1) (res p.T s) = Wc D i := p.fw.laws.spaceW _ (inR i) _ hgs
      have hpre : ∃ j' : (Fin (p.R.toRealDat.nW i) → D.what₂.LL) →ₛₗ[s] (p.R.toRealDat.HW i s).H,
          ∀ g : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n,
            ((p.R.toRealDat.HW i s).e (j' ((p.fw.e i g : (p.R.toRealDat.FW i).WK) :
              Fin (p.R.toRealDat.nW i) → D.what₂.LL))) (p.v₀ i s) =
              hV' ▸ p.T.phiJ ((i : ℕ) + 1) (res p.T s) (wtA (p.κ i)) (g : p.T.R ((i : ℕ) + 1)) := by
        by_contra hne
        have hj0 := p.fw.ev0 i s hgs hV' hne
        have hli := (hp.prim.unif i s).1 1 (fun _ => y) (linearIndependent_unique_iff.2 hy0)
        rw [hj0] at hli
        exact hli.ne_zero 0 (LinearMap.zero_apply _)
      refine Or.inl ⟨hgs, p.v₀ i s, (p.fw.hv₀ i s).1, ?_⟩
      rw [hf'_def, adFun_rdU]
      refine (p.fw.ev i s hgs hV' hpre f).trans ?_
      show phiC p.T hV' (wtA (p.κ i)) _ = _
      generalize (f : p.T.R ((i : ℕ) + 1)) = F0
      rw [ha]
      exact phiC_congr hgd'.symm _ _ _ _
    · have hgd' : gd p.T s = resC p.T s := by show goodOf _ _ = _; rw [goodOf, if_neg hgs]
      have hVc : p.T.V ((i : ℕ) + 1) (resC p.T s) = Wc D i := p.fw.laws.spaceW _ (inR i) _ (good_resC p.T hgs)
      obtain ⟨v, hv, hvf⟩ := (p.bar i s hgs hVc).1 (hp.jEvBar i s hgs hVc)
      refine Or.inr ⟨hgs, v, hv, ?_⟩
      rw [hf'_def, adFun_rdU]
      refine (hvf f).trans (funext fun g => ?_)
      show starRingEnd ℂ (phiC p.T hVc (wtA (p.κ i)) _ g) = _
      generalize (f : p.T.R ((i : ℕ) + 1)) = F0
      rw [ha, phiC_congr hgd' hV hVc]
  have e := (he p.T p.fw.laws p.fw.alg_eq p.R.toRealDat.θ hmod.inf s (p.R.toRealDat.MW i s) hV _ hx f' hf' hc).2
  rw [← hip, inner_self_eq_norm_sq_to_K] at e
  have e' : ‖x‖ ^ 2 = ratio D i (p.R.toRealDat.νW i) (p.R.toRealDat.fdW i) * probSq p.T i (gd p.T s) f' := by
    have : (((‖x‖ ^ 2 : ℝ)) : ℂ) = _ := (Complex.ofReal_pow _ _).trans e
    exact_mod_cast this
  rw [hf'_def, probSq_rdU] at e'
  unfold petW
  rw [← hgd, hG, ← Real.sqrt_sq (norm_nonneg x), e', Real.sqrt_mul' _ (sq_nonneg _),
    Real.sqrt_sq (petAt_nonneg _ _ _ _ _ _ _)]
  rfl

end GlobalTheory.CovTop.MeasRd
