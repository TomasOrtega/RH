import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartTransportSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IntChartTrunc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.L2.Pj.SaturatedCharts (toT prodPts_of_combAt combAt_of_prodPts chartTan_of tanAt_of isTan_iff' fst_comp_jetTan)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
open ReciprocityTheory.ChartRestriction.G.Chart (tcoord) in

/- English proof (translation)
Introduce `hIC E _ _ _ H Dw l Xo c _ hstar hTr T io y`. Establish `I : IntData Xo c T io y.1` using `Classical.choice (by`. Take `⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩` from `y.2.2`. Conclude with `⟨⟨G, t', m1, m2, ub, h1, h2, h3, h4, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩⟩)`. Establish `hp1 : IsProper I.t'.G.hom`.

Use `Xo.univ.proper` as an intermediate fact. Rewrite using `[← I.m1.cart.1.isoPullback_hom_snd]`. Use `infer_instance`. Establish `hprop : IsProper ((Over.pullback (spMap (algebraMap T.V (FractionRing T.V)))).obj I.G.G).hom` using `by show IsProper (pullback.snd I.G.G.hom (spMap (algebraMap T.V T.Fr)))`. Rewrite using `[← I.m2.cart.1.isoPullback_inv_snd]`.

Use `infer_instance`. Establish `hsm : Smooth I.G.G.hom` using `I.G.semi.smooth`. Take `⟨n, x, hx⟩` from `ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc (R := T.V) I.G.G`. Set `v : Fin n → (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀` to `T.V) (DualNumber T.V) ⟶ I.G.G) := fun i => ReciprocityTheory.ChartRestriction.G.Chart.tvec (x := x) (Pi.single i 1)`. Set `tg : Fin n → (Sp (DualNumber T.V) ⟶ I.G.G.left)` to `fun i => (v i).left`.

Establish `htgo : ∀ i, tg i ≫ I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V))` using `fun i => Over.w (v i)`. Establish `htgt : ∀ i, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT I.G (tg i) (htgo i))` using `fun i => ReciprocityTheory.ChartRestriction.G.Chart.isTan_tvec hx _`. Establish `htgc : ∀ i, tcoord hx _ (htgt i) = Pi.single i 1` using `fun i => ReciprocityTheory.ChartRestriction.G.Chart.tcoord_tvec hx _`. Establish `htan : ∀ i, IsTanAtG I.G (𝟙 (Sp T.V)) (tg i)` using `fun i => tanAt_of I.G _ (htgo i) (htgt i)`. Set `e0` to `Fintype.equivFin (Fin n)`.

Establish `hcombR : ∀ (a : Fin (Fintype.card (Fin n)) → T.V) (w : Sp (DualNumber T.V) ⟶ I.G.G.left) (hw : w ≫ I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V))), IsCombAtG I.G (𝟙 (Sp T.V)) (fun j => tg (e0.symm j)) a w ↔ ∃ h : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT I.G w hw …`. Introduce `a w hw`. Rewrite using `[combAt_iff I.G hx (fun j => tg (e0.symm j)) (fun j => htgo _) (fun j => htgt _) a w hw]`. Establish `hs : ∑ j, a j • tcoord hx _ (htgt (e0.symm j)) = fun i => a (e0 i)`. Simplify using `only [htgc]`.

Rewrite using `[← Equiv.sum_comp e0 (fun j => a j • (Pi.single (e0.symm j) (1 : T.V) : Fin n → T.V))]`. Simplify using `only [Equiv.symm_apply_apply]`. Use function extensionality and compare the values at `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hs]`.

Establish `hwo : ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → w ≫ I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V))` using `fun w hw => hw.1.trans (Category.comp_id _)`. Establish `hbasR : ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin (Fintype.card (Fin n)) → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) (fun j => tg (e0.symm j)) a w`. Introduce `w hw`. Establish `ht` using `chartTan_of I.G w hw`. Use `⟨fun j => tcoord hx _ ht (e0.symm j), (hcombR _ w (hwo w hw)).2 ⟨ht, ?_⟩, fun a ha => ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using `only [Equiv.symm_apply_apply]`. Take `⟨h', hh'⟩` from `(hcombR a w (hwo w hw)).1 ha`. Use function extensionality and compare the values at `j`. Use `congrFun hh' (e0.symm j)` as an intermediate fact.

Simplify using `only [Equiv.apply_symm_apply] at this`. Rewrite using `[← this]`. Establish `hbas : ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin n → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) (m` using `Fintype.card (Fin n)) (fun i => tg (e0.symm i)) (fun i => a (e0.symm i)) w := by`. Introduce `w hw`. Take `⟨a, ha, hu⟩` from `hbasR w hw`.

Use `⟨fun i => a (e0 i), by simpa only [Equiv.apply_symm_apply] using ha, fun b hb => ?_⟩` and prove the remaining obligations. Use `hu _ hb` as an intermediate fact. Use function extensionality and compare the values at `i`. Rewrite using `[← this]`. Simplify using `only [Equiv.symm_apply_apply]`.

Take `⟨d, B, uvec, xT, eT, wPT, hd, hu, hch, hfr, hpr, htr, hrig, -⟩` from `hIC E H T.V inferInstance I.G hprop tg htan hbas hstar`. Substitute `hd` using the available equality. Set `tgT : Fin (Fintype.card (Fin n)) → (Sp (DualNumber T.V) ⟶ I.G.G.left)` to `fun j => tg (e0.symm j)`. Establish `chartT : IsChartG I.G (𝟙 (Sp T.V)) (Fintype.card (Fin n)) B.G.F B.A.act tgT (fun j => Pi.single j (1 : T.V)) xT`. Establish `h0` using `isChartG_reindex I.G (𝟙 (Sp T.V)) _ B.G.F B.A.act tg uvec xT hch e0.symm`.

Establish `hue : (fun ℓ => uvec (e0.symm ℓ)) = fun j => Pi.single j (1 : T.V)`. Use function extensionality and compare the values at `ℓ j`. Rewrite using `[hu, Equiv.apply_symm_apply, Pi.single_apply]`. Simplify using `only [Fin.val_inj, eq_comm]`. Rewrite `h0` using `[hue]`.

Conclude with `h0`. Establish `tgBasis : (∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧ ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin (Fintype.card (Fin n)) → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w` using `⟨fun j => htan _, hbasR⟩`. Establish `hDo : ∀ j, (homAt (𝟙 (Sp T.V)) (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin (Fintype.card (Fin n))) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left ≫ I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V))` using `fun j => (Over.w (homAt (𝟙 (Sp T.V)) (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin (Fintype.card (Fin n))) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1)).trans (Category.comp_id _)`. Establish `hDt` using `fun j => dir_tan I.G xT chartT.zero j (hDo j)`. Establish `hDc : ∀ j, tcoord hx _ (hDt j) = tcoord hx _ (htgt (e0.symm j))`.

Introduce `j`. Take `⟨h, hh⟩` from `(combAt_iff I.G hx _ hDo hDt (Pi.single j 1) (tgT j) (htgo _)).1 (chartT.tan j)`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx rfl (htgt _) h, hh]`. Simplify using `[Pi.single_apply]`. Establish `hubo : ∀ ℓ : Lt1 Dw, (I.ub ℓ.1 ℓ.2).left ≫ I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V))` using `fun ℓ => Over.w _`.

Establish `hubt : ∀ ℓ : Lt1 Dw, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT I.G _ (hubo ℓ))` using `fun ℓ => (isTan_iff' I.G _).1 (I.tan ℓ.1 ℓ.2)`. Set `uvecT : Lt1 Dw → Fin (Fintype.card (Fin n)) → T.V` to `fun ℓ j => tcoord hx _ (hubt ℓ) (e0.symm j)`. Establish `dirT : ∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V)) (fun j : Fin (Fintype.card (Fin n)) => (homAt (𝟙 (Sp T.V)) (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin (Fintype.card (Fin n))) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left) (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left`. Introduce `ℓ`. Use `(combAt_iff I.G hx _ hDo hDt (uvecT ℓ) _ (hubo ℓ)).2 ⟨hubt ℓ, ?_⟩` and prove the remaining obligations.

Simplify using `only [hDc, htgc, uvecT]`. Rewrite using `[← Equiv.sum_comp e0 (fun j => tcoord hx _ (hubt ℓ) (e0.symm j) • (Pi.single (e0.symm j) (1 : T.V) : Fin n → T.V))]`. Simplify using `only [Equiv.symm_apply_apply]`. Use function extensionality and compare the values at `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Take `⟨B', uvec', x', e', wP', h', hch', hfr', hpr', hg', hr', hgen⟩` from `hTr hstar T io y I _ B tgT uvecT xT eT wPT tgBasis chartT dirT hfr hpr htr hrig`. Use `letI := io.toAlgebra`. Conclude with `⟨⟨⟨_, B', uvec', x', e', wP', h', hch', hfr', hpr', hg', hr'⟩, I, B.G.F, B.A.act, B.ph1, B.ph2, B.sy, B.ad, uvecT, tgT, xT, eT, wPT, tgBasis, chartT, dirT, hfr, hpr, hgen⟩, htr⟩`.
-/
theorem exists_intChart_frTrunc : IntChartStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ChartTransportSt Xo c → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ∃ C : IntegralChartA3 Xo c T io y, FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT := by
  intro hIC E _ _ _ H Dw l Xo c _ hstar hTr T io y
  have I : IntData Xo c T io y.1 := Classical.choice (by
    obtain ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩ := y.2.2
    exact ⟨⟨G, t', m1, m2, ub, h1, h2, h3, h4, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩⟩)

  have hp1 : IsProper I.t'.G.hom := by
    have := Xo.univ.proper
    rw [← I.m1.cart.1.isoPullback_hom_snd]
    infer_instance
  have hprop : IsProper ((Over.pullback (spMap (algebraMap T.V (FractionRing T.V)))).obj I.G.G).hom := by
    show IsProper (pullback.snd I.G.G.hom (spMap (algebraMap T.V T.Fr)))
    rw [← I.m2.cart.1.isoPullback_inv_snd]
    infer_instance

  have hsm : Smooth I.G.G.hom := I.G.semi.smooth
  obtain ⟨n, x, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc (R := T.V) I.G.G
  let v : Fin n → (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := T.V) (DualNumber T.V) ⟶ I.G.G) := fun i =>
    ReciprocityTheory.ChartRestriction.G.Chart.tvec (x := x) (Pi.single i 1)
  let tg : Fin n → (Sp (DualNumber T.V) ⟶ I.G.G.left) := fun i => (v i).left
  have htgo : ∀ i, tg i ≫ I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := fun i => Over.w (v i)
  have htgt : ∀ i, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT I.G (tg i) (htgo i)) := fun i =>
    ReciprocityTheory.ChartRestriction.G.Chart.isTan_tvec hx _
  have htgc : ∀ i, tcoord hx _ (htgt i) = Pi.single i 1 := fun i => ReciprocityTheory.ChartRestriction.G.Chart.tcoord_tvec hx _
  have htan : ∀ i, IsTanAtG I.G (𝟙 (Sp T.V)) (tg i) := fun i => tanAt_of I.G _ (htgo i) (htgt i)
  let e0 := Fintype.equivFin (Fin n)

  have hcombR : ∀ (a : Fin (Fintype.card (Fin n)) → T.V) (w : Sp (DualNumber T.V) ⟶ I.G.G.left)
      (hw : w ≫ I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V))),
      IsCombAtG I.G (𝟙 (Sp T.V)) (fun j => tg (e0.symm j)) a w ↔
        ∃ h : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT I.G w hw), tcoord hx _ h = fun i => a (e0 i) := by
    intro a w hw
    rw [combAt_iff I.G hx (fun j => tg (e0.symm j)) (fun j => htgo _) (fun j => htgt _) a w hw]
    have hs : ∑ j, a j • tcoord hx _ (htgt (e0.symm j)) = fun i => a (e0 i) := by
      simp only [htgc]
      rw [← Equiv.sum_comp e0 (fun j => a j • (Pi.single (e0.symm j) (1 : T.V) : Fin n → T.V))]
      simp only [Equiv.symm_apply_apply]
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hs]
  have hwo : ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → w ≫ I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) :=
    fun w hw => hw.1.trans (Category.comp_id _)
  have hbasR : ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w →
      ∃! a : Fin (Fintype.card (Fin n)) → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) (fun j => tg (e0.symm j)) a w := by
    intro w hw
    have ht := chartTan_of I.G w hw
    refine ⟨fun j => tcoord hx _ ht (e0.symm j), (hcombR _ w (hwo w hw)).2 ⟨ht, ?_⟩, fun a ha => ?_⟩
    · funext i
      simp only [Equiv.symm_apply_apply]
    · obtain ⟨h', hh'⟩ := (hcombR a w (hwo w hw)).1 ha
      funext j
      have := congrFun hh' (e0.symm j)
      simp only [Equiv.apply_symm_apply] at this
      rw [← this]
  have hbas : ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w →
      ∃! a : Fin n → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) (m := Fintype.card (Fin n))
        (fun i => tg (e0.symm i)) (fun i => a (e0.symm i)) w := by
    intro w hw
    obtain ⟨a, ha, hu⟩ := hbasR w hw
    refine ⟨fun i => a (e0 i), by simpa only [Equiv.apply_symm_apply] using ha, fun b hb => ?_⟩
    have := hu _ hb
    funext i
    rw [← this]
    simp only [Equiv.symm_apply_apply]

  obtain ⟨d, B, uvec, xT, eT, wPT, hd, hu, hch, hfr, hpr, htr, hrig, -⟩ :=
    hIC E H T.V inferInstance I.G hprop tg htan hbas hstar
  subst hd
  let tgT : Fin (Fintype.card (Fin n)) → (Sp (DualNumber T.V) ⟶ I.G.G.left) := fun j => tg (e0.symm j)
  have chartT : IsChartG I.G (𝟙 (Sp T.V)) (Fintype.card (Fin n)) B.G.F B.A.act tgT
      (fun j => Pi.single j (1 : T.V)) xT := by
    have h0 := isChartG_reindex I.G (𝟙 (Sp T.V)) _ B.G.F B.A.act tg uvec xT hch e0.symm
    have hue : (fun ℓ => uvec (e0.symm ℓ)) = fun j => Pi.single j (1 : T.V) := by
      funext ℓ j
      rw [hu, Equiv.apply_symm_apply, Pi.single_apply]
      simp only [Fin.val_inj, eq_comm]
    rw [hue] at h0
    exact h0
  have tgBasis : (∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧
      ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin (Fintype.card (Fin n)) → T.V,
        IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w := ⟨fun j => htan _, hbasR⟩

  have hDo : ∀ j, (homAt (𝟙 (Sp T.V)) (jetTan ((0 : Fin 1), j) :
      Jet T.V (Fin 1 × Fin (Fintype.card (Fin n))) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left ≫ I.G.G.hom =
        spMap (algebraMap T.V (DualNumber T.V)) := fun j =>
    (Over.w (homAt (𝟙 (Sp T.V)) (jetTan ((0 : Fin 1), j) :
      Jet T.V (Fin 1 × Fin (Fintype.card (Fin n))) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1)).trans
      (Category.comp_id _)
  have hDt := fun j => dir_tan I.G xT chartT.zero j (hDo j)
  have hDc : ∀ j, tcoord hx _ (hDt j) = tcoord hx _ (htgt (e0.symm j)) := by
    intro j
    obtain ⟨h, hh⟩ := (combAt_iff I.G hx _ hDo hDt (Pi.single j 1) (tgT j) (htgo _)).1 (chartT.tan j)
    rw [ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx rfl (htgt _) h, hh]
    simp [Pi.single_apply]

  have hubo : ∀ ℓ : Lt1 Dw, (I.ub ℓ.1 ℓ.2).left ≫ I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) :=
    fun ℓ => Over.w _
  have hubt : ∀ ℓ : Lt1 Dw, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT I.G _ (hubo ℓ)) := fun ℓ =>
    (isTan_iff' I.G _).1 (I.tan ℓ.1 ℓ.2)
  let uvecT : Lt1 Dw → Fin (Fintype.card (Fin n)) → T.V := fun ℓ j => tcoord hx _ (hubt ℓ) (e0.symm j)
  have dirT : ∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V))
      (fun j : Fin (Fintype.card (Fin n)) => (homAt (𝟙 (Sp T.V))
        (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin (Fintype.card (Fin n))) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫
          xT 1).left) (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left := by
    intro ℓ
    refine (combAt_iff I.G hx _ hDo hDt (uvecT ℓ) _ (hubo ℓ)).2 ⟨hubt ℓ, ?_⟩
    simp only [hDc, htgc, uvecT]
    rw [← Equiv.sum_comp e0 (fun j => tcoord hx _ (hubt ℓ) (e0.symm j) •
      (Pi.single (e0.symm j) (1 : T.V) : Fin n → T.V))]
    simp only [Equiv.symm_apply_apply]
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  obtain ⟨B', uvec', x', e', wP', h', hch', hfr', hpr', hg', hr', hgen⟩ :=
    hTr hstar T io y I _ B tgT uvecT xT eT wPT tgBasis chartT dirT hfr hpr htr hrig
  letI := io.toAlgebra
  exact ⟨⟨⟨_, B', uvec', x', e', wP', h', hch', hfr', hpr', hg', hr'⟩, I, B.G.F, B.A.act, B.ph1, B.ph2, B.sy, B.ad,
    uvecT, tgT, xT, eT, wPT, tgBasis, chartT, dirT, hfr, hpr, hgen⟩, htr⟩

end GlobalTheory.IntChartTrunc
