import Mathlib
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValueGermsIndependentOfChart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicConnectionValueBaseChangeField
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortThetaValueFieldEqMapSubfieldData
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FaithfullyFlatPointsBaseChangeDescent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HarmonicAny

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FrameBiextId GlobalTheory.ChartCmp ReciprocityTheory.ChartRestriction.G.TB.WickVanishing Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh GlobalTheory.ChartField in
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct) in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ hs S _ _ _ y C C' k n F f f' hf hf' P hP`. Establish `hAct` using `expActOf_of GlobalTheory.EigDir.linEig_holds`. Take `⟨φ, hφ, hx⟩` from `expChartOf_of hAct E H Dw l Xo c S y C`. Take `⟨φ', hφ', hx'⟩` from `expChartOf_of hAct E H Dw l Xo c S y C'`. Establish `hxx` using `ExpUniqChart.expUniqTan E H Dw l Xo c S y _ _ hx' hx`.

Establish `ha` using `hAct E H Dw l Xo c S y C φ hφ`. Establish `ha'` using `hAct E H Dw l Xo c S y C' φ' hφ'`. Establish `heig` using `GlobalTheory.EigDir.linEig_holds E H Dw l Xo c S y C'`. Establish `hw` using `primUniq_of_global GlobalTheory.SemiRigid.globalFns E H Dw l Xo _ _ C.prim C'.prim`. Establish `hd` using `CIndRelPf.dim_eq_card C.uvec C.chart.basis`.

Establish `hd'` using `CIndRelPf.dim_eq_card C'.uvec C'.chart.basis`. Rewrite using `[chartVal_eq, chartVal_eq]`. Take `⟨d, B, u, x, e, wP, h, hc, hfr, hp, hg, hr⟩` from `C`. Take `⟨d', B', u', x', e', wP', h', hc', hfr', hp', hg', hr'⟩` from `C'`. Simplify using `only at hd hd' hw hφ hφ' ha ha' heig f f' hf hf' φ φ' ⊢`.

Substitute `hd hd' hw` using the available equality. Take `⟨⟨β, hβ⟩, hl⟩` from `exp_facts B.G u hc.basis φ hφ`. Take `⟨⟨β', hβ'⟩, hl'⟩` from `exp_facts B'.G u' hc'.basis φ' hφ'`. Set `α : Q S (dL Dw) 1` to `⟨φ, hφ.const⟩`. Set `α' : Q S (dL Dw) 1` to `⟨φ', hφ'.const⟩`.

Take `⟨hinv, hαα, hlaw, hact⟩` from `coord_of_exp α β α' β' hβ hβ'`. Set `D : 𝓞 E → Q S (dL Dw) 1` to `fun b => ⟨fun j => algebraMap c.F S (embK c ((ltIdx Dw).symm j).1 b) • MvPowerSeries.X ((0 : Fin 1), j), fun j => by simp⟩`. Establish `hD : ∀ (A ψ : Q S (dL Dw) 1) (b : 𝓞 E), (∀ j, MvPowerSeries.subst (fun p : Fin 1 × Fin (dL Dw) => ψ.1 p.2) (A.1 j) = MvPowerSeries.subst (fun q : Fin 1 × Fin (dL Dw) => algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 b) • (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) …`. Introduce `A ψ b hb`. Use `Subtype.ext (funext fun j => ?_)` and prove the remaining obligations.

Rewrite using `[ac_val, ac_val, comp1, comp1, CoordLaw.ev_one_eq, CoordLaw.ev_one_eq, hb j]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Take `⟨i, s⟩` from `q`. Take `rfl : i = 0` from `Subsingleton.elim _ _`.

Both sides reduce to the same expression. Establish `hj : ∀ (ψ : Q S (dL Dw) 1) (m : ℕ), jφ ψ.1 m = jQ m ![ψ]` using `fun ψ m => subst_eq m _ ![ψ] (fun s => by obtain ⟨j, s⟩ := s; fin_cases j; rfl) (fun s => (cc_psTrunc m _).trans (ψ.2 _))`. Establish `hco : ∀ m n (v : Q S (dL Dw) n), PP (t` using `Xo.univ.t) (x0 := y.x) m x' v = PP (t := Xo.univ.t) (x0 := y.x) m x (ac (ac α β') v) := fun m n v => by`. Establish `e0 : homAt y.x (jφ α'.1 m) ≫ x' m = homAt y.x (jφ α.1 m) ≫ x m` using `congrFun hxx m`. Rewrite `e0` using `[hj, hj]`.

Establish `e1 : PP (t` using `Xo.univ.t) (x0 := y.x) m x' α' = PP (t := Xo.univ.t) (x0 := y.x) m x α := e0`. Establish `e2` using `congrArg (homAt y.x (jQ m ![ac β' v]) ≫ ·) e1`. Simplify using `only [PP_sq] at e2`. Establish `e3 : sq ![ac β' v] α' = v` using `Subtype.ext (by`. Rewrite using `[show sq ![ac β' v] α' = ac α' (ac β' v) from rfl, ac_val, ac_val]`.

Conclude with `gt_comp_inv hβ' _ v.2)`. Rewrite `e2` using `[e3]`. Rewrite using `[FrameRatioAdj.ac_ac]`. Conclude with `e2`. Establish `hsurj` using `(GlobalTheory.SemiRigid.globalFns _ _ (AbelianSchemeGerms.isAbelianScheme_tensor _ _ (isAbelianScheme_univ Xo) (isAbelianScheme_univ Xo))).2`.

Take `⟨ε, hε, hge⟩` from `exists_jRel hs hsurj B B' ((isChart_iff y _ _ _ _ _).1 hc) ((isChart_iff y _ _ _ _ _).1 hc') ((isFrame_iff y _ _ _ _ _ _ _ _ _).1 hfr) ((isFrame_iff y _ _ _ _ _ _ _ _ _).1 hfr') (ac α β') (ac α' β) hinv hco (hlaw (FQ B.G) (FQ B'.G) _ hl hl') (fun b => hact (AQ B.A b) (AQ B'.A b) …`. Use `nabValN_box_eq _ (𝓞 E) S B B' (ac α β') (ac α' β) h h' hg hg' (E →+* ℂ) Dw.mult ComplexEmbedding.conjugate (InPsi H) (fun τ => (algebraMap c.F S).comp (embK c τ)) (fun τ => by ext x; simp) (inPsi_or_conjugate H) (fun τ a => by` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, hs]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq, IsCMField.complexEmbedding_complexConj])`. Use the proof step `(fun σ τ hne => by`. Establish `hex : ∃ a : 𝓞 E, σ (a : E) ≠ τ (a : E)`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Conclude with `hne (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => by simpa using hc a))`. Take `⟨a, ha⟩` from `hex`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `h0 : embK c σ a - embK c τ a ≠ 0`. Rewrite using `[sub_ne_zero]`.

Introduce `h1`. Apply `ha` to reduce the goal to its premises. Rewrite using `[← embK_coe c, ← embK_coe c, h1]`. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, ← map_sub]`. Conclude with `(Ne.isUnit h0).map _)`.

Use `u u' (fun ℓ b => funext fun i => ?_) (fun ℓ => funext fun i => ?_) n _`. Use the proof step `(PullbackSections.harmK_map (algebraMap c.F S) hP) H.w0 k f f' ε hε`. Use the proof step `(fun b => hge k (F b) (f b) (f' b) ((isGerm_iff y _ _ _ _ _ _ _ _).1 (hf b)) ((isGerm_iff y _ _ _ _ _ _ _ _).1 (hf' b)))`. Use `Eq.trans ?_ (heig b ℓ i)` and prove the remaining obligations. Simplify using `only [Matrix.mulVec, dotProduct, dAct, FB.actK, gt_map_id, dLin]`.

Establish `e0 : comp1 (ac α β').1 φ' = φ` using `(ac_val _ α').symm.trans (congrArg Subtype.val hαα)`. Establish `e1` using `congrFun (congrFun (dLin_comp1 (ac α β').1 φ' hφ'.const) i) (ltIdx Dw ℓ)`. Rewrite `e1` using `[e0, Matrix.mul_apply]`. Rewrite using `[← hφ.lin ℓ i]`. Use `e1.trans (Finset.sum_congr rfl fun j _ => ?_)` and prove the remaining obligations.

Rewrite using `[← hφ'.lin ℓ j]`. Both sides reduce to the same expression.
-/
theorem chartVal_indep_of_harmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (S : Type) [Field S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C C' : ChartAt Xo c y) (k n : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S) (f' : Fin n → MvPowerSeries (Fin 1 × Fin C'.d) S), (∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)) → (∀ b, IsGerm y C'.d C'.x C'.B.A.act C'.e C'.wP k (F b) (f' b)) → ∀ (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) → chartVal C k f P = chartVal C' k f' P := by
  intro E _ _ _ H Dw l Xo c _ hs S _ _ _ y C C' k n F f f' hf hf' P hP
  have hAct := expActOf_of GlobalTheory.EigDir.linEig_holds
  obtain ⟨φ, hφ, hx⟩ := expChartOf_of hAct E H Dw l Xo c S y C
  obtain ⟨φ', hφ', hx'⟩ := expChartOf_of hAct E H Dw l Xo c S y C'
  have hxx := ExpUniqChart.expUniqTan E H Dw l Xo c S y _ _ hx' hx
  have ha := hAct E H Dw l Xo c S y C φ hφ
  have ha' := hAct E H Dw l Xo c S y C' φ' hφ'
  have heig := GlobalTheory.EigDir.linEig_holds E H Dw l Xo c S y C'
  have hw := primUniq_of_global GlobalTheory.SemiRigid.globalFns E H Dw l Xo _ _ C.prim C'.prim
  have hd := CIndRelPf.dim_eq_card C.uvec C.chart.basis
  have hd' := CIndRelPf.dim_eq_card C'.uvec C'.chart.basis
  rw [chartVal_eq, chartVal_eq]
  obtain ⟨d, B, u, x, e, wP, h, hc, hfr, hp, hg, hr⟩ := C
  obtain ⟨d', B', u', x', e', wP', h', hc', hfr', hp', hg', hr'⟩ := C'
  dsimp only at hd hd' hw hφ hφ' ha ha' heig f f' hf hf' φ φ' ⊢
  subst hd hd' hw
  obtain ⟨⟨β, hβ⟩, hl⟩ := exp_facts B.G u hc.basis φ hφ
  obtain ⟨⟨β', hβ'⟩, hl'⟩ := exp_facts B'.G u' hc'.basis φ' hφ'
  let α : Q S (dL Dw) 1 := ⟨φ, hφ.const⟩
  let α' : Q S (dL Dw) 1 := ⟨φ', hφ'.const⟩
  obtain ⟨hinv, hαα, hlaw, hact⟩ := coord_of_exp α β α' β' hβ hβ'
  let D : 𝓞 E → Q S (dL Dw) 1 := fun b => ⟨fun j => algebraMap c.F S (embK c ((ltIdx Dw).symm j).1 b) •
    MvPowerSeries.X ((0 : Fin 1), j), fun j => by simp⟩
  have hD : ∀ (A ψ : Q S (dL Dw) 1) (b : 𝓞 E), (∀ j, MvPowerSeries.subst (fun p : Fin 1 × Fin (dL Dw) => ψ.1 p.2) (A.1 j) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin (dL Dw) => algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 b) •
        (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) (ψ.1 j)) → ac A ψ = ac ψ (D b) := by
    intro A ψ b hb
    refine Subtype.ext (funext fun j => ?_)
    rw [ac_val, ac_val, comp1, comp1, CoordLaw.ev_one_eq, CoordLaw.ev_one_eq, hb j]
    congr 1
    funext q
    obtain ⟨i, s⟩ := q
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rfl
  have hj : ∀ (ψ : Q S (dL Dw) 1) (m : ℕ), jφ ψ.1 m = jQ m ![ψ] := fun ψ m =>
    subst_eq m _ ![ψ] (fun s => by obtain ⟨j, s⟩ := s; fin_cases j; rfl) (fun s => (cc_psTrunc m _).trans (ψ.2 _))
  have hco : ∀ m n (v : Q S (dL Dw) n), PP (t := Xo.univ.t) (x0 := y.x) m x' v =
      PP (t := Xo.univ.t) (x0 := y.x) m x (ac (ac α β') v) := fun m n v => by
    have e0 : homAt y.x (jφ α'.1 m) ≫ x' m = homAt y.x (jφ α.1 m) ≫ x m := congrFun hxx m
    rw [hj, hj] at e0
    have e1 : PP (t := Xo.univ.t) (x0 := y.x) m x' α' = PP (t := Xo.univ.t) (x0 := y.x) m x α := e0
    have e2 := congrArg (homAt y.x (jQ m ![ac β' v]) ≫ ·) e1
    simp only [PP_sq] at e2
    have e3 : sq ![ac β' v] α' = v := Subtype.ext (by
      rw [show sq ![ac β' v] α' = ac α' (ac β' v) from rfl, ac_val, ac_val]; exact gt_comp_inv hβ' _ v.2)
    rw [e3] at e2
    rw [FrameRatioAdj.ac_ac]
    exact e2
  have hsurj := (GlobalTheory.SemiRigid.globalFns _ _ (AbelianSchemeGerms.isAbelianScheme_tensor _ _ (isAbelianScheme_univ Xo)
    (isAbelianScheme_univ Xo))).2
  obtain ⟨ε, hε, hge⟩ := exists_jRel hs hsurj B B' ((isChart_iff y _ _ _ _ _).1 hc) ((isChart_iff y _ _ _ _ _).1 hc')
    ((isFrame_iff y _ _ _ _ _ _ _ _ _).1 hfr) ((isFrame_iff y _ _ _ _ _ _ _ _ _).1 hfr') (ac α β') (ac α' β) hinv hco
    (hlaw (FQ B.G) (FQ B'.G) _ hl hl')
    (fun b => hact (AQ B.A b) (AQ B'.A b) (D b) (hD _ α b (ha b)) (hD _ α' b (ha' b))) wP
    ((P.map (algebraMap c.F S)).totalDegree + 2)
  refine nabValN_box_eq _ (𝓞 E) S B B' (ac α β') (ac α' β) h h' hg hg' (E →+* ℂ) Dw.mult
    ComplexEmbedding.conjugate (InPsi H) (fun τ => (algebraMap c.F S).comp (embK c τ)) (fun τ => by ext x; simp)
    (inPsi_or_conjugate H)
    (fun τ a => by
      rw [RingHom.comp_apply, RingHom.comp_apply, hs]
      congr 1
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq, IsCMField.complexEmbedding_complexConj])
    (fun σ τ hne => by
      have hex : ∃ a : 𝓞 E, σ (a : E) ≠ τ (a : E) := by
        by_contra hc
        push Not at hc
        exact hne (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => by simpa using hc a))
      obtain ⟨a, ha⟩ := hex
      refine ⟨a, ?_⟩
      have h0 : embK c σ a - embK c τ a ≠ 0 := by
        rw [sub_ne_zero]
        intro h1
        apply ha
        rw [← embK_coe c, ← embK_coe c, h1]
      rw [RingHom.comp_apply, RingHom.comp_apply, ← map_sub]
      exact (Ne.isUnit h0).map _)
    u u' (fun ℓ b => funext fun i => ?_) (fun ℓ => funext fun i => ?_) n _
    (PullbackSections.harmK_map (algebraMap c.F S) hP) H.w0 k f f' ε hε
    (fun b => hge k (F b) (f b) (f' b) ((isGerm_iff y _ _ _ _ _ _ _ _).1 (hf b))
      ((isGerm_iff y _ _ _ _ _ _ _ _).1 (hf' b)))
  · refine Eq.trans ?_ (heig b ℓ i)
    simp only [Matrix.mulVec, dotProduct, dAct, FB.actK, gt_map_id, dLin]
  · have e0 : comp1 (ac α β').1 φ' = φ := (ac_val _ α').symm.trans (congrArg Subtype.val hαα)
    have e1 := congrFun (congrFun (dLin_comp1 (ac α β').1 φ' hφ'.const) i) (ltIdx Dw ℓ)
    rw [e0, Matrix.mul_apply] at e1
    rw [← hφ.lin ℓ i]
    refine e1.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [← hφ'.lin ℓ j]
    rfl

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Substitute `hK` using the available equality. Take `⟨hx, hu, -⟩` from `hm`. Take `⟨x', xo', u', tan', eig', basis', s', gen'⟩` from `y'`. Simplify using `only at hx hu h hh F' hF'`. Establish `hu' : u' = fun τ i => spMap (dualMap (ψ : S →+* S')) ≫ y.u τ i` using `funext fun τ => funext fun i => hu τ i`.

Establish `hx' : x' = spMap (ψ : S →+* S') ≫ y.x` using `hx`. Substitute `hx'` using the available equality. Substitute `hu'` using the available equality. Establish `hh' : h = ptBC (ψ : S →+* S') y.x` using `Over.OverMorphism.ext hh`. Substitute `hh'` using the available equality.

Take `⟨C, hex, hpin⟩` from `hnab.2 S y`. Use `choose f hf using fun b => hex k (F b)`. Take `⟨B', x2, e2, -, hF, hA, -, -, -, -, hch, hfr, hga, hrig, hgerm⟩` from `GlobalTheory.rawChart_baseChange E H Dw l Xo c S S' ψ y.x y.u (ChartAt.toRaw C)`. Set `z : FrPt Xo c S'` to `⟨_, xo', _, tan', eig', basis', s', gen'⟩`. Set `C2 : ChartAt Xo c z` to `⟨C.d, B', fun ℓ j => ψ (C.uvec ℓ j), x2, e2, C.wP, MvPowerSeries.map (ψ : S →+* S') C.h, ⟨hch.zero, hch.trunc, hch.law, hch.act, hch.tan, hch.basis⟩, ⟨hfr.gen, hfr.ph1, hfr.ph2, hfr.sy, hfr.ad⟩, C.prim, hga, hrig⟩`.

Establish `hg2 : ∀ b, IsGerm z C2.d C2.x C2.B.A.act C2.e C2.wP k (F' b) (MvPowerSeries.map (ψ : S →+* S') (f b))` using `fun b => hgerm k (F b) (F' b) (f b) (hF' b) (hf b)`. Take `⟨C3, hex3, hpin3⟩` from `hnab.2 S' z`. Use `choose f3 hf3 using fun b => hex3 k (F' b)`. Establish `hI` using `chartVal_indep_of_harmonic E H Dw l Xo c hnab.1 S' z C2 C3 k n F' _ f3 hg2 hf3 P hP`. Establish `e3 : (∑ m ∈ P.support, algebraMap c.F S' (P.coeff m) * ∏ b, nab z k (F' b) (colOf m b)) = chartVal C3 k f3 P`.

Unfold `chartVal`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun b _ => hpin3 k (F' b) (f3 b) (hf3 b) (colOf m b)`. Use `Eq.trans ?_ (hI.trans e3.symm)` and prove the remaining obligations.

Unfold `chartVal`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, AlgHom.commutes, map_prod]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `hN` using `nabMap_holds S S' (ψ : S →+* S') C.d (𝓞 E) C.B B' hF hA C.h C.gauge H.w0 k (f b) (Lt1 Dw) C.uvec (MvPolynomial.monomial (colOf m b) 1)`. Rewrite `hN` using `[MvPolynomial.map_monomial, map_one]`. Conclude with `(congrArg ψ (hpin k (F b) (f b) (hf b) (colOf m b))).trans hN.symm`.
-/
theorem sum_map_of_harmonic {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] (nab : NabV Xo c)
    (hnab : IsNab Xo c nab) {S S' : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    [Field S'] [Algebra c.F S'] [Algebra ℚ S'] (ψ : S →ₐ[c.F] S') (y : FrPt Xo c S) (y' : FrPt Xo c S')
    (hm : FrMap ψ y y') (h : ptO Xo y'.x ⟶ ptO Xo y.x) (hh : h.left = spMap ψ.toRingHom)
    (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1)) (K : ℤ) (k : ℕ)
    (hK : K = k) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x)))
    (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y'.x)))
    (hF' : ∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L K (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) :
    ψ (∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y K (F b) (colOf m b)) =
      ∑ m ∈ P.support, algebraMap c.F S' (P.coeff m) * ∏ b, nab y' K (F' b) (colOf m b) := by
  subst hK
  obtain ⟨hx, hu, -⟩ := hm
  obtain ⟨x', xo', u', tan', eig', basis', s', gen'⟩ := y'
  dsimp only at hx hu h hh F' hF'
  have hu' : u' = fun τ i => spMap (dualMap (ψ : S →+* S')) ≫ y.u τ i := funext fun τ => funext fun i => hu τ i
  have hx' : x' = spMap (ψ : S →+* S') ≫ y.x := hx
  subst hx'
  subst hu'
  have hh' : h = ptBC (ψ : S →+* S') y.x := Over.OverMorphism.ext hh
  subst hh'
  obtain ⟨C, hex, hpin⟩ := hnab.2 S y
  choose f hf using fun b => hex k (F b)
  obtain ⟨B', x2, e2, -, hF, hA, -, -, -, -, hch, hfr, hga, hrig, hgerm⟩ :=
    GlobalTheory.rawChart_baseChange E H Dw l Xo c S S' ψ y.x y.u (ChartAt.toRaw C)
  let z : FrPt Xo c S' := ⟨_, xo', _, tan', eig', basis', s', gen'⟩
  let C2 : ChartAt Xo c z :=
    ⟨C.d, B', fun ℓ j => ψ (C.uvec ℓ j), x2, e2, C.wP, MvPowerSeries.map (ψ : S →+* S') C.h,
      ⟨hch.zero, hch.trunc, hch.law, hch.act, hch.tan, hch.basis⟩,
      ⟨hfr.gen, hfr.ph1, hfr.ph2, hfr.sy, hfr.ad⟩, C.prim, hga, hrig⟩
  have hg2 : ∀ b, IsGerm z C2.d C2.x C2.B.A.act C2.e C2.wP k (F' b)
      (MvPowerSeries.map (ψ : S →+* S') (f b)) := fun b => hgerm k (F b) (F' b) (f b) (hF' b) (hf b)
  obtain ⟨C3, hex3, hpin3⟩ := hnab.2 S' z
  choose f3 hf3 using fun b => hex3 k (F' b)
  have hI := chartVal_indep_of_harmonic E H Dw l Xo c hnab.1 S' z C2 C3 k n F' _ f3 hg2 hf3 P hP
  have e3 : (∑ m ∈ P.support, algebraMap c.F S' (P.coeff m) * ∏ b, nab z k (F' b) (colOf m b)) =
      chartVal C3 k f3 P := by
    unfold chartVal
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    exact Finset.prod_congr rfl fun b _ => hpin3 k (F' b) (f3 b) (hf3 b) (colOf m b)
  refine Eq.trans ?_ (hI.trans e3.symm)
  unfold chartVal
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, AlgHom.commutes, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  have hN := nabMap_holds S S' (ψ : S →+* S') C.d (𝓞 E) C.B B' hF hA C.h C.gauge H.w0 k (f b) (Lt1 Dw) C.uvec
    (MvPolynomial.monomial (colOf m b) 1)
  rw [MvPolynomial.map_monomial, map_one] at hN
  exact (congrArg ψ (hpin k (F b) (f b) (hf b) (colOf m b))).trans hN.symm

/- English proof (translation)
Set `h : ptO Xo w.x ⟶ ptO Xo y.x` to `Over.homMk (spMap ψ.toRingHom) hm.1.symm`. Use `choose F' hF' using fun q i b => GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F q i b)`. Take `⟨p1, -, p3, -⟩` from `GlobalTheory.inZh_geoInj_stable E H Dw l Xo n Λ N`. Use `⟨fun i b => h ≫ z i b, fun q b => h ≫ tp q b, F', fun i => p1 _ _ h _ (hz i), p3 S T y.x w.x ψ.toRingHom h rfl _ z hg, fun q b => ⟨?_, ?_⟩, fun q i b => ?_, fun q => ?_⟩` and prove the remaining obligations. Establish `e : h ≫ levPt Xo y.x (levRep (q b)) = levPt Xo w.x (levRep (q b))`.

Unfold `levPt`. Rewrite using `[← Category.assoc, comp_toUnit]`. Rewrite using `[← e, ← (ht q b).1, MonObj.comp_pow]`. Take `⟨j, hj⟩` from `(ht q b).2`. Conclude with `⟨j, fun u hu => by rw [Category.assoc, hj u hu, MonObj.comp_one]⟩`.

Conclude with `(GlobalTheory.VtBaseChange.isVtOver_isUUOver_baseChange E H Dw l Xo N ⊤ _ _ h y.s w.s (GlobalTheory.FramedBaseChange.isPullSec ψ hm h rfl) (F q i b) (F' q i b) (hF' q i b)).2 _ _ (hF q i b)`. Rewrite using `[map_sum]`. Use `letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra`. Use `letI : Algebra ℚ T := ((algebraMap c.F T).comp (algebraMap ℚ c.F)).toAlgebra`. Conclude with `Finset.sum_congr rfl fun i _ => sum_map_of_harmonic nab hnab ψ y w hm h rfl n P hP _ (N ^ 2) (by push_cast; rfl) (F q i) (F' q i) (hF' q i)`.
-/
theorem exists_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {n : ℕ} (Λ : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1))
    {S T : Type} [CommRing S] [Algebra c.F S] [Field T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (w : FrPt Xo c T) (hm : FrMap ψ y w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo y.x z)
    (ht : ∀ q b, tp q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b))
    (hF : ∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (tp q b) (F q i b)) :
    ∃ (z' : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo w.x ⟶ Xo.univ.t.G))
      (tp' : (Fin n → LevQ Dw l) → Fin n → (ptO Xo w.x ⟶ Xo.univ.t.G))
      (F' : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
        LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo w.x))),
      (∀ i, InZh Xo Λ N (z' i)) ∧ GeoInj Xo w.x z' ∧
      (∀ q b, tp' q b ^ N = levPt Xo w.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp' q b)) ∧
      (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N w.s (z' i b) (tp' q b) (F' q i b)) ∧
      ∀ q, ψ (∑ i, ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          ∏ b, nab y ((N : ℤ) ^ 2) (F q i b) (colOf m b)) =
        ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
          ∏ b, nab w ((N : ℤ) ^ 2) (F' q i b) (colOf m b) := by
  let h : ptO Xo w.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hm.1.symm
  choose F' hF' using fun q i b => GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2)
    (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F q i b)
  obtain ⟨p1, -, p3, -⟩ := GlobalTheory.inZh_geoInj_stable E H Dw l Xo n Λ N
  refine ⟨fun i b => h ≫ z i b, fun q b => h ≫ tp q b, F', fun i => p1 _ _ h _ (hz i),
    p3 S T y.x w.x ψ.toRingHom h rfl _ z hg, fun q b => ⟨?_, ?_⟩, fun q i b => ?_, fun q => ?_⟩
  · have e : h ≫ levPt Xo y.x (levRep (q b)) = levPt Xo w.x (levRep (q b)) := by
      unfold levPt
      rw [← Category.assoc, comp_toUnit]
    rw [← e, ← (ht q b).1, MonObj.comp_pow]
  · obtain ⟨j, hj⟩ := (ht q b).2
    exact ⟨j, fun u hu => by rw [Category.assoc, hj u hu, MonObj.comp_one]⟩
  · exact (GlobalTheory.VtBaseChange.isVtOver_isUUOver_baseChange E H Dw l Xo N ⊤ _ _ h y.s w.s
      (GlobalTheory.FramedBaseChange.isPullSec ψ hm h rfl) (F q i b) (F' q i b) (hF' q i b)).2 _ _ (hF q i b)
  · rw [map_sum]
    letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
    letI : Algebra ℚ T := ((algebraMap c.F T).comp (algebraMap ℚ c.F)).toAlgebra
    exact Finset.sum_congr rfl fun i _ =>
      sum_map_of_harmonic nab hnab ψ y w hm h rfl n P hP _ (N ^ 2) (by push_cast; rfl) (F q i) (F' q i) (hF' q i)

/- English proof (translation)
Establish `hL : Laws` using `GlobalTheory.firstFiveLaws.1`. Use `haveI := GlobalTheory.ShortAtField.finite_levQ Dw l`. Take `⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1, e1⟩` from `hv`. Take `⟨U, _, _, ψ2, ψ1, hc, -, hinj⟩` from `GlobalTheory.exists_faithfullyFlat_pushout c.F K k S1 ψ φ1 hf1`. Use `haveI : Nontrivial U := hinj.nontrivial`.

Take `⟨Ω, _, _, ⟨κ⟩⟩` from `GlobalTheory.ShortAtField.exists_algHom_field c.F U`. Take `⟨u, hu⟩` from `GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c S1 Ω (κ.comp ψ1) y1`. Take `⟨u', hu'⟩` from `GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c k Ω (κ.comp ψ2) yk`. Establish `e : (κ.comp ψ2).comp ψ = (κ.comp ψ1).comp φ1`. Rewrite using `[AlgHom.comp_assoc, hc, AlgHom.comp_assoc]`.

Establish `h1` using `GlobalTheory.FramedBaseChange.trans φ1 _ hm1 hu`. Establish `h2` using `GlobalTheory.FramedBaseChange.trans ψ _ hψ hu'`. Rewrite `h2` using `[e]`. Take `rfl : u = u'` from `(GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K Ω _ y).1 u u' h1 h2`. Take `⟨z1', tp1', G1, a1', b1', c1', d1', f1⟩` from `exists_pull nab hnab Λ N P hP (κ.comp ψ1) y1 u hu z1 tp1 F1 hz1 hg1 ht1 hu1`.

Take `⟨z2', tp2', G2, a2', b2', c2', d2', f2⟩` from `exists_pull nab hnab Λ N P hP (κ.comp ψ2) yk u hu' z tp F hz hg ht hF`. Apply `(κ.comp ψ2).toRingHom.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(κ.comp ψ2) (ψ v) = (κ.comp ψ2) _`. Rewrite using `[show (κ.comp ψ2) (ψ v) = (κ.comp ψ1) (φ1 v) from AlgHom.congr_fun e v, e1]`. Use `GlobalTheory.ShortAtField.map_weighted (κ.comp ψ1) (κ.comp ψ2) _ cf _ _ fun q => ?_` and prove the remaining obligations.

Conclude with `(f1 q).trans ((GlobalTheory.shortSum_indep_local hL E H Dw l Xo c nab hnab n Λ N hU hT hN P Ω u z1' tp1' G1 z2' tp2' G2 a1' b1' c1' d1' a2' b2' c2' d2' q).trans (f2 q).symm)`.
-/
theorem map_shortValAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {n : ℕ} (Λ : GenLat E n) (N : ℕ) (hU : Λ.Unimod) (hT : Λ.TrivAt l.M) (hN : Λ.LevOK N l.M)
    (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1))
    (cf : (Fin n → LevQ Dw l) → c.F) (β : c.F)
    {K k : Type} [Field K] [Algebra c.F K] [Field k] [Algebra c.F k] (ψ : K →ₐ[c.F] k)
    (y : FrPt Xo c K) (yk : FrPt Xo c k) (hψ : FrMap ψ y yk)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo yk.x ⟶ Xo.univ.t.G))
    (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo yk.x ⟶ Xo.univ.t.G))
    (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo yk.x)))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo yk.x z)
    (ht : ∀ q b, tp q b ^ N = levPt Xo yk.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b))
    (hF : ∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N yk.s (z i b) (tp q b) (F q i b))
    (v : K) (hv : ShortValAt Xo c nab cf Λ β N P y v) :
    ψ v = algebraMap c.F k (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ *
        ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F k (cf q) *
        ∑ i, ∑ m ∈ P.support, algebraMap c.F k (P.coeff m) * ∏ b, nab yk ((N : ℤ) ^ 2) (F q i b) (colOf m b) := by
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  haveI := GlobalTheory.ShortAtField.finite_levQ Dw l
  obtain ⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1, e1⟩ := hv
  obtain ⟨U, _, _, ψ2, ψ1, hc, -, hinj⟩ := GlobalTheory.exists_faithfullyFlat_pushout c.F K k S1 ψ φ1 hf1
  haveI : Nontrivial U := hinj.nontrivial
  obtain ⟨Ω, _, _, ⟨κ⟩⟩ := GlobalTheory.ShortAtField.exists_algHom_field c.F U
  obtain ⟨u, hu⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c S1 Ω (κ.comp ψ1) y1
  obtain ⟨u', hu'⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c k Ω (κ.comp ψ2) yk
  have e : (κ.comp ψ2).comp ψ = (κ.comp ψ1).comp φ1 := by
    rw [AlgHom.comp_assoc, hc, AlgHom.comp_assoc]
  have h1 := GlobalTheory.FramedBaseChange.trans φ1 _ hm1 hu
  have h2 := GlobalTheory.FramedBaseChange.trans ψ _ hψ hu'
  rw [e] at h2
  obtain rfl : u = u' := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K Ω _ y).1 u u' h1 h2
  obtain ⟨z1', tp1', G1, a1', b1', c1', d1', f1⟩ :=
    exists_pull nab hnab Λ N P hP (κ.comp ψ1) y1 u hu z1 tp1 F1 hz1 hg1 ht1 hu1
  obtain ⟨z2', tp2', G2, a2', b2', c2', d2', f2⟩ :=
    exists_pull nab hnab Λ N P hP (κ.comp ψ2) yk u hu' z tp F hz hg ht hF
  apply (κ.comp ψ2).toRingHom.injective
  change (κ.comp ψ2) (ψ v) = (κ.comp ψ2) _
  rw [show (κ.comp ψ2) (ψ v) = (κ.comp ψ1) (φ1 v) from AlgHom.congr_fun e v, e1]
  refine GlobalTheory.ShortAtField.map_weighted (κ.comp ψ1) (κ.comp ψ2) _ cf _ _ fun q => ?_
  exact (f1 q).trans ((GlobalTheory.shortSum_indep_local hL E H Dw l Xo c nab hnab n Λ N hU hT hN P Ω u z1' tp1' G1 z2' tp2' G2
    a1' b1' c1' d1' a2' b2' c2' d2' q).trans (f2 q).symm)

end GlobalTheory.HarmonicAny
