import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqChart
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActOf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PrimUniqPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndRelPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndEnc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FFVMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalCompApplyEqMvPowerSeriesSubst
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.BiextensionDepthLeOfRelated
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartLawActionEqTransportedOfCoordRel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumSupportRename
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.SvalValueAt
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.NabValNTransport

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

namespace GlobalTheory.ChartField

section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FrameBiextId GlobalTheory.ChartCmp ReciprocityTheory.ChartRestriction.G.TB.WickVanishing Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {S : Type} [Field S] [Algebra c.F S] [Algebra ℚ S]

/- English proof (translation)
Establish `h0 : MvPowerSeries.constantCoeff C.h = 0`. Use `congrArg MvPowerSeries.constantCoeff C.gauge.ax0` as an intermediate fact. Rewrite `this` using `[gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero]`. Then use the resulting hypothesis. Establish `key` using `GlobalTheory.nabValN_boxSer S C.d (𝓞 E) C.B S C.h H.w0 h0 k n f (Lt1 Dw) (LtN Dw n) (ltEquiv Dw n).symm (fun ℓ : LtN Dw n => ℓ.2.2) C.uvec (fun ℓ : LtN Dw n => C.uvec ⟨ℓ.1, ℓ.2.1⟩) (fun _ => rfl) (fun _ => rfl) (MvPolynomial.rename (ltEquiv Dw n) (P.map (algebraMap c.F S)))`. Rewrite `key` using `[MvPolynomial.rename_rename, Equiv.symm_comp_self, MvPolynomial.rename_id_apply, MvPolynomial.support_rename_of_injective (ltEquiv Dw n).injective, Finset.sum_image (fun _ _ _ _ h => Finsupp.mapDomain_injective (ltEquiv Dw n).injective h), MvPolynomial.support_map_of_injective _ …`.

Rewrite using `[key, chartVal]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_rename_mapDomain _ (ltEquiv Dw n).injective, MvPolynomial.coeff_map]`. Use `congr 1`. Use `Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations.

Use `congrArg (fun z => C.B.nabVal S C.h H.w0 k (f b) C.uvec (MvPolynomial.monomial z 1)) (Finsupp.ext fun ℓ => ?_)` and prove the remaining obligations. Conclude with `(Finsupp.mapDomain_apply (ltEquiv Dw n).injective m ⟨ℓ.1, ℓ.2, b⟩).symm`.
-/
theorem chartVal_eq {y : FrPt Xo c S} (C : ChartAt Xo c y) (k : ℕ) {n : ℕ} (f : Fin n → PS S 1 C.d)
    (P : MvPolynomial (LtN Dw n) c.F) :
    chartVal C k f P = nabValN C.B S C.h H.w0 k (GlobalTheory.PowGerm.boxSer f) (fun ℓ : LtN Dw n => ℓ.2.2)
      (fun ℓ : LtN Dw n => C.uvec ⟨ℓ.1, ℓ.2.1⟩) (P.map (algebraMap c.F S)) := by
  classical
  have h0 : MvPowerSeries.constantCoeff C.h = 0 := by
    have := congrArg MvPowerSeries.constantCoeff C.gauge.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
  have key := GlobalTheory.nabValN_boxSer S C.d (𝓞 E) C.B S C.h H.w0 h0 k n f (Lt1 Dw) (LtN Dw n) (ltEquiv Dw n).symm
    (fun ℓ : LtN Dw n => ℓ.2.2) C.uvec (fun ℓ : LtN Dw n => C.uvec ⟨ℓ.1, ℓ.2.1⟩) (fun _ => rfl) (fun _ => rfl)
    (MvPolynomial.rename (ltEquiv Dw n) (P.map (algebraMap c.F S)))
  rw [MvPolynomial.rename_rename, Equiv.symm_comp_self, MvPolynomial.rename_id_apply,
    MvPolynomial.support_rename_of_injective (ltEquiv Dw n).injective,
    Finset.sum_image (fun _ _ _ _ h => Finsupp.mapDomain_injective (ltEquiv Dw n).injective h),
    MvPolynomial.support_map_of_injective _ (algebraMap c.F S).injective] at key
  rw [key, chartVal]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain _ (ltEquiv Dw n).injective, MvPolynomial.coeff_map]
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  refine congrArg (fun z => C.B.nabVal S C.h H.w0 k (f b) C.uvec (MvPolynomial.monomial z 1)) (Finsupp.ext fun ℓ => ?_)
  exact (Finsupp.mapDomain_apply (ltEquiv Dw n).injective m ⟨ℓ.1, ℓ.2, b⟩).symm

omit [StarRing (𝓞 E)] [Algebra ℚ S] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `hs : Function.Surjective (dLin φ).mulVec` using `fun v => by`. Take `⟨a, ha, -⟩` from `hb v`. Use `⟨fun i => a ((ltIdx Dw).symm i), funext fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[← ha j, Matrix.mulVec, dotProduct, ← (ltIdx Dw).sum_comp]`.

Use `Finset.sum_congr rfl fun ℓ _ => ?_` and prove the remaining obligations. Rewrite using `[Equiv.symm_apply_apply, mul_comm, ← h.lin ℓ j]`. Both sides reduce to the same expression. Take `⟨φi, hi⟩` from `GlobalTheory.ChartInv.exists_isInvPair S _ φ h.const ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_surjective_iff_isUnit.1 hs))`. Conclude with `⟨⟨φi, hi.2.1⟩, hi⟩`.

Use `Subtype.ext (funext fun j => ?_)` and prove the remaining obligations. Rewrite using `[op_val, ac_val, ac_val, ac_val]`. Use `Eq.trans ?_ ((h.hom j).trans ?_)` and prove the remaining obligations. Simplify using `only [addOf, ev]`. Use `congr 1`.

Use function extensionality and compare the values at `p`. Take `⟨i, s⟩` from `p`. Apply the tactic sequence `fin_cases i <;> exact CoordLaw.ev_one_eq _ _`. Rewrite using `[comp1, CoordLaw.ev_one_eq]`. Use `congr 1`.
-/
theorem exp_facts (G : FGLaw S (dL Dw)) (uvec : Lt1 Dw → Fin (dL Dw) → S)
    (hb : ∀ v : Fin (dL Dw) → S, ∃! a : Lt1 Dw → S, ∀ j, ∑ ℓ, a ℓ * uvec ℓ j = v j) (φ : Pt S 1 (dL Dw))
    (h : IsExpOf G.F uvec φ) :
    (∃ β : Q S (dL Dw) 1, IsInvPair φ β.1) ∧
    op (FQ G) (ac (⟨φ, h.const⟩ : Q S (dL Dw) 1) (gen 0 : Q S (dL Dw) 2)) (ac ⟨φ, h.const⟩ (gen 1)) =
      ac ⟨φ, h.const⟩ (gen 0 + gen 1) := by
  classical
  constructor
  · have hs : Function.Surjective (dLin φ).mulVec := fun v => by
      obtain ⟨a, ha, -⟩ := hb v
      refine ⟨fun i => a ((ltIdx Dw).symm i), funext fun j => ?_⟩
      rw [← ha j, Matrix.mulVec, dotProduct, ← (ltIdx Dw).sum_comp]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [Equiv.symm_apply_apply, mul_comm, ← h.lin ℓ j]
      rfl
    obtain ⟨φi, hi⟩ := GlobalTheory.ChartInv.exists_isInvPair S _ φ h.const
      ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_surjective_iff_isUnit.1 hs))
    exact ⟨⟨φi, hi.2.1⟩, hi⟩
  · refine Subtype.ext (funext fun j => ?_)
    rw [op_val, ac_val, ac_val, ac_val]
    refine Eq.trans ?_ ((h.hom j).trans ?_)
    · simp only [addOf, ev]
      congr 1
      funext p
      obtain ⟨i, s⟩ := p
      fin_cases i <;> exact CoordLaw.ev_one_eq _ _
    · rw [comp1, CoordLaw.ev_one_eq]
      congr 1

end

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FrameBiextId GlobalTheory.ChartCmp ReciprocityTheory.ChartRestriction.G.TB.WickVanishing Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh in
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct) in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ hs S _ _ _ y C C' k n F f f' hf hf' a P hP`. Establish `hAct` using `expActOf_of GlobalTheory.EigDir.linEig_holds`. Take `⟨φ, hφ, hx⟩` from `expChartOf_of hAct E H Dw l Xo c S y C`. Take `⟨φ', hφ', hx'⟩` from `expChartOf_of hAct E H Dw l Xo c S y C'`. Establish `hxx` using `ExpUniqChart.expUniqTan E H Dw l Xo c S y _ _ hx' hx`.

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

Use `u u' (fun ℓ b => funext fun i => ?_) (fun ℓ => funext fun i => ?_) n _`. Use the proof step `(PullbackSections.harmK_map (algebraMap c.F S) hP.1.1) H.w0 k f f' ε hε`. Use the proof step `(fun b => hge k (F b) (f b) (f' b) ((isGerm_iff y _ _ _ _ _ _ _ _).1 (hf b)) ((isGerm_iff y _ _ _ _ _ _ _ _).1 (hf' b)))`. Use `Eq.trans ?_ (heig b ℓ i)` and prove the remaining obligations. Simplify using `only [Matrix.mulVec, dotProduct, dAct, FB.actK, gt_map_id, dLin]`.

Establish `e0 : comp1 (ac α β').1 φ' = φ` using `(ac_val _ α').symm.trans (congrArg Subtype.val hαα)`. Establish `e1` using `congrFun (congrFun (dLin_comp1 (ac α β').1 φ' hφ'.const) i) (ltIdx Dw ℓ)`. Rewrite `e1` using `[e0, Matrix.mul_apply]`. Rewrite using `[← hφ.lin ℓ i]`. Use `e1.trans (Finset.sum_congr rfl fun j _ => ?_)` and prove the remaining obligations.

Rewrite using `[← hφ'.lin ℓ j]`. Both sides reduce to the same expression.
-/
theorem chartVal_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (S : Type) [Field S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C C' : ChartAt Xo c y) (k n : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S) (f' : Fin n → MvPowerSeries (Fin 1 × Fin C'.d) S), (∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)) → (∀ b, IsGerm y C'.d C'.x C'.B.A.act C'.e C'.wP k (F b) (f' b)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → chartVal C k f P = chartVal C' k f' P := by
  intro E _ _ _ H Dw l Xo c _ hs S _ _ _ y C C' k n F f f' hf hf' a P hP
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
    (PullbackSections.harmK_map (algebraMap c.F S) hP.1.1) H.w0 k f f' ε hε
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

end GlobalTheory.ChartField
