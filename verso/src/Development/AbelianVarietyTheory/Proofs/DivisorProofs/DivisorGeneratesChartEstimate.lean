import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorGeneratorRootExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormBoundedByPositivePotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPotentialSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormUnitLocallyHarmonic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormPotentialSumSmooth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LeviRedInterp

open Filter Topology

/- English proof (translation)
Establish `h` using `GlobalTheory.ChernCompare.formAt_chart P hP hψ j hz hj w`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.formAt at h`. Establish `hpi : (2 / Real.pi : ℝ) ≠ 0` using `by positivity`. Conclude with `mul_left_cancel₀ hpi h`.
-/
theorem levi_compat_eq_leviAt {e : ℕ} {X : Type} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas e X}
    {P : ReciprocityTheory.AnForm.M.LocPot X} (hP : ReciprocityTheory.AnForm.M.IsPotential A P)
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) (j : Fin A.n) {z : Fin e → ℂ}
    (hz : z ∈ ψ.target) (hj : ψ.symm z ∈ (A.chart j).source) (w : Fin e → ℂ) :
    ReciprocityTheory.AnForm.levi (P.φ (ψ.symm z) ∘ ψ.symm) z w =
      GlobalTheory.Mean4O.leviAt A P j (A.chart j (ψ.symm z)) (fderiv ℂ (A.chart j ∘ ψ.symm) z w) := by
  have h := GlobalTheory.ChernCompare.formAt_chart P hP hψ j hz hj w
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.formAt at h
  have hpi : (2 / Real.pi : ℝ) ≠ 0 := by positivity
  exact mul_left_cancel₀ hpi h

section Norms

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {σ : F →+* ℂ} {Δ : Y.Dv}

/- English proof (translation)
Take `⟨b, hb, e⟩` from `exists_pn_eq (C := C) hg`. Establish `hP : 0 < C.pn Y σ Δ m (C.cx Y σ g) p`. Rewrite using `[e m]`. Conclude with `mul_pos hb hp`. Establish `hn : ‖ratVal v p‖ ≠ 0` using `norm_ne_zero_iff.2 (ratVal_ne_zero hv)`.

Simplify using `only [lnN]`. Rewrite using `[C.pn_mul Y σ Δ m v g p hv.regAt hg.regularAt, Real.log_mul (pow_ne_zero 2 hn) hP.ne', Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lnN_unit_mul (m : C.Met Y σ Δ) {g v : Y.Fn} {p : Pts Y σ} (hg : Δ.GeneratesAt (under p) g)
    (hv : UnitAt (under p) v) (hp : PosAt m p) :
    lnN m (v * g) p = lnN m g p + Real.log ‖ratVal v p‖ := by
  obtain ⟨b, hb, e⟩ := exists_pn_eq (C := C) hg
  have hP : 0 < C.pn Y σ Δ m (C.cx Y σ g) p := by
    rw [e m]
    exact mul_pos hb hp
  have hn : ‖ratVal v p‖ ≠ 0 := norm_ne_zero_iff.2 (ratVal_ne_zero hv)
  simp only [lnN]
  rw [C.pn_mul Y σ Δ m v g p hv.regAt hg.regularAt, Real.log_mul (pow_ne_zero 2 hn) hP.ne', Real.log_pow]
  push_cast
  ring

/- English proof (translation)
Establish `e` using `Base.isEqn_eqn Δ x`. Establish `h1` using `e.generatesAt_iff.1 hf`. Establish `h2` using `e.generatesAt_iff.1 hg`. Establish `he : (eqn Δ x : Y.Fn) ≠ 0` using `Units.ne_zero _`. Establish `hg0 : g ≠ 0` using `fun h => h2.ne_zero (by rw [h, zero_mul])`.

Use `⟨?_, (inv_mul_cancel_right₀ hg0 f).symm⟩` and prove the remaining obligations. Establish `h3` using `h1.mul h2.inv`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Clear the denominators using the available nonvanishing facts.
-/
theorem unitAt_mul_inv {x : Y.X} {f g : Y.Fn} (hf : Δ.GeneratesAt x f) (hg : Δ.GeneratesAt x g) :
    UnitAt x (f * g⁻¹) ∧ f = f * g⁻¹ * g := by
  have e := Base.isEqn_eqn Δ x
  have h1 := e.generatesAt_iff.1 hf
  have h2 := e.generatesAt_iff.1 hg
  have he : (eqn Δ x : Y.Fn) ≠ 0 := Units.ne_zero _
  have hg0 : g ≠ 0 := fun h => h2.ne_zero (by rw [h, zero_mul])
  refine ⟨?_, (inv_mul_cancel_right₀ hg0 f).symm⟩
  have h3 := h1.mul h2.inv
  convert h3 using 1
  field_simp

end Norms

end GlobalTheory.LeviRedInterp

open Filter Topology in

/- English proof (translation)
Introduce `p2 ph D O hc hR A T H h c a ψ hψ z hz R hRle u f hf w`. Use `set I := h.man c`. Take `⟨Q, hQ, hlevi⟩` from `(h.an c).th u a`. Use `choose g hg using fun y => (hQ y).1 (ψ.symm z)`. Establish `hgx : ∀ y, _` using `fun y => hg y (ψ.symm z) ((Q y).mem_U _)`.

Establish `hunit : ∀ y, UnitAt (under (I.pt a (ψ.symm z))) (f y * (g y)⁻¹)` using `fun y => (GlobalTheory.LeviRedInterp.unitAt_mul_inv (hf y) (hgx y).1).1`. Establish `hfeq : ∀ y, f y = f y * (g y)⁻¹ * g y` using `fun y => (GlobalTheory.LeviRedInterp.unitAt_mul_inv (hf y) (hgx y).1).2`. Use `choose U0 hU0 hU0u using fun y => (hunit y).exists_nhds`. Use `choose W hWo hxW G hG hGe using fun y => GlobalTheory.Mean4O.log_norm_ratVal_eq_re_holo _ _ _ _ I a (f y * (g y)⁻¹) (ψ.symm z) (hunit y)`. Use `set S : Set ((T.M c).X a) := ⋂ y, ((Q y).U (ψ.symm z) ∩ (I.pt a) ⁻¹' ptsIn _ _ (U0 y) ∩ W y) with hS`.

Establish `hSo : IsOpen S` using `isOpen_iInter_of_finite fun y => (((Q y).isOpen_U _).inter ((isOpen_ptsIn (U0 y)).preimage (I.pt a).continuous)).inter (hWo y)`. Establish `hzS : ψ.symm z ∈ S` using `Set.mem_iInter.2 fun y => ⟨⟨(Q y).mem_U _, mem_ptsIn.2 (hU0 y)⟩, hxW y⟩`. Establish `hN : ψ.target ∩ ψ.symm ⁻¹' S ∈ 𝓝 z` using `(ψ.isOpen_inter_preimage_symm hSo).mem_nhds ⟨hz, hzS⟩`. Establish `hθ : ContDiffAt ℝ 2 (((T.F c).th u a).φ (ψ.symm z) ∘ ψ.symm) z` using `GlobalTheory.ChernCompare.pot_contDiffAt (T.th_pot c u a) hψ _ hz (((T.F c).th u a).mem_U _)`. Establish `hq : ∀ y, ContDiffAt ℝ 2 ((Q y).φ (ψ.symm z) ∘ ψ.symm) z` using `fun y => GlobalTheory.ChernCompare.pot_contDiffAt (hQ y).2 hψ _ hz ((Q y).mem_U _)`.

Establish `hφ : ContDiffAt ℝ 2 ((T.F c).phR R u a ∘ ψ.symm) z`. Establish `h1` using `ReciprocityTheory.AnForm.M.PLAux.contDiffOn_compat hψ isOpen_univ (GlobalTheory.InterpChgSmooth.smooth_phR p2 ph D O hc hR A T H h c u a R hRle)`. Use `(h1.contDiffAt ?_).of_le (WithTop.coe_le_coe.2 le_top)` and prove the remaining obligations. Conclude with `(ψ.isOpen_inter_preimage_symm isOpen_univ).mem_nhds ⟨hz, Set.mem_univ _⟩`. Establish `hGa : ∀ y, AnalyticAt ℂ (G y ∘ ψ.symm) z` using `fun y => ReciprocityTheory.AnForm.M.PLAux.analyticAt_compat_fun hψ (hG y) hz (hxW y)`.

Establish `hRe : ∀ y, ContDiffAt ℝ 2 (fun v => ((G y ∘ ψ.symm) v).re) z` using `fun y => by`. Use `(Complex.reCLM.contDiff (n := 2)).contDiffAt.comp z ((hGa y).restrictScalars (𝕜 := ℝ)).contDiffAt` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Use `set φ : DV.Rt D.what₂.Tau O.N → (Fin (WeightThresholdDefs.dimY O.Y) → ℂ) → ℝ := fun y v => ((G y ∘ ψ.symm) v).re + (-1) * ((Q y).φ (ψ.symm z) ∘ ψ.symm) v with hφdef`. Establish `hφy : ∀ y, ContDiffAt ℝ 2 (φ y) z` using `fun y => (hRe y).add (contDiffAt_const.mul (hq y))`.

Establish `hlφ : ∀ y, ReciprocityTheory.AnForm.levi (φ y) z w = -ReciprocityTheory.AnForm.levi ((Q y).φ (ψ.symm z) ∘ ψ.symm) z w`. Introduce `y`. Rewrite using `[hφdef, ReciprocityTheory.AnForm.levi_add_smul (-1) (hRe y) (hq y) w, ReciprocityTheory.AnForm.levi_re_analytic (hGa y)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hEq : (fun v => ∑ y : DV.Rt D.what₂.Tau O.N, u y.1 y.2 * lnN (O.met.hm c (some R) (I.ε a) (O.ex y)) (f y) (I.pt a (ψ.symm v))) =ᶠ[𝓝 z] fun v => ((T.F c).phR R u a ∘ ψ.symm) v + ∑ y : DV.Rt D.what₂.Tau O.N, u y.1 y.2 * φ y v` using `by filter_upwards [hN] with v hv`.

Establish `hvS : ∀ y, ψ.symm v ∈ (Q y).U (ψ.symm z) ∩ (I.pt a) ⁻¹' ptsIn _ _ (U0 y) ∩ W y` using `fun y => Set.mem_iInter.1 hv.2 y`. Simplify using `only [Function.comp_apply, hφdef]`. Rewrite using `[show (T.F c).phR R u a (ψ.symm v) = O.chg c (some R) u (I.ε a) (I.pt a (ψ.symm v)) from (h.an c).phR R hRle u a (ψ.symm v)]`. Unfold `Setup.chg`. Rewrite using `[← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Take `⟨⟨hvQ, hvU⟩, hvW⟩` from `hvS y`. Establish `hgv` using `hg y _ hvQ`. Establish `e1` using `GlobalTheory.LeviRedInterp.lnN_unit_mul (O.met.hm c (some R) (I.ε a) (O.ex y)) hgv.1 (hU0u y _ (mem_ptsIn.1 hvU)) (hc.posAt_hm c _ (some R) _ _)`. Rewrite `e1` using `[← hfeq y]`.

Rewrite using `[e1, lnRatio_eq hgv.1 (hc.posAt_hm c _ (some R) _ _) (hc.referenceMetric_posAt c _ _ _), hgv.2.2, hGe y _ hvW]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨j, hj⟩` from `((T.M c).A a).cover (ψ.symm z)`. Establish `hy' : ((T.M c).A a).chart j (ψ.symm z) ∈ (((T.M c).A a).chart j).target` using `(((T.M c).A a).chart j).map_source hj`. Establish `hθl : ReciprocityTheory.AnForm.levi (((T.F c).th u a).φ (ψ.symm z) ∘ ψ.symm) z w = ∑ y : DV.Rt D.what₂.Tau O.N, -u y.1 y.2 * ReciprocityTheory.AnForm.levi ((Q y).φ (ψ.symm z) ∘ ψ.symm) z w`.

Rewrite using `[GlobalTheory.LeviRedInterp.levi_compat_eq_leviAt (T.th_pot c u a) hψ j hz hj w, hlevi j _ hy']`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.LeviRedInterp.levi_compat_eq_leviAt (hQ y).2 hψ j hz hj w]`. Establish `hsum : ContDiffAt ℝ 2 (fun v => ∑ y : DV.Rt D.what₂.Tau O.N, u y.1 y.2 * φ y v) z` using `ContDiffAt.sum fun y _ => contDiffAt_const.mul (hφy y)`. Express the relevant statement in the definitionally equal form `ReciprocityTheory.AnForm.levi (fun v => (((T.F c).th u a).φ (ψ.symm z) ∘ ψ.symm) v + ((T.F c).phR R u a ∘ ψ.symm) v) z w = _`.

Rewrite using `[GlobalTheory.LeviRed.levi_add hθ hφ, GlobalTheory.LeviRed.levi_congr hEq, GlobalTheory.LeviRed.levi_add hφ hsum, GlobalTheory.LeviRelation.levi_sum_mul Finset.univ _ φ (fun y _ => hφy y), hθl]`. Simplify using `only [hlφ, neg_mul, mul_neg, Finset.sum_neg_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.LeviRedInterp.levi_th_add_phR : Hypotheses2 → HypothesesH → OnObj fun D O _ T _ h => ∀ (c : O.Y.Comp) (a : Fin ((T.M c).n + 1)) (ψ : OpenPartialHomeomorph ((T.M c).X a) (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ)), IsCompatChart ((T.M c).A a) ψ → ∀ z ∈ ψ.target, ∀ R : ℝ, 2 ≤ R → ∀ (u : D.what₂.Tau → Fin O.Y.N → ℝ) (f : DV.Rt D.what₂.Tau O.N → (O.var c).Fn), (∀ y, (GlobalTheory.ShFam.Pad.divOf (O.Φ.C c) (O.ex y)).GeneratesAt (under ((h.man c).pt a (ψ.symm z))) (f y)) → ∀ w, levi (((T.F c).th u a + LocPot.ofFun ((T.F c).phR R u a)).φ (ψ.symm z) ∘ ψ.symm) z w = levi (fun v => ∑ y : DV.Rt D.what₂.Tau O.N, u y.1 y.2 * lnN (O.met.hm c (some R) ((h.man c).ε a) (O.ex y)) (f y) ((h.man c).pt a (ψ.symm v))) z w := by
  intro p2 ph D O hc hR A T H h c a ψ hψ z hz R hRle u f hf w
  set I := h.man c
  obtain ⟨Q, hQ, hlevi⟩ := (h.an c).th u a
  choose g hg using fun y => (hQ y).1 (ψ.symm z)
  have hgx : ∀ y, _ := fun y => hg y (ψ.symm z) ((Q y).mem_U _)
  have hunit : ∀ y, UnitAt (under (I.pt a (ψ.symm z))) (f y * (g y)⁻¹) := fun y =>
    (GlobalTheory.LeviRedInterp.unitAt_mul_inv (hf y) (hgx y).1).1
  have hfeq : ∀ y, f y = f y * (g y)⁻¹ * g y := fun y => (GlobalTheory.LeviRedInterp.unitAt_mul_inv (hf y) (hgx y).1).2
  choose U0 hU0 hU0u using fun y => (hunit y).exists_nhds
  choose W hWo hxW G hG hGe using fun y =>
    GlobalTheory.Mean4O.log_norm_ratVal_eq_re_holo _ _ _ _ I a (f y * (g y)⁻¹) (ψ.symm z) (hunit y)

  set S : Set ((T.M c).X a) := ⋂ y, ((Q y).U (ψ.symm z) ∩ (I.pt a) ⁻¹' ptsIn _ _ (U0 y) ∩ W y) with hS
  have hSo : IsOpen S := isOpen_iInter_of_finite fun y =>
    (((Q y).isOpen_U _).inter ((isOpen_ptsIn (U0 y)).preimage (I.pt a).continuous)).inter (hWo y)
  have hzS : ψ.symm z ∈ S := Set.mem_iInter.2 fun y => ⟨⟨(Q y).mem_U _, mem_ptsIn.2 (hU0 y)⟩, hxW y⟩
  have hN : ψ.target ∩ ψ.symm ⁻¹' S ∈ 𝓝 z := (ψ.isOpen_inter_preimage_symm hSo).mem_nhds ⟨hz, hzS⟩

  have hθ : ContDiffAt ℝ 2 (((T.F c).th u a).φ (ψ.symm z) ∘ ψ.symm) z :=
    GlobalTheory.ChernCompare.pot_contDiffAt (T.th_pot c u a) hψ _ hz (((T.F c).th u a).mem_U _)
  have hq : ∀ y, ContDiffAt ℝ 2 ((Q y).φ (ψ.symm z) ∘ ψ.symm) z := fun y =>
    GlobalTheory.ChernCompare.pot_contDiffAt (hQ y).2 hψ _ hz ((Q y).mem_U _)
  have hφ : ContDiffAt ℝ 2 ((T.F c).phR R u a ∘ ψ.symm) z := by
    have h1 := ReciprocityTheory.AnForm.M.PLAux.contDiffOn_compat hψ isOpen_univ
      (GlobalTheory.InterpChgSmooth.smooth_phR p2 ph D O hc hR A T H h c u a R hRle)
    refine (h1.contDiffAt ?_).of_le (WithTop.coe_le_coe.2 le_top)
    exact (ψ.isOpen_inter_preimage_symm isOpen_univ).mem_nhds ⟨hz, Set.mem_univ _⟩
  have hGa : ∀ y, AnalyticAt ℂ (G y ∘ ψ.symm) z := fun y =>
    ReciprocityTheory.AnForm.M.PLAux.analyticAt_compat_fun hψ (hG y) hz (hxW y)
  have hRe : ∀ y, ContDiffAt ℝ 2 (fun v => ((G y ∘ ψ.symm) v).re) z := fun y => by
    have := (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp z ((hGa y).restrictScalars (𝕜 := ℝ)).contDiffAt
    simpa [Function.comp_def] using this

  set φ : DV.Rt D.what₂.Tau O.N → (Fin (WeightThresholdDefs.dimY O.Y) → ℂ) → ℝ := fun y v =>
    ((G y ∘ ψ.symm) v).re + (-1) * ((Q y).φ (ψ.symm z) ∘ ψ.symm) v with hφdef
  have hφy : ∀ y, ContDiffAt ℝ 2 (φ y) z := fun y => (hRe y).add (contDiffAt_const.mul (hq y))
  have hlφ : ∀ y, ReciprocityTheory.AnForm.levi (φ y) z w = -ReciprocityTheory.AnForm.levi ((Q y).φ (ψ.symm z) ∘ ψ.symm) z w := by
    intro y
    rw [hφdef, ReciprocityTheory.AnForm.levi_add_smul (-1) (hRe y) (hq y) w, ReciprocityTheory.AnForm.levi_re_analytic (hGa y)]
    ring

  have hEq : (fun v => ∑ y : DV.Rt D.what₂.Tau O.N, u y.1 y.2 *
      lnN (O.met.hm c (some R) (I.ε a) (O.ex y)) (f y) (I.pt a (ψ.symm v))) =ᶠ[𝓝 z]
      fun v => ((T.F c).phR R u a ∘ ψ.symm) v + ∑ y : DV.Rt D.what₂.Tau O.N, u y.1 y.2 * φ y v := by
    filter_upwards [hN] with v hv
    have hvS : ∀ y, ψ.symm v ∈ (Q y).U (ψ.symm z) ∩ (I.pt a) ⁻¹' ptsIn _ _ (U0 y) ∩ W y := fun y =>
      Set.mem_iInter.1 hv.2 y
    simp only [Function.comp_apply, hφdef]
    rw [show (T.F c).phR R u a (ψ.symm v) = O.chg c (some R) u (I.ε a) (I.pt a (ψ.symm v)) from
      (h.an c).phR R hRle u a (ψ.symm v)]
    unfold Setup.chg
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    obtain ⟨⟨hvQ, hvU⟩, hvW⟩ := hvS y
    have hgv := hg y _ hvQ
    have e1 := GlobalTheory.LeviRedInterp.lnN_unit_mul (O.met.hm c (some R) (I.ε a) (O.ex y)) hgv.1
      (hU0u y _ (mem_ptsIn.1 hvU)) (hc.posAt_hm c _ (some R) _ _)
    rw [← hfeq y] at e1
    rw [e1, lnRatio_eq hgv.1 (hc.posAt_hm c _ (some R) _ _) (hc.referenceMetric_posAt c _ _ _), hgv.2.2, hGe y _ hvW]
    ring

  obtain ⟨j, hj⟩ := ((T.M c).A a).cover (ψ.symm z)
  have hy' : ((T.M c).A a).chart j (ψ.symm z) ∈ (((T.M c).A a).chart j).target :=
    (((T.M c).A a).chart j).map_source hj
  have hθl : ReciprocityTheory.AnForm.levi (((T.F c).th u a).φ (ψ.symm z) ∘ ψ.symm) z w =
      ∑ y : DV.Rt D.what₂.Tau O.N, -u y.1 y.2 * ReciprocityTheory.AnForm.levi ((Q y).φ (ψ.symm z) ∘ ψ.symm) z w := by
    rw [GlobalTheory.LeviRedInterp.levi_compat_eq_leviAt (T.th_pot c u a) hψ j hz hj w, hlevi j _ hy']
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [GlobalTheory.LeviRedInterp.levi_compat_eq_leviAt (hQ y).2 hψ j hz hj w]
  have hsum : ContDiffAt ℝ 2 (fun v => ∑ y : DV.Rt D.what₂.Tau O.N, u y.1 y.2 * φ y v) z :=
    ContDiffAt.sum fun y _ => contDiffAt_const.mul (hφy y)
  change ReciprocityTheory.AnForm.levi (fun v => (((T.F c).th u a).φ (ψ.symm z) ∘ ψ.symm) v +
    ((T.F c).phR R u a ∘ ψ.symm) v) z w = _
  rw [GlobalTheory.LeviRed.levi_add hθ hφ, GlobalTheory.LeviRed.levi_congr hEq, GlobalTheory.LeviRed.levi_add hφ hsum,
    GlobalTheory.LeviRelation.levi_sum_mul Finset.univ _ φ (fun y _ => hφy y), hθl]
  simp only [hlφ, neg_mul, mul_neg, Finset.sum_neg_distrib]
  ring
