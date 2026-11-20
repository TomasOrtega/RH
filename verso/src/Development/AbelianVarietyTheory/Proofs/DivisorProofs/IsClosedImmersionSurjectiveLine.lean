import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSmallSecTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ArInt

noncomputable section

namespace GlobalTheory.FlagZ.Plane

/- English proof (translation)
Introduce `k _ X p σ D U hU x hb`. Set `e` to `RingEquiv.ofBijective _ hb`. Establish `he (P) : e.symm (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) x P) = P` using `e.symm_apply_apply P`. Set `s (v : ReciprocityTheory.L2DbarEstimates.V D) : CxPts p σ` to `ofHom hU ((MvPolynomial.eval₂Hom σ fun a => v a).comp e.symm.toRingHom) fun a => by`. Use `he (MvPolynomial.C a)` as an intermediate fact.

Rewrite `this` using `[MvPolynomial.eval₂Hom_C]`. Conclude with `(congrArg _ this).trans (MvPolynomial.eval₂Hom_C _ _ a)`. Establish `hs (v) : s v ∈ ptsIn p σ U` using `ofHom_mem _ _ _`. Establish `hev (v) (P) : CxPts.ev p σ U (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) x P) (s v) = MvPolynomial.eval₂Hom σ (fun a => v a) P` using `(ev_ofHom _ _ _ _).trans (congrArg (MvPolynomial.eval₂Hom σ fun a => v a) (he P))`. Establish `hd (a : Γ(X, U)) : DifferentiableOn ℂ (CxPts.ev p σ U a ∘ s) Set.univ`.

Take `⟨P, rfl⟩` from `hb.2 a`. Use `Differentiable.differentiableOn ?_` and prove the remaining obligations. Rewrite using `[show CxPts.ev p σ U (MvPolynomial.eval₂Hom _ x P) ∘ s = fun v : ReciprocityTheory.L2DbarEstimates.V D => MvPolynomial.eval₂Hom σ (fun a => v a) P from funext fun v => hev v P]`. Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => simp`.

Consider the case `add p q hp hq`. Simplify using `only [map_add]`. Conclude with `hp.add hq`. Consider the case `mul_X p n hp`. Simplify using `only [map_mul, MvPolynomial.eval₂Hom_X']`.

Conclude with `hp.mul (EuclideanSpace.proj (𝕜 := ℂ) n : ReciprocityTheory.L2DbarEstimates.V D →L[ℂ] ℂ).differentiable`. Establish `hh` using `holo_of_affine hU isOpen_univ (fun v _ => hs v) hd`. Use `⟨⟨{ toFun := fun z => WithLp.toLp 2 fun a => CxPts.ev p σ U (x a) z invFun := s source := ptsIn p σ U target := Set.univ map_source' := fun _ _ => trivial map_target' := fun v _ => hs v left_inv' := fun z hz => Subtype.ext (ext_of_valR hU (hs _) hz fun a => ?_) right_inv' := fun …` and prove the remaining obligations. Take `⟨P, rfl⟩` from `hb.2 a`. Use `(hev _ P).trans (Eq.trans ?_ (ev_eq hz _).symm)` and prove the remaining obligations.

Use `RingHom.congr_fun (g := (evHom hz).comp (MvPolynomial.eval₂Hom _ x)) (MvPolynomial.ringHom_ext (fun c => ?_) fun c => ?_) P` and prove the remaining obligations. Rewrite using `[MvPolynomial.eval₂Hom_C, RingHom.comp_apply, ← ev_eq, MvPolynomial.eval₂Hom_C]`. Conclude with `(ev_algX hz c).symm`. Rewrite using `[MvPolynomial.eval₂Hom_X', RingHom.comp_apply, ← ev_eq, MvPolynomial.eval₂Hom_X']`. Use extensionality with `a`.

Use `hev v (MvPolynomial.X a)` as an intermediate fact. Rewrite `this` using `[MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']`. Then use the resulting hypothesis.
-/
theorem exists_chart_of_bijective : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (U : X.Opens) (_ : IsAffineOpen U) (x : Fin D → Γ(X, U)), Function.Bijective (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) x) → ∃ c : AlgChart p σ D, c.e.source = ptsIn p σ U ∧ c.e.target = Set.univ ∧ ∀ y ∈ c.e.source, ∀ a, c.e y a = CxPts.ev p σ U (x a) y := by
  intro k _ X p σ D U hU x hb
  let e := RingEquiv.ofBijective _ hb
  have he (P) : e.symm (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) x P) = P := e.symm_apply_apply P
  let s (v : ReciprocityTheory.L2DbarEstimates.V D) : CxPts p σ :=
    ofHom hU ((MvPolynomial.eval₂Hom σ fun a => v a).comp e.symm.toRingHom) fun a => by
      have := he (MvPolynomial.C a)
      rw [MvPolynomial.eval₂Hom_C] at this
      exact (congrArg _ this).trans (MvPolynomial.eval₂Hom_C _ _ a)
  have hs (v) : s v ∈ ptsIn p σ U := ofHom_mem _ _ _
  have hev (v) (P) : CxPts.ev p σ U (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) x P) (s v) =
      MvPolynomial.eval₂Hom σ (fun a => v a) P := (ev_ofHom _ _ _ _).trans (congrArg (MvPolynomial.eval₂Hom σ fun a => v a) (he P))
  have hd (a : Γ(X, U)) : DifferentiableOn ℂ (CxPts.ev p σ U a ∘ s) Set.univ := by
    obtain ⟨P, rfl⟩ := hb.2 a
    refine Differentiable.differentiableOn ?_
    rw [show CxPts.ev p σ U (MvPolynomial.eval₂Hom _ x P) ∘ s = fun v : ReciprocityTheory.L2DbarEstimates.V D =>
      MvPolynomial.eval₂Hom σ (fun a => v a) P from funext fun v => hev v P]
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq =>
      simp only [map_add]
      exact hp.add hq
    | mul_X p n hp =>
      simp only [map_mul, MvPolynomial.eval₂Hom_X']
      exact hp.mul (EuclideanSpace.proj (𝕜 := ℂ) n : ReciprocityTheory.L2DbarEstimates.V D →L[ℂ] ℂ).differentiable
  have hh := holo_of_affine hU isOpen_univ (fun v _ => hs v) hd
  refine ⟨⟨{ toFun := fun z => WithLp.toLp 2 fun a => CxPts.ev p σ U (x a) z
             invFun := s
             source := ptsIn p σ U
             target := Set.univ
             map_source' := fun _ _ => trivial
             map_target' := fun v _ => hs v
             left_inv' := fun z hz => Subtype.ext (ext_of_valR hU (hs _) hz fun a => ?_)
             right_inv' := fun v _ => ?_
             open_source := isOpen_ptsIn _
             open_target := isOpen_univ
             continuousOn_toFun := (PiLp.continuous_toLp 2 _).comp_continuousOn
               (continuousOn_pi.2 fun a => continuousOn_ev _)
             continuousOn_invFun := hh.1 }, U, hU, x, RingHom.Etale.of_bijective hb, fun _ h => h, fun _ _ _ => rfl,
    hh.2⟩, rfl, rfl, fun _ _ _ => rfl⟩
  · obtain ⟨P, rfl⟩ := hb.2 a
    refine (hev _ P).trans (Eq.trans ?_ (ev_eq hz _).symm)
    refine RingHom.congr_fun (g := (evHom hz).comp (MvPolynomial.eval₂Hom _ x))
      (MvPolynomial.ringHom_ext (fun c => ?_) fun c => ?_) P
    · rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, ← ev_eq, MvPolynomial.eval₂Hom_C]
      exact (ev_algX hz c).symm
    · rw [MvPolynomial.eval₂Hom_X', RingHom.comp_apply, ← ev_eq, MvPolynomial.eval₂Hom_X']
  · ext a
    have := hev v (MvPolynomial.X a)
    rwa [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X'] at this

/- English proof (translation)
Establish `hd : Module.finrank ℝ (ReciprocityTheory.L2DbarEstimates.V 1) = 2`. Rewrite using `[← Module.finrank_mul_finrank ℝ ℂ (ReciprocityTheory.L2DbarEstimates.V 1)]`. Simplify using the standard rewrite rules. Establish `hu (v : ReciprocityTheory.L2DbarEstimates.V 1) : ArithHeightModel.u v = 1 + ‖v‖ ^ 2`. Rewrite using `[ArithHeightModel.u, EuclideanSpace.norm_sq_eq, Fin.sum_univ_one, Complex.sq_norm, Complex.normSq_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `: Nontrivial (ReciprocityTheory.L2DbarEstimates.V 1)` using `inferInstance`. Establish `h` using `integral_fun_norm_addHaar (volume : Measure (ReciprocityTheory.L2DbarEstimates.V 1)) (fun r => 1 / Real.pi * ((1 + r ^ 2) ^ 2)⁻¹ * Real.log (1 + r ^ 2))`. Establish `hr : ∫ r in Set.Ioi (0 : ℝ), r * (((1 + r ^ 2) ^ 2)⁻¹ * Real.log (1 + r ^ 2)) = 0 - -(1 / 2 * (Real.log (1 + (0 : ℝ) ^ 2) / (1 + (0 : ℝ) ^ 2) + (1 + (0 : ℝ) ^ 2)⁻¹))`. Use `integral_Ioi_of_hasDerivAt_of_nonneg' (g := fun r => -(1 / 2 * (Real.log (1 + r ^ 2) / (1 + r ^ 2) + (1 + r ^ 2)⁻¹))) (fun r _ => ?_) (fun r hr => mul_nonneg (le_of_lt hr) (mul_nonneg (by positivity) (Real.log_nonneg (le_add_of_nonneg_right (sq_nonneg r))))) ?_` and prove the remaining obligations.

Establish `h0 : (1 + r ^ 2) ≠ 0` using `by positivity`. Establish `h1` using `(hasDerivAt_pow 2 r).const_add 1`. Use `HasDerivAt.congr_deriv (((((h1.log h0).div h1 h0).add (h1.inv h0)).const_mul (1 / 2)).neg) ?_` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Establish `ht : Filter.Tendsto (fun r : ℝ => 1 + r ^ 2) Filter.atTop Filter.atTop` using `Filter.tendsto_atTop_add_const_left _ 1 (Filter.tendsto_pow_atTop two_ne_zero)`. Use `(((Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ht).add (tendsto_inv_atTop_zero.comp ht)).const_mul (1 / 2)).neg` as an intermediate fact. Simplify using `using this`. Simplify using `only [hu]`.

Rewrite using `[h, hd, Measure.real, AnReadModel.volume_ball_one, ENNReal.toReal_ofReal Real.pi_pos.le]`. Simplify using `only [smul_eq_mul, Nat.reduceSub, pow_one, mul_assoc (1 / Real.pi), mul_left_comm _ (1 / Real.pi), integral_const_mul, hr]`. Use `Real.pi_pos` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Evaluate the numerical expressions.
-/
theorem integral_log_dens : ∫ v : ReciprocityTheory.L2DbarEstimates.V 1, 1 / Real.pi * (ArithHeightModel.u v ^ 2)⁻¹ * Real.log (ArithHeightModel.u v) = 1 := by
  have hd : Module.finrank ℝ (ReciprocityTheory.L2DbarEstimates.V 1) = 2 := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (ReciprocityTheory.L2DbarEstimates.V 1)]; simp
  have hu (v : ReciprocityTheory.L2DbarEstimates.V 1) : ArithHeightModel.u v = 1 + ‖v‖ ^ 2 := by
    rw [ArithHeightModel.u, EuclideanSpace.norm_sq_eq, Fin.sum_univ_one, Complex.sq_norm, Complex.normSq_apply]
    ring
  have : Nontrivial (ReciprocityTheory.L2DbarEstimates.V 1) := inferInstance
  have h := integral_fun_norm_addHaar (volume : Measure (ReciprocityTheory.L2DbarEstimates.V 1))
    (fun r => 1 / Real.pi * ((1 + r ^ 2) ^ 2)⁻¹ * Real.log (1 + r ^ 2))
  have hr : ∫ r in Set.Ioi (0 : ℝ), r * (((1 + r ^ 2) ^ 2)⁻¹ * Real.log (1 + r ^ 2)) =
      0 - -(1 / 2 * (Real.log (1 + (0 : ℝ) ^ 2) / (1 + (0 : ℝ) ^ 2) + (1 + (0 : ℝ) ^ 2)⁻¹)) := by
    refine integral_Ioi_of_hasDerivAt_of_nonneg'
      (g := fun r => -(1 / 2 * (Real.log (1 + r ^ 2) / (1 + r ^ 2) + (1 + r ^ 2)⁻¹)))
      (fun r _ => ?_) (fun r hr => mul_nonneg (le_of_lt hr) (mul_nonneg (by positivity)
        (Real.log_nonneg (le_add_of_nonneg_right (sq_nonneg r))))) ?_
    · have h0 : (1 + r ^ 2) ≠ 0 := by positivity
      have h1 := (hasDerivAt_pow 2 r).const_add 1
      refine HasDerivAt.congr_deriv (((((h1.log h0).div h1 h0).add (h1.inv h0)).const_mul (1 / 2)).neg) ?_
      field_simp
      simp
      ring
    · have ht : Filter.Tendsto (fun r : ℝ => 1 + r ^ 2) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_add_const_left _ 1 (Filter.tendsto_pow_atTop two_ne_zero)
      have := (((Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ht).add
        (tendsto_inv_atTop_zero.comp ht)).const_mul (1 / 2)).neg
      simpa using this
  simp only [hu]
  rw [h, hd, Measure.real, AnReadModel.volume_ball_one, ENNReal.toReal_ofReal Real.pi_pos.le]
  simp only [smul_eq_mul, Nat.reduceSub, pow_one, mul_assoc (1 / Real.pi), mul_left_comm _ (1 / Real.pi), integral_const_mul, hr]
  have := Real.pi_pos
  field_simp
  norm_num

/- English proof (translation)
Establish `hm` using `(c.e.symm.isOpenEmbedding ht).measurableEmbedding`. Establish `key (ε : ℤˣ) : (φ.chernPart D ε).restrict c.e.source = (volume.withDensity fun v => ENNReal.ofReal ((ε : ℤ) * ρ v)).map c.e.symm`. Use extensionality with `T hT`. Rewrite using `[Measure.restrict_apply hT, Weight.chernPart_apply h ε c (hT.inter c.e.open_source.measurableSet) Set.inter_subset_right, hm.map_apply, withDensity_apply _ (hm.measurable hT), Set.inter_comm, c.e.image_source_inter_eq', ht, Set.univ_inter]`. Simplify using `only [hc]`.

Establish `hi (ε : ℤˣ) : ∫ y in c.e.source, f y ∂φ.chernPart D ε = ∫ v, (ENNReal.ofReal ((ε : ℤ) * ρ v)).toReal • f (c.e.symm v)`. Rewrite using `[key, hm.integral_map, integral_withDensity_eq_integral_toReal_smul (hρ.measurable.const_mul _).ennreal_ofReal (.of_forall fun _ => ENNReal.ofReal_lt_top)]`. Rewrite using `[Weight.chernInt, hi, hi]`. Simplify using `[ENNReal.ofReal_of_nonpos (neg_nonpos.2 (h0 _)), ENNReal.toReal_ofReal (h0 _)]`.
-/
theorem chernInt_chart {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB X}
    [SecondCountableTopology (CxPts p σ)] {φ : Weight p σ B} (h : φ.IsCInf) (c : AlgChart p σ D)
    (ht : c.e.target = Set.univ) {ρ : ReciprocityTheory.L2DbarEstimates.V D → ℝ} (hρ : Continuous ρ) (h0 : ∀ v, 0 ≤ ρ v)
    (hc : ∀ v, c.chernDens φ (c.e.symm v) = ρ v) (f : CxPts p σ → ℝ) :
    φ.chernInt D c.e.source f = ∫ v, ρ v * f (c.e.symm v) := by
  have hm := (c.e.symm.isOpenEmbedding ht).measurableEmbedding
  have key (ε : ℤˣ) : (φ.chernPart D ε).restrict c.e.source =
      (volume.withDensity fun v => ENNReal.ofReal ((ε : ℤ) * ρ v)).map c.e.symm := by
    ext T hT
    rw [Measure.restrict_apply hT, Weight.chernPart_apply h ε c (hT.inter c.e.open_source.measurableSet)
      Set.inter_subset_right, hm.map_apply, withDensity_apply _ (hm.measurable hT), Set.inter_comm,
      c.e.image_source_inter_eq', ht, Set.univ_inter]
    simp only [hc]
  have hi (ε : ℤˣ) : ∫ y in c.e.source, f y ∂φ.chernPart D ε =
      ∫ v, (ENNReal.ofReal ((ε : ℤ) * ρ v)).toReal • f (c.e.symm v) := by
    rw [key, hm.integral_map, integral_withDensity_eq_integral_toReal_smul
      (hρ.measurable.const_mul _).ennreal_ofReal (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [Weight.chernInt, hi, hi]
  simp [ENNReal.ofReal_of_nonpos (neg_nonpos.2 (h0 _)), ENNReal.toReal_ofReal (h0 _)]

/- English proof (translation)
Introduce `k _ σ`. Set `e : MvPolynomial (Fin 1) k ≃ₐ[k] Γ(PSpace k 1, chart k 1 0)` to `(MvPolynomial.renameEquiv k (finSuccAboveEquiv 0)).trans (chartAlgEquiv k 1 0)`. Establish `he : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (PSpace.str k 1) (chart k 1 0)) (fun a => ratio k 1 0 ((0 : Fin 2).succAbove a)) = (e : MvPolynomial (Fin 1) k →+* _)` using `MvPolynomial.ringHom_ext (fun a => (MvPolynomial.eval₂Hom_C _ _ a).trans (e.commutes a).symm) fun b => (MvPolynomial.eval₂Hom_X' _ _ b).trans ((congrArg (chartAlgEquiv k 1 0) (MvPolynomial.rename_X _ b)).trans (chartAlgEquiv_X k 1 0 (finSuccAboveEquiv 0 b))).symm`. Take `⟨c, hs, ht, hx⟩` from `exists_chart_of_bijective k _ (PSpace.str k 1) σ 1 _ (isAffineOpen_chart k 1 0) (fun a => ratio k 1 0 ((0 : Fin 2).succAbove a)) (by rw [he]; exact e.bijective)`. Establish `hm (v) : c.e.symm v ∈ c.e.source` using `c.e.map_target (ht ▸ trivial)`.

Establish `hr (v) : c.e (c.e.symm v) = v` using `c.e.right_inv (ht ▸ trivial)`. Establish `h1 (v) : CxPts.ev _ σ (chart k 1 0) (ratio k 1 0 0) (c.e.symm v) = 1`. Rewrite using `[ev_eq (hs ▸ hm v), ratio, ratioOn_self, map_one]`. Establish `h2 (v) : CxPts.ev _ σ (chart k 1 0) (ratio k 1 0 1) (c.e.symm v) = v 0` using `(hx _ (hm v) 0).symm.trans (by rw [hr])`. Establish `hφ (v) : (ProjAn.fsO1 k σ 1).φ (0 : Fin 2) (c.e.symm v) = Real.log (ArithHeightModel.u v)`.

Use `(Weight.fsBasis_φ _ _ _ _ _ _ _).trans (congrArg _ ?_)` and prove the remaining obligations. Simplify using `only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Use `(Fin.sum_univ_two _).trans ((congrArg₂ (fun a b : ℂ => ‖a‖ ^ 2 + ‖b‖ ^ 2) (h1 v) (h2 v)).trans ?_)` and prove the remaining obligations. Simplify using `only [norm_one, one_pow, ArithHeightModel.u, Complex.sq_norm, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hi : (ProjAn.fsO1 k σ 1).IsCInf` using `(hermitianTwistingSheaf k 1).cInf σ`. Establish `hu : Continuous ArithHeightModel.u` using `continuous_iff_continuousAt.2 fun v => (ArithHeightModel.hasFDerivAt_u v).continuousAt`. Use `CxPts.secondCountableTopology_of_isProjOver σ (isProjOver_pspace_str k 1)` as an intermediate fact. Rewrite using `[← hs, chernInt_chart hi c ht (ρ := fun v => 1 / Real.pi * (ArithHeightModel.u v ^ 2)⁻¹) (continuous_const.mul ((hu.pow 2).inv₀ fun v => (pow_pos (ArithHeightModel.u_pos v) 2).ne')) (fun v => by have := Real.pi_pos; positivity) fun v => ?_]`. Establish `hn (v) : (ProjAn.fsO1 k σ 1).nsq (secVal (PSpace.str k 1) σ (ProjSpace.coord k 1 0)) (c.e.symm v) = Real.exp (-Real.log (ArithHeightModel.u v))`.

Use `(Weight.nsq_eq _ (secVal_mem _) (i := (0 : Fin 2)) (hs ▸ hm v)).trans ?_` and prove the remaining obligations. Rewrite using `[hφ]`. Conclude with `(congrArg (fun a : ℂ => ‖a‖ ^ 2 * _) (h1 v)).trans (by simp)`. Simplify using `only [hn, Real.log_exp]`. Rewrite using `[← mul_one (-(1 / 2) : ℝ), ← integral_log_dens, ← integral_const_mul]`.

Conclude with `integral_congr_ae (.of_forall fun v => by ring)`. Rewrite using `[c.chernDens_eq hi (hm v) (i := (0 : Fin 2)) (hs ▸ hm v), Matrix.det_unique]`. Establish `e₁ : c.hess (ProjAn.fsO1 k σ 1) (0 : Fin 2) (c.e.symm v) default default = ((ArithHeightModel.u v ^ 2)⁻¹ : ℝ)` using `(congrArg₂ (fun F w => ReciprocityTheory.L2DbarEstimates.cHess 1 F w 0 0) (funext fun w => congrArg _ (hφ w)) (hr v)).trans (ArithHeightModel.cHess_log v)`. Rewrite using `[e₁, Complex.ofReal_re]`. Simplify using the standard rewrite rules.
-/
theorem chernInt_log_coord : ∀ (k : Type) [CommRing k] (σ : k →+* ℂ), (ProjAn.fsO1 k σ 1).chernInt 1 (ptsIn (PSpace.str k 1) σ (chart k 1 0)) (fun y => Real.log ((ProjAn.fsO1 k σ 1).nsq (secVal (PSpace.str k 1) σ (ProjSpace.coord k 1 0)) y) / 2) = -(1 / 2) := by
  intro k _ σ
  let e : MvPolynomial (Fin 1) k ≃ₐ[k] Γ(PSpace k 1, chart k 1 0) :=
    (MvPolynomial.renameEquiv k (finSuccAboveEquiv 0)).trans (chartAlgEquiv k 1 0)
  have he : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (PSpace.str k 1) (chart k 1 0))
      (fun a => ratio k 1 0 ((0 : Fin 2).succAbove a)) = (e : MvPolynomial (Fin 1) k →+* _) :=
    MvPolynomial.ringHom_ext (fun a => (MvPolynomial.eval₂Hom_C _ _ a).trans (e.commutes a).symm)
      fun b => (MvPolynomial.eval₂Hom_X' _ _ b).trans
        ((congrArg (chartAlgEquiv k 1 0) (MvPolynomial.rename_X _ b)).trans
          (chartAlgEquiv_X k 1 0 (finSuccAboveEquiv 0 b))).symm
  obtain ⟨c, hs, ht, hx⟩ := exists_chart_of_bijective k _ (PSpace.str k 1) σ 1 _ (isAffineOpen_chart k 1 0)
    (fun a => ratio k 1 0 ((0 : Fin 2).succAbove a)) (by rw [he]; exact e.bijective)
  have hm (v) : c.e.symm v ∈ c.e.source := c.e.map_target (ht ▸ trivial)
  have hr (v) : c.e (c.e.symm v) = v := c.e.right_inv (ht ▸ trivial)
  have h1 (v) : CxPts.ev _ σ (chart k 1 0) (ratio k 1 0 0) (c.e.symm v) = 1 := by
    rw [ev_eq (hs ▸ hm v), ratio, ratioOn_self, map_one]
  have h2 (v) : CxPts.ev _ σ (chart k 1 0) (ratio k 1 0 1) (c.e.symm v) = v 0 :=
    (hx _ (hm v) 0).symm.trans (by rw [hr])
  have hφ (v) : (ProjAn.fsO1 k σ 1).φ (0 : Fin 2) (c.e.symm v) = Real.log (ArithHeightModel.u v) := by
    refine (Weight.fsBasis_φ _ _ _ _ _ _ _).trans (congrArg _ ?_)
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    refine (Fin.sum_univ_two _).trans ((congrArg₂ (fun a b : ℂ => ‖a‖ ^ 2 + ‖b‖ ^ 2) (h1 v) (h2 v)).trans ?_)
    simp only [norm_one, one_pow, ArithHeightModel.u, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hi : (ProjAn.fsO1 k σ 1).IsCInf := (hermitianTwistingSheaf k 1).cInf σ
  have hu : Continuous ArithHeightModel.u := continuous_iff_continuousAt.2 fun v =>
    (ArithHeightModel.hasFDerivAt_u v).continuousAt
  have := CxPts.secondCountableTopology_of_isProjOver σ (isProjOver_pspace_str k 1)
  rw [← hs, chernInt_chart hi c ht (ρ := fun v => 1 / Real.pi * (ArithHeightModel.u v ^ 2)⁻¹)
    (continuous_const.mul ((hu.pow 2).inv₀ fun v => (pow_pos (ArithHeightModel.u_pos v) 2).ne'))
    (fun v => by have := Real.pi_pos; positivity) fun v => ?_]
  · have hn (v) : (ProjAn.fsO1 k σ 1).nsq (secVal (PSpace.str k 1) σ (ProjSpace.coord k 1 0)) (c.e.symm v) =
        Real.exp (-Real.log (ArithHeightModel.u v)) := by
      refine (Weight.nsq_eq _ (secVal_mem _) (i := (0 : Fin 2)) (hs ▸ hm v)).trans ?_
      rw [hφ]
      exact (congrArg (fun a : ℂ => ‖a‖ ^ 2 * _) (h1 v)).trans (by simp)
    simp only [hn, Real.log_exp]
    rw [← mul_one (-(1 / 2) : ℝ), ← integral_log_dens, ← integral_const_mul]
    exact integral_congr_ae (.of_forall fun v => by ring)
  · rw [c.chernDens_eq hi (hm v) (i := (0 : Fin 2)) (hs ▸ hm v), Matrix.det_unique]
    have e₁ : c.hess (ProjAn.fsO1 k σ 1) (0 : Fin 2) (c.e.symm v) default default =
        ((ArithHeightModel.u v ^ 2)⁻¹ : ℝ) :=
      (congrArg₂ (fun F w => ReciprocityTheory.L2DbarEstimates.cHess 1 F w 0 0) (funext fun w => congrArg _ (hφ w)) (hr v)).trans
        (ArithHeightModel.cHess_log v)
    rw [e₁, Complex.ofReal_re]
    simp

/- English proof (translation)
The claim follows from `(Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨1, rfl⟩)`.
-/
theorem span_infty {A : Type} [CommRing A] : Ideal.span (Set.range (![0, 1] : Fin 2 → A)) = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨1, rfl⟩)

def infty : Sp ℤ ⟶ PSpace ℤ 1 := pt (RingHom.id ℤ) ![0, 1] span_infty

instance : IsClosedImmersion infty := by
  have : IsClosedImmersion (infty ≫ PSpace.str ℤ 1) := by
    rw [toZ_ext (infty ≫ _) (𝟙 _)]; infer_instance
  exact IsClosedImmersion.of_comp infty (PSpace.str ℤ 1)

/- English proof (translation)
Take `⟨v, hv⟩` from `projPt_surjective (Int.castRingHom ((PSpace ℤ n).residueField z)) ⟨(PSpace ℤ n).fromSpecResidueField z, toZ_ext _ _⟩`. Use `⟨_, inferInstance, v.1, v.2, ?_⟩` and prove the remaining obligations. Conclude with `(congrArg (fun f => f.1 (IsLocalRing.closedPoint _)) hv).trans (Scheme.fromSpecResidueField_apply _ _)`.
-/
theorem exists_pt_eq {n : ℕ} (z : PSpace ℤ n) : ∃ (K : Type) (_ : Field K) (v : Fin (n + 1) → K)
    (hv : Ideal.span (Set.range v) = ⊤), pt (Int.castRingHom K) v hv (IsLocalRing.closedPoint K) = z := by
  obtain ⟨v, hv⟩ := projPt_surjective (Int.castRingHom ((PSpace ℤ n).residueField z))
    ⟨(PSpace ℤ n).fromSpecResidueField z, toZ_ext _ _⟩
  refine ⟨_, inferInstance, v.1, v.2, ?_⟩
  exact (congrArg (fun f => f.1 (IsLocalRing.closedPoint _)) hv).trans (Scheme.fromSpecResidueField_apply _ _)

/- English proof (translation)
Take `⟨K, _, v, hv, rfl⟩` from `exists_pt_eq z`. Establish `h0 : v 0 = 0`. Assume the negation of the conclusion as `h`. Conclude with `hz ((le_pt_preimage_chart_iff _ v hv 0).2 (Ne.isUnit h) (Opens.mem_top _))`. Apply the tactic sequence `have h1 : v 1 ≠ 0 := fun h => span_range_eq_top_iff_ne_zero.1 hv (funext fun a => by fin_cases a <;> assumption)`.

Establish `e : spMap (Int.castRingHom K) ≫ infty = pt (Int.castRingHom K) v hv`. Rewrite using `[infty, spMap_pt]`. Apply the tactic sequence `exact (pt_eq_pt_iff _ _ _).2 ⟨Units.mk0 _ h1, funext fun a => by fin_cases a <;> simp [h0, Units.smul_def]⟩`. Conclude with `⟨_, congrArg (fun f => f (IsLocalRing.closedPoint K)) e⟩`.
-/
theorem mem_range_infty {z : PSpace ℤ 1} (hz : z ∉ chart ℤ 1 0) : z ∈ Set.range infty := by
  obtain ⟨K, _, v, hv, rfl⟩ := exists_pt_eq z
  have h0 : v 0 = 0 := by
    by_contra h
    exact hz ((le_pt_preimage_chart_iff _ v hv 0).2 (Ne.isUnit h) (Opens.mem_top _))
  have h1 : v 1 ≠ 0 := fun h => span_range_eq_top_iff_ne_zero.1 hv (funext fun a => by fin_cases a <;> assumption)
  have e : spMap (Int.castRingHom K) ≫ infty = pt (Int.castRingHom K) v hv := by
    rw [infty, spMap_pt]
    exact (pt_eq_pt_iff _ _ _).2 ⟨Units.mk0 _ h1, funext fun a => by fin_cases a <;> simp [h0, Units.smul_def]⟩
  exact ⟨_, congrArg (fun f => f (IsLocalRing.closedPoint K)) e⟩

/- English proof (translation)
Establish `e : nonzeroLocus (GlobalTheory.secPull (ProjSpace.coord ℤ 1 1) infty) = ⊤`. Rewrite using `[GlobalTheory.nonzeroLocus_secPull, nonzeroLocus_coord]`. Conclude with `top_le_iff.1 ((le_pt_preimage_chart_iff _ _ _ 1).2 isUnit_one)`. Establish `hu : genericPoint (Sp ℤ) ∈ nonzeroLocus (GlobalTheory.secPull (L` using `(hermitianTwistingSheaf ℤ 1).B) (ProjSpace.coord ℤ 1 1) infty) := e.ge trivial`. Rewrite using `[H.point _ infty ArithBase.isArithVar_int.charZero ArithBase.isArithVar_int.dim_eq _ (Cartier.isRatSec_ratOfSec _ hu), HermLB.curveDeg_sec infty _ hu fun σ y => ptsIn_mono e.ge mem_ptsIn_top, finsum_eq_zero_of_forall_eq_zero, finsum_eq_zero_of_forall_eq_zero, sub_zero]`.

Use `fun σ => finsum_eq_zero_of_forall_eq_zero fun y => ?_` and prove the remaining obligations. Establish `hy : PtsOver.map infty rfl _ y = projPt σ ⟨![0, 1], span_infty⟩`. Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `y.1 ≫ infty = pt σ ![0, 1] span_infty`. Rewrite using `[toZ_ext y.1 (spMap σ), infty, spMap_pt]`.

Use `congr 1`. Apply the tactic sequence `exact funext fun a => by fin_cases a <;> simp`. Establish `hm : projPt σ ⟨![0, 1], span_infty⟩ ∈ ptsIn (PSpace.str ℤ 1) σ ((O1 ℤ 1).U (1 : Fin 2))` using `(le_pt_preimage_chart_iff σ _ span_infty 1).2 isUnit_one`. Establish `e₁` using `ProjAn.fubiniStudyWeight_projPoint ℤ σ 1 ⟨![0, 1], span_infty⟩ 1 one_ne_zero`. Establish `e₂` using `valR_pt_ratio σ ![0, 1] span_infty (i := 1) isUnit_one 1`.

Establish `e₃ : (ProjAn.fsO1 ℤ σ 1).nsq (secVal _ σ (ProjSpace.coord ℤ 1 1)) (projPt σ ⟨![0, 1], span_infty⟩) = 1`. Use `(Weight.nsq_eq (ProjAn.fsO1 ℤ σ 1) (secVal_mem _) hm).trans ?_` and prove the remaining obligations. Use `(congrArg₂ (fun (a : ℂ) b => ‖a‖ ^ 2 * Real.exp (-b)) e₂ e₁).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[hy]`.

Conclude with `(congrArg (Real.log · / 2) e₃).trans (by simp)`. Introduce `z`. Use `mul_eq_zero_of_left (Int.cast_eq_zero.2 (by_contra fun hz => ?_)) _` and prove the remaining obligations. Conclude with `Cartier.notMem_supp_divOfSec.2 (e.ge trivial) (Cartier.CartierDiv.mem_supp_of_mult_ne_zero hz)`.
-/
theorem height_infty {h : PSpace ℤ 1 → ℝ} (H : (hermitianTwistingSheaf ℤ 1).IsArithHeight h) : h (infty (genericPoint _)) = 0 := by
  have e : nonzeroLocus (GlobalTheory.secPull (ProjSpace.coord ℤ 1 1) infty) = ⊤ := by
    rw [GlobalTheory.nonzeroLocus_secPull, nonzeroLocus_coord]
    exact top_le_iff.1 ((le_pt_preimage_chart_iff _ _ _ 1).2 isUnit_one)
  have hu : genericPoint (Sp ℤ) ∈ nonzeroLocus (GlobalTheory.secPull (L := (hermitianTwistingSheaf ℤ 1).B) (ProjSpace.coord ℤ 1 1) infty) :=
    e.ge trivial
  rw [H.point _ infty ArithBase.isArithVar_int.charZero ArithBase.isArithVar_int.dim_eq _
    (Cartier.isRatSec_ratOfSec _ hu), HermLB.curveDeg_sec infty _ hu fun σ y => ptsIn_mono e.ge mem_ptsIn_top,
    finsum_eq_zero_of_forall_eq_zero, finsum_eq_zero_of_forall_eq_zero, sub_zero]
  · refine fun σ => finsum_eq_zero_of_forall_eq_zero fun y => ?_
    have hy : PtsOver.map infty rfl _ y = projPt σ ⟨![0, 1], span_infty⟩ := by
      refine Subtype.ext ?_
      change y.1 ≫ infty = pt σ ![0, 1] span_infty
      rw [toZ_ext y.1 (spMap σ), infty, spMap_pt]
      congr 1
      exact funext fun a => by fin_cases a <;> simp
    have hm : projPt σ ⟨![0, 1], span_infty⟩ ∈ ptsIn (PSpace.str ℤ 1) σ ((O1 ℤ 1).U (1 : Fin 2)) :=
      (le_pt_preimage_chart_iff σ _ span_infty 1).2 isUnit_one
    have e₁ := ProjAn.fubiniStudyWeight_projPoint ℤ σ 1 ⟨![0, 1], span_infty⟩ 1 one_ne_zero
    have e₂ := valR_pt_ratio σ ![0, 1] span_infty (i := 1) isUnit_one 1
    have e₃ : (ProjAn.fsO1 ℤ σ 1).nsq (secVal _ σ (ProjSpace.coord ℤ 1 1)) (projPt σ ⟨![0, 1], span_infty⟩) = 1 := by
      refine (Weight.nsq_eq (ProjAn.fsO1 ℤ σ 1) (secVal_mem _) hm).trans ?_
      refine (congrArg₂ (fun (a : ℂ) b => ‖a‖ ^ 2 * Real.exp (-b)) e₂ e₁).trans ?_
      simp
    rw [hy]
    exact (congrArg (Real.log · / 2) e₃).trans (by simp)
  · intro z
    refine mul_eq_zero_of_left (Int.cast_eq_zero.2 (by_contra fun hz => ?_)) _
    exact Cartier.notMem_supp_divOfSec.2 (e.ge trivial) (Cartier.CartierDiv.mem_supp_of_mult_ne_zero hz)

/- English proof (translation)
Introduce `h H z hz hn`. Use `ProjSpace.isIntegral_of_isDomain ℤ 1` as an intermediate fact. Take `⟨w, rfl⟩` from `mem_range_infty hn`. Establish `h₁ : infty w ≤ infty (genericPoint _)` using `(genericPoint_specializes w).map infty.continuous`. Establish `h₂ : infty (genericPoint _) < genericPoint (PSpace ℤ 1)`.

Use `lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_` and prove the remaining obligations. Establish `h₃ : genericPoint (PSpace ℤ 1) ∈ chart ℤ 1 0` using `Cartier.gen_mem (x := chartι ℤ 1 0 (⊥ : PrimeSpectrum _)) (opensRange_chartι ℤ 1 0 ▸ ⟨_, rfl⟩)`. Establish `h₄ : genericPoint (Sp ℤ) ∈ infty ⁻¹ᵁ chart ℤ 1 0`. Establish `e' : _ = genericPoint (PSpace ℤ 1)` using `(Specializes.antisymm e (genericPoint_specializes _)).eq`. Conclude with `show infty _ ∈ chart ℤ 1 0 from e'.symm ▸ h₃`.

Rewrite `h₄` using `[infty, pt_preimage_chart]`. Conclude with `h₄ (Ideal.zero_mem _)`. Distinguish the cases in `hne : infty (genericPoint _) = infty w`. Conclude with `hne ▸ height_infty H`. Establish `h₃` using `Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e => hne (Specializes.antisymm h₁ e).eq)`.

Establish `h₄` using `Order.coheight_add_one_le h₂`. Rewrite `h₃` using `[hz]`. Establish `h₅ : (1 : ℕ∞) + 1 ≤ 1` using `(add_le_add_left (le_add_self.trans h₄) 1).trans h₃`. Conclude with `absurd h₅ (by decide)`.
-/
theorem height_eq_zero_off_chart : ∀ (h : PSpace ℤ 1 → ℝ), (hermitianTwistingSheaf ℤ 1).IsArithHeight h → ∀ z : PSpace ℤ 1, Order.coheight z = 1 → z ∉ chart ℤ 1 0 → h z = 0 := by
  intro h H z hz hn
  have := ProjSpace.isIntegral_of_isDomain ℤ 1
  obtain ⟨w, rfl⟩ := mem_range_infty hn
  have h₁ : infty w ≤ infty (genericPoint _) := (genericPoint_specializes w).map infty.continuous
  have h₂ : infty (genericPoint _) < genericPoint (PSpace ℤ 1) := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
    have h₃ : genericPoint (PSpace ℤ 1) ∈ chart ℤ 1 0 :=
      Cartier.gen_mem (x := chartι ℤ 1 0 (⊥ : PrimeSpectrum _)) (opensRange_chartι ℤ 1 0 ▸ ⟨_, rfl⟩)
    have h₄ : genericPoint (Sp ℤ) ∈ infty ⁻¹ᵁ chart ℤ 1 0 := by
      have e' : _ = genericPoint (PSpace ℤ 1) := (Specializes.antisymm e (genericPoint_specializes _)).eq
      exact show infty _ ∈ chart ℤ 1 0 from e'.symm ▸ h₃
    rw [infty, pt_preimage_chart] at h₄
    exact h₄ (Ideal.zero_mem _)
  by_cases hne : infty (genericPoint _) = infty w
  · exact hne ▸ height_infty H
  have h₃ := Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e => hne (Specializes.antisymm h₁ e).eq)
  have h₄ := Order.coheight_add_one_le h₂
  rw [hz] at h₃
  have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
  exact absurd h₅ (by decide)

/- English proof (translation)
Substitute `hn` using the available equality. Use `HermLB.isometric_of_chart (fun _ => PUnit.unit) (fun _ => le_top) (fun x j j' h h' => ?_) fun σ j y hy => ?_` and prove the remaining obligations. Take `rfl : j = j'` from `Subsingleton.elim (α := Fin 1) _ _`. Establish `e` using `(hermitianTwistingSheaf k 0).isLB.g_self j`. Establish `e'` using `gm_res (𝟙 _) x (le_inf le_rfl le_rfl) h ((hermitianTwistingSheaf k 0).B.g j j)`.

Rewrite using `[← e']`. Conclude with `(congrArg _ e).trans ((map_one _).trans (map_one _).symm)`. Take `⟨v, rfl⟩` from `projPt_surjective σ y`. Establish `hu` using `(le_pt_preimage_chart_iff σ v.1 v.2 j).1 hy`. Use `Eq.symm ((ProjAn.fubiniStudyWeight_projPoint k σ 0 v j hu.ne_zero).trans ?_)` and prove the remaining obligations.

Take `rfl : j = (0 : Fin 1)` from `Subsingleton.elim (α := Fin 1) _ _`. Rewrite using `[Fin.sum_univ_one, div_self hu.ne_zero, norm_one, one_pow, Real.log_one]`. Both sides reduce to the same expression.
-/
theorem isometric_fubini_study_dim_zero {k : Type} [CommRing k] {n : ℕ} (hn : n = 0) :
    (hermitianTwistingSheaf k n).Isometric (HermLB.triv _) := by
  subst hn
  refine HermLB.isometric_of_chart (fun _ => PUnit.unit) (fun _ => le_top) (fun x j j' h h' => ?_) fun σ j y hy => ?_
  · obtain rfl : j = j' := Subsingleton.elim (α := Fin 1) _ _
    have e := (hermitianTwistingSheaf k 0).isLB.g_self j
    have e' := gm_res (𝟙 _) x (le_inf le_rfl le_rfl) h ((hermitianTwistingSheaf k 0).B.g j j)
    rw [← e']
    exact (congrArg _ e).trans ((map_one _).trans (map_one _).symm)
  · obtain ⟨v, rfl⟩ := projPt_surjective σ y
    have hu := (le_pt_preimage_chart_iff σ v.1 v.2 j).1 hy
    refine Eq.symm ((ProjAn.fubiniStudyWeight_projPoint k σ 0 v j hu.ne_zero).trans ?_)
    obtain rfl : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
    rw [Fin.sum_univ_one, div_self hu.ne_zero, norm_one, one_pow, Real.log_one]
    rfl

/- English proof (translation)
Use `hX.isLocallyNoetherian` as an intermediate fact. Establish `e : nonzeroLocus (GlobalTheory.secPull u (𝟙 X)) = nonzeroLocus u` using `GlobalTheory.nonzeroLocus_secPull _ _`. Establish `key {q : X ⟶ Sp k} (hq : 𝟙 X ≫ p = q) : h (genericPoint X) = -∑ᶠ σ, ((L.pull (𝟙 X) hq).φ σ).chernInt D (ptsIn q σ (nonzeroLocus u)) fun y => Real.log ((L.φ σ).nsq (secVal p σ u) (PtsOver.map (𝟙 X) hq _ y)) / 2`. Substitute `hq` using the available equality. Establish `hu' : genericPoint X ∈ nonzeroLocus (GlobalTheory.secPull u (𝟙 X))` using `e ▸ hu`.

Establish `h₁` using `(H.recursion_sec (𝟙 X) u hu' hX.charZero hD hX.dim_eq).2`. Rewrite `h₁` using `[finsum_eq_zero_of_forall_eq_zero, zero_sub, e]`. Conclude with `h₁`. Introduce `z`. Distinguish the cases in `hz : (Cartier.divOfSec (L.restr (𝟙 X)).isLB _ hu').mult z = 0`.

Rewrite using `[hz, Int.cast_zero, zero_mul]`. Use `mul_eq_zero_of_right _ (h0 z (Cartier.CartierDiv.coheight_eq_one_of_mult_ne_zero hz) fun hm => ?_)` and prove the remaining obligations. Conclude with `Cartier.notMem_supp_divOfSec.2 (e ▸ hm) (Cartier.CartierDiv.mem_supp_of_mult_ne_zero hz)`. Establish `hid {σ : k →+* ℂ} (y : CxPts p σ) : PtsOver.map (𝟙 X) (Category.id_comp p) _ y = y` using `Subtype.ext (Category.comp_id _)`. Establish `hiso : L.Isometric (L.pull (𝟙 X) (Category.id_comp p))`.

Use `HermLB.isometric_of_chart (fun c _ => c) (fun c y hy => Set.mem_iInter.2 fun _ => hy) (fun z c c' hc hc' => ?_) fun σ c y _ => ?_` and prove the remaining obligations. Use `Eq.trans ?_ (gm_pull_g L.B (𝟙 X) (𝟙 X) z (fun _ => c) (fun _ => c') (Set.mem_iInter.2 fun _ => hc) (Set.mem_iInter.2 fun _ => hc')).symm` and prove the remaining obligations. Rewrite using `[Category.comp_id]`. Conclude with `((L.φ σ).pull_φ (𝟙 X) (Category.id_comp p) (fun _ => c) y).trans (congrArg _ (hid y))`. Rewrite using `[key (Category.id_comp p)]`.

Simplify using `only [hid, ← hiso.chernInt_eq]`.
-/
theorem recursion_self {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) (hD : 1 ≤ D) {L : HermLB p} {h : X → ℝ} (H : L.IsArithHeight h) (u : L.B.Sec)
    (hu : genericPoint X ∈ nonzeroLocus u) (h0 : ∀ z, Order.coheight z = 1 → z ∉ nonzeroLocus u → h z = 0) :
    h (genericPoint X) = -∑ᶠ σ, (L.φ σ).chernInt D (ptsIn p σ (nonzeroLocus u)) fun y =>
      Real.log ((L.φ σ).nsq (secVal p σ u) y) / 2 := by
  have := hX.isLocallyNoetherian
  have e : nonzeroLocus (GlobalTheory.secPull u (𝟙 X)) = nonzeroLocus u := GlobalTheory.nonzeroLocus_secPull _ _
  have key {q : X ⟶ Sp k} (hq : 𝟙 X ≫ p = q) : h (genericPoint X) =
      -∑ᶠ σ, ((L.pull (𝟙 X) hq).φ σ).chernInt D (ptsIn q σ (nonzeroLocus u)) fun y =>
        Real.log ((L.φ σ).nsq (secVal p σ u) (PtsOver.map (𝟙 X) hq _ y)) / 2 := by
    subst hq
    have hu' : genericPoint X ∈ nonzeroLocus (GlobalTheory.secPull u (𝟙 X)) := e ▸ hu
    have h₁ := (H.recursion_sec (𝟙 X) u hu' hX.charZero hD hX.dim_eq).2
    rw [finsum_eq_zero_of_forall_eq_zero, zero_sub, e] at h₁
    · exact h₁
    intro z
    by_cases hz : (Cartier.divOfSec (L.restr (𝟙 X)).isLB _ hu').mult z = 0
    · rw [hz, Int.cast_zero, zero_mul]
    · refine mul_eq_zero_of_right _ (h0 z (Cartier.CartierDiv.coheight_eq_one_of_mult_ne_zero hz) fun hm => ?_)
      exact Cartier.notMem_supp_divOfSec.2 (e ▸ hm) (Cartier.CartierDiv.mem_supp_of_mult_ne_zero hz)
  have hid {σ : k →+* ℂ} (y : CxPts p σ) : PtsOver.map (𝟙 X) (Category.id_comp p) _ y = y := Subtype.ext (Category.comp_id _)
  have hiso : L.Isometric (L.pull (𝟙 X) (Category.id_comp p)) := by
    refine HermLB.isometric_of_chart (fun c _ => c) (fun c y hy => Set.mem_iInter.2 fun _ => hy)
      (fun z c c' hc hc' => ?_) fun σ c y _ => ?_
    · refine Eq.trans ?_ (gm_pull_g L.B (𝟙 X) (𝟙 X) z (fun _ => c) (fun _ => c')
        (Set.mem_iInter.2 fun _ => hc) (Set.mem_iInter.2 fun _ => hc')).symm
      rw [Category.comp_id]
    · exact ((L.φ σ).pull_φ (𝟙 X) (Category.id_comp p) (fun _ => c) y).trans (congrArg _ (hid y))
  rw [key (Category.id_comp p)]
  simp only [hid, ← hiso.chernInt_eq]

/- English proof (translation)
Substitute `hn` using the available equality. Take `⟨h, H, rfl⟩` from `ha`. Establish `e : nonzeroLocus (ProjSpace.coord ℤ 1 0) = chart ℤ 1 0` using `nonzeroLocus_coord ℤ 1 0`. Establish `hg : genericPoint (PSpace ℤ 1) ∈ chart ℤ 1 0` using `Cartier.gen_mem (x := chartι ℤ 1 0 (⊥ : PrimeSpectrum _)) (opensRange_chartι ℤ 1 0 ▸ ⟨_, rfl⟩)`. Rewrite using `[recursion_self (ProjSpace.isArithVar_int 1) le_rfl H (ProjSpace.coord ℤ 1 0) (e ▸ hg) (fun z h₁ h₂ => height_eq_zero_off_chart h H z h₁ (e ▸ h₂)), finsum_eq_single _ (Int.castRingHom ℂ) fun σ h => absurd (RingHom.ext_int _ _) h]`.

Use `neg_eq_iff_eq_neg.2 (Eq.trans ?_ (chernInt_log_coord ℤ (Int.castRingHom ℂ)))` and prove the remaining obligations. Rewrite using `[← e]`. Both sides reduce to the same expression.
-/
theorem selfInter_line {n : ℕ} (hn : n = 1) [IsIntegral (PSpace ℤ n)] {a : ℝ} (ha : (hermitianTwistingSheaf ℤ n).IsSelfInter a) :
    a = 1 / 2 := by
  subst hn
  obtain ⟨h, H, rfl⟩ := ha
  have e : nonzeroLocus (ProjSpace.coord ℤ 1 0) = chart ℤ 1 0 := nonzeroLocus_coord ℤ 1 0
  have hg : genericPoint (PSpace ℤ 1) ∈ chart ℤ 1 0 :=
    Cartier.gen_mem (x := chartι ℤ 1 0 (⊥ : PrimeSpectrum _)) (opensRange_chartι ℤ 1 0 ▸ ⟨_, rfl⟩)
  rw [recursion_self (ProjSpace.isArithVar_int 1) le_rfl H (ProjSpace.coord ℤ 1 0) (e ▸ hg)
    (fun z h₁ h₂ => height_eq_zero_off_chart h H z h₁ (e ▸ h₂)),
    finsum_eq_single _ (Int.castRingHom ℂ) fun σ h => absurd (RingHom.ext_int _ _) h]
  refine neg_eq_iff_eq_neg.2 (Eq.trans ?_ (chernInt_log_coord ℤ (Int.castRingHom ℂ)))
  rw [← e]
  rfl

end GlobalTheory.FlagZ.Plane
