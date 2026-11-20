import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsomOfInducedHermitianBundles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalIsometryIsometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfIntegralValuationBoundStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.CoverNorm.Isom

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

/- English proof (translation)
Rewrite using `[← Scheme.Hom.comp_apply, V.pb.w, Scheme.Hom.comp_apply]`. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap (𝓞 F) F) ((V.π ≫ Y.str) y).asIdeal = ⊥`. Use `((V.π ≫ Y.str) y).isPrime` as an intermediate fact. Rewrite using `[Ideal.eq_bot_of_prime ((V.π ≫ Y.str) y).asIdeal]`. Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)`.
-/
theorem asIdeal_p_j (V : Cover Y) (y : V.G) : (V.p (V.j y)).asIdeal = ⊥ := by
  rw [← Scheme.Hom.comp_apply, V.pb.w, Scheme.Hom.comp_apply]
  change Ideal.comap (algebraMap (𝓞 F) F) ((V.π ≫ Y.str) y).asIdeal = ⊥
  have := ((V.π ≫ Y.str) y).isPrime
  rw [Ideal.eq_bot_of_prime ((V.π ≫ Y.str) y).asIdeal]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

/- English proof (translation)
Rewrite using `[← V.pb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, V.pb.isoPullback.hom.surjective.range_eq, Set.image_univ, Scheme.Pullback.range_fst]`. Use `⟨IsLocalRing.closedPoint F, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap (𝓞 F) F) (IsLocalRing.maximalIdeal F) = ⊥`. Rewrite using `[IsLocalRing.maximalIdeal_eq_bot]`. Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)`.
-/
theorem mem_range_j (V : Cover Y) {x : V.X} (hx : (V.p x).asIdeal = ⊥) : x ∈ Set.range V.j := by
  rw [← V.pb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, V.pb.isoPullback.hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]
  refine ⟨IsLocalRing.closedPoint F, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
  change Ideal.comap (algebraMap (𝓞 F) F) (IsLocalRing.maximalIdeal F) = ⊥
  rw [IsLocalRing.maximalIdeal_eq_bot]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

/- English proof (translation)
Establish `h0 : (V.p (genericPoint V.X)).asIdeal = ⊥` using `eq_bot_iff.2 (((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2 ((genericPoint_specializes (V.j (genericPoint V.G))).map V.p.continuous))).trans (asIdeal_p_j V _).le)`. Take `⟨y, hy⟩` from `mem_range_j V h0`. Conclude with `hy ▸ (genericPoint_specializes y).map V.j.continuous`.
-/
theorem j_gen_specializes (V : Cover Y) : V.j (genericPoint V.G) ⤳ genericPoint V.X := by
  have h0 : (V.p (genericPoint V.X)).asIdeal = ⊥ :=
    eq_bot_iff.2 (((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2
      ((genericPoint_specializes (V.j (genericPoint V.G))).map V.p.continuous))).trans
        (asIdeal_p_j V _).le)
  obtain ⟨y, hy⟩ := mem_range_j V h0
  exact hy ▸ (genericPoint_specializes y).map V.j.continuous

/- English proof (translation)
Establish `hτ` using `ringOfIntegers_hom_complex_injective F τ`. Take `⟨σ, hσ⟩ : ∃ σ : F →+* ℂ, σ.comp (algebraMap (𝓞 F) F) = τ` from `⟨IsFractionRing.lift (K := F) hτ, RingHom.ext fun x => IsFractionRing.lift_algebraMap (K := F) hτ x⟩`. Use `⟨σ, hσ, ?_⟩` and prove the remaining obligations. Establish `hw : y'.1 ≫ V.p = spMap σ ≫ spMap (algebraMap (𝓞 F) F)` using `y'.2.trans ((congrArg spMap hσ.symm).trans (spMap_comp _ _))`. Conclude with `⟨⟨V.pb.lift y'.1 _ hw, V.pb.lift_snd _ _ _⟩, (V.pb.lift_fst _ _ _).symm⟩`.
-/
theorem cxPts_from_generic_fibre (V : Cover Y) (τ : 𝓞 F →+* ℂ) (y' : CxPts V.p τ) :
    ∃ σ : F →+* ℂ, σ.comp (algebraMap (𝓞 F) F) = τ ∧ ∃ z : CxPts (V.π ≫ Y.str) σ, y'.1 = z.1 ≫ V.j := by
  have hτ := ringOfIntegers_hom_complex_injective F τ
  obtain ⟨σ, hσ⟩ : ∃ σ : F →+* ℂ, σ.comp (algebraMap (𝓞 F) F) = τ :=
    ⟨IsFractionRing.lift (K := F) hτ, RingHom.ext fun x => IsFractionRing.lift_algebraMap (K := F) hτ x⟩
  refine ⟨σ, hσ, ?_⟩
  have hw : y'.1 ≫ V.p = spMap σ ≫ spMap (algebraMap (𝓞 F) F) :=
    y'.2.trans ((congrArg spMap hσ.symm).trans (spMap_comp _ _))
  exact ⟨⟨V.pb.lift y'.1 _ hw, V.pb.lift_snd _ _ _⟩, (V.pb.lift_fst _ _ _).symm⟩

/- English proof (translation)
Establish `hc : c ≠ 0` using `left_ne_zero_of_mul ha.ne_zero`. Establish `ha0 : a ≠ 0` using `right_ne_zero_of_mul ha.ne_zero`. Establish `e₁ : b / a = (c * b) * (c * a)⁻¹` using `by field_simp`. Establish `pa` using `e.w.pos (SmallSec.valAt_ne_zero ha)`. Establish `pb` using `e.w.pos (SmallSec.valAt_ne_zero hb)`.

Establish `e₂` using `Real.log_injOn_pos pa pb h`. Rewrite using `[e₁, SmallSec.valAt_mul hb.regAt ha.inv.regAt, GlobalTheory.LineNorm.Neg.valAt_inv ha, map_mul, map_inv₀, ← e₂, mul_inv_cancel₀ pa.ne']`.
-/
theorem w_div_eq_one {Z : Scheme.{0}} [IsIntegral Z] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v)
    (z : Sp (AlgebraicClosure F) ⟶ Z) {c a b : Z.functionField} (ha : UnitAt (below z) (c * a))
    (hb : UnitAt (below z) (c * b))
    (h : Real.log (e.w (valAt z (c * a))) = Real.log (e.w (valAt z (c * b)))) :
    e.w (valAt z (b / a)) = 1 := by
  have hc : c ≠ 0 := left_ne_zero_of_mul ha.ne_zero
  have ha0 : a ≠ 0 := right_ne_zero_of_mul ha.ne_zero
  have e₁ : b / a = (c * b) * (c * a)⁻¹ := by field_simp
  have pa := e.w.pos (SmallSec.valAt_ne_zero ha)
  have pb := e.w.pos (SmallSec.valAt_ne_zero hb)
  have e₂ := Real.log_injOn_pos pa pb h
  rw [e₁, SmallSec.valAt_mul hb.regAt ha.inv.regAt, GlobalTheory.LineNorm.Neg.valAt_inv ha, map_mul, map_inv₀, ← e₂,
    mul_inv_cancel₀ pa.ne']

/- English proof (translation)
Establish `hc : c ≠ 0` using `left_ne_zero_of_mul ha.ne_zero`. Establish `ha0 : a ≠ 0` using `right_ne_zero_of_mul ha.ne_zero`. Establish `e₁ : b / a = (c * b) * (c * a)⁻¹` using `by field_simp`. Establish `hq : UnitAt (under y) (b / a)`. Rewrite using `[e₁]`.

Conclude with `hb.mul ha.inv`. Establish `e₂ : ratVal (b / a) y * ratVal (c * a) y = ratVal (c * b) y`. Rewrite using `[← ratVal_mul hq.regAt ha.regAt]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Establish `na` using `norm_ne_zero_iff.2 (ratVal_ne_zero ha)`. Establish `nq` using `norm_ne_zero_iff.2 (ratVal_ne_zero hq)`. Establish `e₃` using `congrArg (fun t => Real.log ‖t‖) e₂`. Simplify using `only [norm_mul] at e₃`. Rewrite `e₃` using `[Real.log_mul nq na]`.

Rewrite using `[Real.log_pow]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_ratVal_div {k : Type} [CommRing k] {σ : k →+* ℂ} {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (y : CxPts q σ) {c a b : Z.functionField} (ha : UnitAt (under y) (c * a)) (hb : UnitAt (under y) (c * b)) :
    Real.log (‖ratVal (b / a) y‖ ^ 2) = 2 * Real.log ‖ratVal (c * b) y‖ - 2 * Real.log ‖ratVal (c * a) y‖ := by
  have hc : c ≠ 0 := left_ne_zero_of_mul ha.ne_zero
  have ha0 : a ≠ 0 := right_ne_zero_of_mul ha.ne_zero
  have e₁ : b / a = (c * b) * (c * a)⁻¹ := by field_simp
  have hq : UnitAt (under y) (b / a) := by
    rw [e₁]
    exact hb.mul ha.inv
  have e₂ : ratVal (b / a) y * ratVal (c * a) y = ratVal (c * b) y := by
    rw [← ratVal_mul hq.regAt ha.regAt]
    congr 1
    field_simp
  have na := norm_ne_zero_iff.2 (ratVal_ne_zero ha)
  have nq := norm_ne_zero_iff.2 (ratVal_ne_zero hq)
  have e₃ := congrArg (fun t => Real.log ‖t‖) e₂
  simp only [norm_mul] at e₃
  rw [Real.log_mul nq na] at e₃
  rw [Real.log_pow]
  push_cast
  linarith

/- English proof (translation)
Introduce `F _ _ Y V L L' f a l ⟨r, hr, hu, hc, hf⟩ ⟨r', hr', hu', hc', hf'⟩`. Use `haveI := CoverHt.isPreimmersion_j V`. Establish `hη` using `j_gen_specializes V`. Set `ρ : V.X.functionField ≃+* V.G.functionField` to `RingEquiv.ofBijective (SmallSec.fnMap V.j hη) ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩`. Establish `hρ : ∀ (U : V.X.Opens) (hU : genericPoint V.X ∈ U) (hU' : genericPoint V.G ∈ V.j ⁻¹ᵁ U) (s : Γ(V.X, U)), ρ (fnOf U hU s) = fnOf (V.j ⁻¹ᵁ U) hU' (V.j.app U s)` using `fun U hU hU' s => SmallSec.fnMap_fnOf V.j hη hU hU' s`.

Establish `hj : V.j (genericPoint V.G) = genericPoint V.X` using `(hη.antisymm (genericPoint_specializes _)).eq`. Establish `hv : ∀ {K : Type} [Field K] (y : Sp K ⟶ V.G) (g : V.X.functionField), valAt (y ≫ V.j) g = valAt y (ρ g)` using `fun y g => ModelFn.valAt_comp V.j hη y g`. Establish `hR` using `InducedIsom.isRatSec_lift V.j ρ hρ hj L.B hr`. Establish `hR'` using `InducedIsom.isRatSec_lift V.j ρ hρ hj L'.B hr'`. Establish `hP` using `presents_divOfRatSec L.isLB hR`.

Establish `eρ (a b : V.G.functionFieldˣ) : ρ ((Units.map ρ.symm.toMonoidHom b : V.X.functionField) / (Units.map ρ.symm.toMonoidHom a : V.X.functionField)) = (b : V.G.functionField) / a`. Rewrite using `[map_div₀]`. Conclude with `congrArg₂ (· / ·) (ρ.apply_symm_apply _) (ρ.apply_symm_apply _)`. Establish `key : ∀ (i : L.B.ι) (j : L'.B.ι) (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ (L.B.U i ⊓ L'.B.U j) → e.w (valAt z (((r …`. Introduce `i j v e z yt hz e₂ hU`.

Set `y : AlgPt Y` to `⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩`. Establish `h₁ : ⊤ ≤ yt ⁻¹ᵁ L.B.U ((fun _ => i : (L.B.pull V.j).ι) PUnit.unit)` using `fun w hw => (hU hw).1`. Establish `h₂ : ⊤ ≤ yt ⁻¹ᵁ L'.B.U ((fun _ => j : (L'.B.pull V.j).ι) PUnit.unit)` using `fun w hw => (hU hw).2`. Establish `H₁` using `hf v e y z yt (fun _ => i) rfl e₂ h₁`. Establish `H₂` using `hf' v e y z yt (fun _ => j) rfl e₂ h₂`.

Establish `hpt : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ L.B.U i ⊓ L'.B.U j`. Rewrite using `[← e₂]`. Conclude with `hU (Set.mem_univ _)`. Establish `m₁ : below z ∈ (L.B.pull V.j).U (fun _ => i)` using `Set.mem_iInter.2 fun _ => hpt.1`. Establish `m₂ : below z ∈ (L'.B.pull V.j).U (fun _ => j)` using `Set.mem_iInter.2 fun _ => hpt.2`.

Establish `hπ : V.π (below z) = below y.1` using `rfl`. Establish `u₁` using `hu _ _ m₁`. Establish `u₂` using `hu' _ _ m₂`. Rewrite `u₁`, `u₂` using `[hπ]`. Conclude with `⟨w_div_eq_one e z u₁ u₂ (H₁.symm.trans H₂), w_div_eq_one e z u₂ u₁ (H₂.symm.trans H₁)⟩`.

Use `GlobalTheory.T.rational_isometry_isometric _ _ _ L L' ⟨_, _, _, hP, ⟨L'.isLB, hR', fun j x hxj => ?_⟩, fun τ y' i j hi hj' => ?_⟩` and prove the remaining obligations. Take `⟨i, hxi⟩` from `exists_chart L.isLB x`. Use `(hP.isEqn i x hxi).iff_unitAt.2 ((unitAt_iff (div_ne_zero (Units.ne_zero _) (Units.ne_zero _))).2 ⟨?_, ?_⟩)` and prove the remaining obligations. Use `GlobalTheory.T.regular_of_integral_valuation_bound F Y V (L.B.U i ⊓ L'.B.U j) _ (fun v e z yt hz h hU => ?_) x ⟨hxi, hxj⟩` and prove the remaining obligations. Rewrite using `[hv, eρ]`.

Conclude with `(key i j v e z yt hz h hU).1.le`. Rewrite using `[inv_div]`. Use `GlobalTheory.T.regular_of_integral_valuation_bound F Y V (L.B.U i ⊓ L'.B.U j) _ (fun v e z yt hz h hU => ?_) x ⟨hxi, hxj⟩` and prove the remaining obligations. Rewrite using `[hv, eρ]`. Conclude with `(key i j v e z yt hz h hU).2.le`.

Take `⟨σ, rfl, z, hz⟩` from `cxPts_from_generic_fibre V τ y'`. Set `y : Pts Y σ` to `⟨z.1 ≫ V.π, by rw [Category.assoc]; exact z.2⟩`. Establish `hun : under y' = V.j (under z)`. Express the relevant statement in the definitionally equal form `y'.1 _ = _`. Rewrite using `[hz]`.

Both sides reduce to the same expression. Establish `m₁ : under z ∈ (L.B.pull V.j).U fun _ => i` using `Set.mem_iInter.2 fun _ => by`. Express the relevant statement in the definitionally equal form `V.j (under z) ∈ L.B.U i`. Rewrite using `[← hun]`. Conclude with `mem_ptsIn.1 hi`.

Establish `m₂ : under z ∈ (L'.B.pull V.j).U fun _ => j` using `Set.mem_iInter.2 fun _ => by`. Express the relevant statement in the definitionally equal form `V.j (under z) ∈ L'.B.U j`. Rewrite using `[← hun]`. Conclude with `mem_ptsIn.1 hj'`. Establish `H₁` using `hc σ z y y' (fun _ => i) rfl hz m₁`.

Establish `H₂` using `hc' σ z y y' (fun _ => j) rfl hz m₂`. Establish `hπ : V.π (under z) = under y` using `rfl`. Establish `u₁` using `hu _ _ m₁`. Establish `u₂` using `hu' _ _ m₂`. Rewrite `u₁`, `u₂` using `[hπ]`.

Establish `hq : ratVal ((Units.map ρ.symm.toMonoidHom (r' fun _ => j) / Units.map ρ.symm.toMonoidHom (r fun _ => i) : V.X.functionFieldˣ) : V.X.functionField) y' = ratVal (((r' fun _ => j : V.G.functionFieldˣ) : V.G.functionField) / ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField)) …`. Rewrite using `[ModelFn.ratVal_eq, ModelFn.ratVal_eq, hz, hv, Units.val_div_eq_div_val, eρ]`. Rewrite using `[hq, log_ratVal_div z u₁ u₂]`. Use `first`. Consider the case `linarith`.

Consider the case `(beta_reduce at H₁ H₂; linarith)`. Consider the case `(dsimp only at H₁ H₂; linarith)`.
-/
theorem isometric_of_norms : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L L' : HermLB V.p)
    (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ),
    Norms V L f a l → Norms V L' f a l → L.Isometric L' := by
  intro F _ _ Y V L L' f a l ⟨r, hr, hu, hc, hf⟩ ⟨r', hr', hu', hc', hf'⟩
  haveI := CoverHt.isPreimmersion_j V
  have hη := j_gen_specializes V
  let ρ : V.X.functionField ≃+* V.G.functionField := RingEquiv.ofBijective (SmallSec.fnMap V.j hη)
    ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩
  have hρ : ∀ (U : V.X.Opens) (hU : genericPoint V.X ∈ U) (hU' : genericPoint V.G ∈ V.j ⁻¹ᵁ U) (s : Γ(V.X, U)),
      ρ (fnOf U hU s) = fnOf (V.j ⁻¹ᵁ U) hU' (V.j.app U s) := fun U hU hU' s => SmallSec.fnMap_fnOf V.j hη hU hU' s
  have hj : V.j (genericPoint V.G) = genericPoint V.X := (hη.antisymm (genericPoint_specializes _)).eq
  have hv : ∀ {K : Type} [Field K] (y : Sp K ⟶ V.G) (g : V.X.functionField), valAt (y ≫ V.j) g = valAt y (ρ g) :=
    fun y g => ModelFn.valAt_comp V.j hη y g
  have hR := InducedIsom.isRatSec_lift V.j ρ hρ hj L.B hr
  have hR' := InducedIsom.isRatSec_lift V.j ρ hρ hj L'.B hr'
  have hP := presents_divOfRatSec L.isLB hR
  have eρ (a b : V.G.functionFieldˣ) : ρ ((Units.map ρ.symm.toMonoidHom b : V.X.functionField) /
      (Units.map ρ.symm.toMonoidHom a : V.X.functionField)) = (b : V.G.functionField) / a := by
    rw [map_div₀]
    exact congrArg₂ (· / ·) (ρ.apply_symm_apply _) (ρ.apply_symm_apply _)

  have key : ∀ (i : L.B.ι) (j : L'.B.ι) (v : HeightOneSpectrum (𝓞 F)) (e : Ext v)
      (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) →
      spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ (L.B.U i ⊓ L'.B.U j) →
      e.w (valAt z (((r' fun _ => j : V.G.functionFieldˣ) : V.G.functionField) / ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField))) = 1 ∧
        e.w (valAt z (((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField) / ((r' fun _ => j : V.G.functionFieldˣ) : V.G.functionField))) = 1 := by
    intro i j v e z yt hz e₂ hU
    let y : AlgPt Y := ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩
    have h₁ : ⊤ ≤ yt ⁻¹ᵁ L.B.U ((fun _ => i : (L.B.pull V.j).ι) PUnit.unit) := fun w hw => (hU hw).1
    have h₂ : ⊤ ≤ yt ⁻¹ᵁ L'.B.U ((fun _ => j : (L'.B.pull V.j).ι) PUnit.unit) := fun w hw => (hU hw).2
    have H₁ := hf v e y z yt (fun _ => i) rfl e₂ h₁
    have H₂ := hf' v e y z yt (fun _ => j) rfl e₂ h₂
    have hpt : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ L.B.U i ⊓ L'.B.U j := by
      rw [← e₂]
      exact hU (Set.mem_univ _)
    have m₁ : below z ∈ (L.B.pull V.j).U (fun _ => i) := Set.mem_iInter.2 fun _ => hpt.1
    have m₂ : below z ∈ (L'.B.pull V.j).U (fun _ => j) := Set.mem_iInter.2 fun _ => hpt.2
    have hπ : V.π (below z) = below y.1 := rfl
    have u₁ := hu _ _ m₁
    have u₂ := hu' _ _ m₂
    rw [hπ] at u₁ u₂
    exact ⟨w_div_eq_one e z u₁ u₂ (H₁.symm.trans H₂), w_div_eq_one e z u₂ u₁ (H₂.symm.trans H₁)⟩
  refine GlobalTheory.T.rational_isometry_isometric _ _ _ L L' ⟨_, _, _, hP, ⟨L'.isLB, hR', fun j x hxj => ?_⟩, fun τ y' i j hi hj' => ?_⟩
  · obtain ⟨i, hxi⟩ := exists_chart L.isLB x
    refine (hP.isEqn i x hxi).iff_unitAt.2
      ((unitAt_iff (div_ne_zero (Units.ne_zero _) (Units.ne_zero _))).2 ⟨?_, ?_⟩)
    · refine GlobalTheory.T.regular_of_integral_valuation_bound F Y V (L.B.U i ⊓ L'.B.U j) _ (fun v e z yt hz h hU => ?_) x ⟨hxi, hxj⟩
      rw [hv, eρ]
      exact (key i j v e z yt hz h hU).1.le
    · rw [inv_div]
      refine GlobalTheory.T.regular_of_integral_valuation_bound F Y V (L.B.U i ⊓ L'.B.U j) _ (fun v e z yt hz h hU => ?_) x ⟨hxi, hxj⟩
      rw [hv, eρ]
      exact (key i j v e z yt hz h hU).2.le
  · obtain ⟨σ, rfl, z, hz⟩ := cxPts_from_generic_fibre V τ y'
    let y : Pts Y σ := ⟨z.1 ≫ V.π, by rw [Category.assoc]; exact z.2⟩
    have hun : under y' = V.j (under z) := by
      change y'.1 _ = _
      rw [hz]
      rfl
    have m₁ : under z ∈ (L.B.pull V.j).U fun _ => i := Set.mem_iInter.2 fun _ => by
      change V.j (under z) ∈ L.B.U i
      rw [← hun]
      exact mem_ptsIn.1 hi
    have m₂ : under z ∈ (L'.B.pull V.j).U fun _ => j := Set.mem_iInter.2 fun _ => by
      change V.j (under z) ∈ L'.B.U j
      rw [← hun]
      exact mem_ptsIn.1 hj'
    have H₁ := hc σ z y y' (fun _ => i) rfl hz m₁
    have H₂ := hc' σ z y y' (fun _ => j) rfl hz m₂
    have hπ : V.π (under z) = under y := rfl
    have u₁ := hu _ _ m₁
    have u₂ := hu' _ _ m₂
    rw [hπ] at u₁ u₂
    have hq : ratVal ((Units.map ρ.symm.toMonoidHom (r' fun _ => j) / Units.map ρ.symm.toMonoidHom (r fun _ => i) :
        V.X.functionFieldˣ) : V.X.functionField) y' = ratVal (((r' fun _ => j : V.G.functionFieldˣ) : V.G.functionField) / ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField)) z := by
      rw [ModelFn.ratVal_eq, ModelFn.ratVal_eq, hz, hv, Units.val_div_eq_div_val, eρ]
    rw [hq, log_ratVal_div z u₁ u₂]
    first
      | linarith
      | (beta_reduce at H₁ H₂; linarith)
      | (dsimp only at H₁ H₂; linarith)

end GlobalTheory.CoverNorm.Isom
