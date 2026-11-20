import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelFunctionFieldCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsLiftModelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularOfValuationBoundedAtPointsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.HermIsom Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.InducedIsom

open OfModel

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `hf`. Rewrite using `[valAt_algebraMap]`. Conclude with `(ha.map _).ne_zero`.
-/
theorem valAt_ne_zero {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) {f : Z.functionField}
    (hf : UnitAt (below y) f) : valAt y f ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [valAt_algebraMap]
  exact (ha.map _).ne_zero

/- English proof (translation)
Introduce `i i' h`. Establish `h' : genericPoint Z ∈ j ⁻¹ᵁ (B.U i ⊓ B.U i')`. Express the relevant statement in the definitionally equal form `j (genericPoint Z) ∈ B.U i ⊓ B.U i'`. Rewrite using `[hj]` and apply the resulting hypothesis. Establish `h₂ : genericPoint Z ∈ (B.pull j).U (fun _ => i) ⊓ (B.pull j).U (fun _ => i')` using `⟨Set.mem_iInter.2 fun _ => h'.1, Set.mem_iInter.2 fun _ => h'.2⟩`.

Establish `l : (B.pull j).U (fun _ => i) ⊓ (B.pull j).U (fun _ => i') ≤ j ⁻¹ᵁ (B.U i ⊓ B.U i')` using `fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩`. Establish `hg : ((B.pull j).g (fun _ => i) (fun _ => i')).val = resG Z l (j.app _ (B.g i i').val)`. Establish `: (B.pull j).g (fun _ => i) (fun _ => i') = res l (pullU j _ (B.g i i'))`. Express the relevant statement in the definitionally equal form `∏ _k : PUnit, _ = _`. Conclude with `(Fintype.prod_unique _).trans (zpow_one _)`.

Rewrite using `[this]`. Both sides reduce to the same expression. Establish `e` using `hr (fun _ => i) (fun _ => i') h₂`. Rewrite `e` using `[hg, fnOf_resG, ← hρ _ h]`. Apply `ρ.injective` to reduce the goal to its premises.

Rewrite using `[map_mul]`. Conclude with `(ρ.apply_symm_apply _).trans (e.trans (congrArg _ (ρ.apply_symm_apply _).symm))`.
-/
theorem isRatSec_lift {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (j : Z ⟶ X)
    (ρ : X.functionField ≃+* Z.functionField)
    (hρ : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint Z ∈ j ⁻¹ᵁ U) (s : Γ(X, U)),
      ρ (fnOf U hU s) = fnOf (j ⁻¹ᵁ U) hU' (j.app U s))
    (hj : j (genericPoint Z) = genericPoint X) (B : LB X) {r : (B.pull j).ι → Z.functionFieldˣ}
    (hr : IsRatSec (B.pull j) r) :
    IsRatSec B fun i => Units.map ρ.symm.toMonoidHom (r fun _ => i) := by
  intro i i' h
  have h' : genericPoint Z ∈ j ⁻¹ᵁ (B.U i ⊓ B.U i') := by
    change j (genericPoint Z) ∈ B.U i ⊓ B.U i'
    rwa [hj]
  have h₂ : genericPoint Z ∈ (B.pull j).U (fun _ => i) ⊓ (B.pull j).U (fun _ => i') :=
    ⟨Set.mem_iInter.2 fun _ => h'.1, Set.mem_iInter.2 fun _ => h'.2⟩
  have l : (B.pull j).U (fun _ => i) ⊓ (B.pull j).U (fun _ => i') ≤ j ⁻¹ᵁ (B.U i ⊓ B.U i') :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have hg : ((B.pull j).g (fun _ => i) (fun _ => i')).val = resG Z l (j.app _ (B.g i i').val) := by
    have : (B.pull j).g (fun _ => i) (fun _ => i') = res l (pullU j _ (B.g i i')) := by
      change ∏ _k : PUnit, _ = _
      exact (Fintype.prod_unique _).trans (zpow_one _)
    rw [this]
    rfl
  have e := hr (fun _ => i) (fun _ => i') h₂
  rw [hg, fnOf_resG, ← hρ _ h] at e
  apply ρ.injective
  rw [map_mul]
  exact (ρ.apply_symm_apply _).trans (e.trans (congrArg _ (ρ.apply_symm_apply _).symm))

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

/- English proof (translation)
Establish `h₀ : (k • D).IsEqn (below y.1) (eqn D (below y.1) ^ k)` using `(D.exists_isEqn (below y.1)).choose_spec.nsmul k`. Establish `hu {c : Y.Fnˣ} (hc : (k • D).IsEqn (below y.1) c) : UnitAt (below y.1) (((eqn D (below y.1))⁻¹ ^ k * c : Y.Fnˣ) : Y.Fn)`. Use `h₀.iff_unitAt.1 hc` as an intermediate fact. Rewrite `this` using `[div_eq_inv_mul, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← inv_pow]`. Then use the resulting hypothesis. Establish `e₁ : (((eqn D (below y.1))⁻¹ ^ k * b : Y.Fnˣ) : Y.Fn) = (b : Y.Fn) / a * (((eqn D (below y.1))⁻¹ ^ k * a : Y.Fnˣ) : Y.Fn)`.

Rewrite using `[Units.val_mul, Units.val_mul, mul_left_comm, div_mul_cancel₀ _ a.ne_zero]`. Establish `pa` using `e.w.pos (valAt_ne_zero _ (hu ha))`. Establish `pb` using `e.w.pos (valAt_ne_zero _ (hu hb))`. Establish `e₂` using `Real.log_injOn_pos pa pb h`. Rewrite `e₂` using `[e₁, valAt_mul _ (ha.iff_unitAt.1 hb).regAt (hu ha).regAt, map_mul]`.

Conclude with `mul_right_cancel₀ pa.ne' (e₂.symm.trans (one_mul _).symm)`.
-/
theorem w_div_eq_one {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (y : AlgPt Y) {D : Y.Dv} {k : ℕ} {a b : Y.Fnˣ}
    (ha : (k • D).IsEqn (below y.1) a) (hb : (k • D).IsEqn (below y.1) b)
    (h : Real.log (e.w (valAt y.1 (((eqn D (below y.1))⁻¹ ^ k * a : Y.Fnˣ) : Y.Fn))) =
      Real.log (e.w (valAt y.1 (((eqn D (below y.1))⁻¹ ^ k * b : Y.Fnˣ) : Y.Fn)))) :
    e.w (valAt y.1 ((b : Y.Fn) / a)) = 1 := by
  have h₀ : (k • D).IsEqn (below y.1) (eqn D (below y.1) ^ k) :=
    (D.exists_isEqn (below y.1)).choose_spec.nsmul k
  have hu {c : Y.Fnˣ} (hc : (k • D).IsEqn (below y.1) c) :
      UnitAt (below y.1) (((eqn D (below y.1))⁻¹ ^ k * c : Y.Fnˣ) : Y.Fn) := by
    have := h₀.iff_unitAt.1 hc
    rwa [div_eq_inv_mul, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← inv_pow] at this
  have e₁ : (((eqn D (below y.1))⁻¹ ^ k * b : Y.Fnˣ) : Y.Fn) =
      (b : Y.Fn) / a * (((eqn D (below y.1))⁻¹ ^ k * a : Y.Fnˣ) : Y.Fn) := by
    rw [Units.val_mul, Units.val_mul, mul_left_comm, div_mul_cancel₀ _ a.ne_zero]
  have pa := e.w.pos (valAt_ne_zero _ (hu ha))
  have pb := e.w.pos (valAt_ne_zero _ (hu hb))
  have e₂ := Real.log_injOn_pos pa pb h
  rw [e₁, valAt_mul _ (ha.iff_unitAt.1 hb).regAt (hu ha).regAt, map_mul] at e₂
  exact mul_right_cancel₀ pa.ne' (e₂.symm.trans (one_mul _).symm)

/- English proof (translation)
Introduce `F _ _ C Y A N hN L L' k cf ⟨_, r, hr, hc, hf⟩ ⟨_, r', hr', hc', hf'⟩`. Use `haveI := N.ar.isIntegral`. Take `⟨ρ, hρ, hj, -, hv, hx⟩` from `GlobalTheory.T.model_function_field_compatibility F Y N`. Establish `hR` using `isRatSec_lift N.j ρ hρ hj L.B hr.isRatSec`. Establish `hR'` using `isRatSec_lift N.j ρ hρ hj L'.B hr'.isRatSec`.

Establish `hP` using `presents_divOfRatSec L.isLB hR`. Establish `eρ (a b : Y.Fnˣ) : ρ ((Units.map ρ.symm.toMonoidHom b : N.X.functionField) / (Units.map ρ.symm.toMonoidHom a : N.X.functionField)) = (b : Y.Fn) / a`. Rewrite using `[map_div₀]`. Conclude with `congrArg₂ (· / ·) (ρ.apply_symm_apply _) (ρ.apply_symm_apply _)`. Use `⟨_, _, _, hP, ⟨L'.isLB, hR', fun j x hxj => ?_⟩, fun τ y' i j hi hj' => ?_⟩` and prove the remaining obligations.

Take `⟨i, hxi⟩` from `exists_chart L.isLB x`. Use `(hP.isEqn i x hxi).iff_unitAt.2 ((unitAt_iff (div_ne_zero (Units.ne_zero _) (Units.ne_zero _))).2 ⟨?_, ?_⟩)` and prove the remaining obligations. Use `GlobalTheory.T.regular_of_valuation_bounded_at_points F Y N hN (L.B.U i ⊓ L'.B.U j) _ (fun v e y yt h hU => ?_) x ⟨hxi, hxj⟩` and prove the remaining obligations. Establish `h₁ : ⊤ ≤ yt ⁻¹ᵁ L.B.U i` using `fun z hz => (hU hz).1`. Establish `h₂ : ⊤ ≤ yt ⁻¹ᵁ L'.B.U j` using `fun z hz => (hU hz).2`.

Rewrite using `[hv, eρ]`. Use `(w_div_eq_one e y (hr.isEqn _ _ (le_chart N L.B e y yt h (i := fun _ => i) h₁ trivial)) (hr'.isEqn _ _ (le_chart N L'.B e y yt h (i := fun _ => j) h₂ trivial)) ?_).le` and prove the remaining obligations. Combine the linear relations using `[hf v e y yt (fun _ => i) h h₁, hf' v e y yt (fun _ => j) h h₂]`. Rewrite using `[inv_div]`. Use `GlobalTheory.T.regular_of_valuation_bounded_at_points F Y N hN (L.B.U i ⊓ L'.B.U j) _ (fun v e y yt h hU => ?_) x ⟨hxi, hxj⟩` and prove the remaining obligations.

Establish `h₁ : ⊤ ≤ yt ⁻¹ᵁ L.B.U i` using `fun z hz => (hU hz).1`. Establish `h₂ : ⊤ ≤ yt ⁻¹ᵁ L'.B.U j` using `fun z hz => (hU hz).2`. Rewrite using `[hv, eρ]`. Use `(w_div_eq_one e y (hr'.isEqn _ _ (le_chart N L'.B e y yt h (i := fun _ => j) h₂ trivial)) (hr.isEqn _ _ (le_chart N L.B e y yt h (i := fun _ => i) h₁ trivial)) ?_).le` and prove the remaining obligations. Combine the linear relations using `[hf v e y yt (fun _ => i) h h₁, hf' v e y yt (fun _ => j) h h₂]`.

Take `⟨σ, rfl, y, hy⟩` from `GlobalTheory.T.complex_points_lift_model F Y N τ y'`. Establish `hu : under y' = N.j (under y)`. Express the relevant statement in the definitionally equal form `y'.1 _ = _`. Rewrite using `[hy]`. Both sides reduce to the same expression.

Establish `h₁ : under y ∈ (L.B.pull N.j).U fun _ => i` using `Set.mem_iInter.2 fun _ => by`. Express the relevant statement in the definitionally equal form `N.j (under y) ∈ L.B.U i`. Rewrite using `[← hu]`. Conclude with `mem_ptsIn.1 hi`. Establish `h₂ : under y ∈ (L'.B.pull N.j).U fun _ => j` using `Set.mem_iInter.2 fun _ => by`.

Express the relevant statement in the definitionally equal form `N.j (under y) ∈ L'.B.U j`. Rewrite using `[← hu]`. Conclude with `mem_ptsIn.1 hj'`. Establish `q₁` using `hr.isEqn _ _ h₁`. Establish `q₂` using `hr'.isEqn _ _ h₂`.

Establish `hg` using `(CartierDiv.isEqn_iff_generatesAt_inv.1 q₁).regularAt`. Establish `h₈ : ratVal (1 : Y.Fn) y = 1`. Establish `e` using `ratVal_fnOf (y := y) CxPts.mem_ptsIn_top trivial 1`. Rewrite `e` using `[map_one, CxPts.ev_one CxPts.mem_ptsIn_top]`. Then use the resulting hypothesis. Establish `e` using `(hc σ y y' _ _ hy h₁ hg).symm.trans (hc' σ y y' _ _ hy h₂ hg)`.

Rewrite `e` using `[inv_mul_cancel₀ (Units.ne_zero _), h₈, ← div_eq_inv_mul, norm_one, one_pow, one_mul]`. Establish `h0` using `ratVal_ne_zero (q₁.iff_unitAt.1 q₂)`. Establish `e'` using `congrArg Real.log e`. Rewrite `e'` using `[Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 h0)) (Real.exp_ne_zero _), Real.log_exp, Real.log_exp]`. Rewrite using `[Units.val_div_eq_div_val, hx σ y y' hy, eρ]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ratIsom_of_induced : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (N : TrueGeo.Model Y), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.X → ∀ (L L' : HermLB N.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced N L k cf → A.Induced N L' k cf → (haveI := N.ar.isIntegral; RatIsom L L') := by
  intro F _ _ C Y A N hN L L' k cf ⟨_, r, hr, hc, hf⟩ ⟨_, r', hr', hc', hf'⟩
  haveI := N.ar.isIntegral
  obtain ⟨ρ, hρ, hj, -, hv, hx⟩ := GlobalTheory.T.model_function_field_compatibility F Y N
  have hR := isRatSec_lift N.j ρ hρ hj L.B hr.isRatSec
  have hR' := isRatSec_lift N.j ρ hρ hj L'.B hr'.isRatSec
  have hP := presents_divOfRatSec L.isLB hR
  have eρ (a b : Y.Fnˣ) : ρ ((Units.map ρ.symm.toMonoidHom b : N.X.functionField) /
      (Units.map ρ.symm.toMonoidHom a : N.X.functionField)) = (b : Y.Fn) / a := by
    rw [map_div₀]
    exact congrArg₂ (· / ·) (ρ.apply_symm_apply _) (ρ.apply_symm_apply _)
  refine ⟨_, _, _, hP, ⟨L'.isLB, hR', fun j x hxj => ?_⟩, fun τ y' i j hi hj' => ?_⟩
  · obtain ⟨i, hxi⟩ := exists_chart L.isLB x
    refine (hP.isEqn i x hxi).iff_unitAt.2
      ((unitAt_iff (div_ne_zero (Units.ne_zero _) (Units.ne_zero _))).2 ⟨?_, ?_⟩)
    · refine GlobalTheory.T.regular_of_valuation_bounded_at_points F Y N hN (L.B.U i ⊓ L'.B.U j) _ (fun v e y yt h hU => ?_) x ⟨hxi, hxj⟩
      have h₁ : ⊤ ≤ yt ⁻¹ᵁ L.B.U i := fun z hz => (hU hz).1
      have h₂ : ⊤ ≤ yt ⁻¹ᵁ L'.B.U j := fun z hz => (hU hz).2
      rw [hv, eρ]
      refine (w_div_eq_one e y
        (hr.isEqn _ _ (le_chart N L.B e y yt h (i := fun _ => i) h₁ trivial))
        (hr'.isEqn _ _ (le_chart N L'.B e y yt h (i := fun _ => j) h₂ trivial)) ?_).le
      linarith [hf v e y yt (fun _ => i) h h₁, hf' v e y yt (fun _ => j) h h₂]
    · rw [inv_div]
      refine GlobalTheory.T.regular_of_valuation_bounded_at_points F Y N hN (L.B.U i ⊓ L'.B.U j) _ (fun v e y yt h hU => ?_) x ⟨hxi, hxj⟩
      have h₁ : ⊤ ≤ yt ⁻¹ᵁ L.B.U i := fun z hz => (hU hz).1
      have h₂ : ⊤ ≤ yt ⁻¹ᵁ L'.B.U j := fun z hz => (hU hz).2
      rw [hv, eρ]
      refine (w_div_eq_one e y
        (hr'.isEqn _ _ (le_chart N L'.B e y yt h (i := fun _ => j) h₂ trivial))
        (hr.isEqn _ _ (le_chart N L.B e y yt h (i := fun _ => i) h₁ trivial)) ?_).le
      linarith [hf v e y yt (fun _ => i) h h₁, hf' v e y yt (fun _ => j) h h₂]
  · obtain ⟨σ, rfl, y, hy⟩ := GlobalTheory.T.complex_points_lift_model F Y N τ y'
    have hu : under y' = N.j (under y) := by
      change y'.1 _ = _
      rw [hy]
      rfl
    have h₁ : under y ∈ (L.B.pull N.j).U fun _ => i := Set.mem_iInter.2 fun _ => by
      change N.j (under y) ∈ L.B.U i
      rw [← hu]
      exact mem_ptsIn.1 hi
    have h₂ : under y ∈ (L'.B.pull N.j).U fun _ => j := Set.mem_iInter.2 fun _ => by
      change N.j (under y) ∈ L'.B.U j
      rw [← hu]
      exact mem_ptsIn.1 hj'
    have q₁ := hr.isEqn _ _ h₁
    have q₂ := hr'.isEqn _ _ h₂
    have hg := (CartierDiv.isEqn_iff_generatesAt_inv.1 q₁).regularAt
    have h₈ : ratVal (1 : Y.Fn) y = 1 := by
      have e := ratVal_fnOf (y := y) CxPts.mem_ptsIn_top trivial 1
      rwa [map_one, CxPts.ev_one CxPts.mem_ptsIn_top] at e
    have e := (hc σ y y' _ _ hy h₁ hg).symm.trans (hc' σ y y' _ _ hy h₂ hg)
    rw [inv_mul_cancel₀ (Units.ne_zero _), h₈, ← div_eq_inv_mul, norm_one, one_pow, one_mul] at e
    have h0 := ratVal_ne_zero (q₁.iff_unitAt.1 q₂)
    have e' := congrArg Real.log e
    rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 h0)) (Real.exp_ne_zero _), Real.log_exp,
      Real.log_exp] at e'
    rw [Units.val_div_eq_div_val, hx σ y y' hy, eρ]
    linarith

end GlobalTheory.TrueGeo.InducedIsom
