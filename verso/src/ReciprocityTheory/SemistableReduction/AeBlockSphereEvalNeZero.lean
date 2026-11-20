import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `f hf`. Use `Filter.Eventually.of_forall fun x => ?_` and prove the remaining obligations.

Rewrite `hf`, the goal using `[MvPolynomial.eq_C_of_isEmpty f]`. Simplify using `using hf`. Consider the case `succ m ih`. Introduce `f hf`. Use `set P := MvPolynomial.finSuccEquiv ℂ m f with hPdef`.

Establish `hP : P ≠ 0`. Introduce `h`. Apply `hf` to reduce the goal to its premises. Conclude with `(MvPolynomial.finSuccEquiv ℂ m).injective (by rw [← hPdef, h, map_zero])`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, P.coeff k ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hP (Polynomial.ext fun k => by simpa using h k)`. Establish `h1` using `ih _ hk`. Use `set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) 0`.

Establish `he : MeasurePreserving e volume volume` using `volume_preserving_piFinSuccAbove _ 0`. Establish `hmeas : MeasurableSet {z : ℂ × (Fin m → ℂ) | MvPolynomial.eval (e.symm z) f ≠ 0}` using `((MvPolynomial.continuous_eval f).measurable.comp e.symm.measurable) (measurableSet_singleton 0).compl`. Establish `key : ∀ᵐ z ∂(volume : Measure (ℂ × (Fin m → ℂ))), MvPolynomial.eval (e.symm z) f ≠ 0`. Rewrite using `[Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas]`. Rewrite using `[Measure.ae_ae_comm (p := fun y s => MvPolynomial.eval (e.symm (y, s)) f ≠ 0) hmeas]`.

Use `filter_upwards [h1] with s hs`. Establish `hQ : Polynomial.map (MvPolynomial.eval s) P ≠ 0`. Introduce `h`. Apply `hs` to reduce the goal to its premises. Use `congrArg (fun q => Polynomial.coeff q k) h` as an intermediate fact.

Simplify `this` using `[Polynomial.coeff_map]`. Establish `hfin : ({y : ℂ | Polynomial.eval y (Polynomial.map (MvPolynomial.eval s) P) = 0}).Finite` using `Polynomial.finite_setOfPred_isRoot hQ`. Establish `hnull` using `hfin.measure_zero (volume : Measure ℂ)`. Rewrite `hnull` using `[measure_eq_zero_iff_ae_notMem]`. Use `filter_upwards [hnull] with y hy`.

Establish `hc : (e.symm (y, s) : Fin (m + 1) → ℂ) = Fin.cons y s`. Simplify using `[e, MeasurableEquiv.piFinSuccAbove_symm_apply]`. Both sides reduce to the same expression. Rewrite using `[hc, MvPolynomial.eval_eq_eval_mv_eval']`. Conclude with `hy`.

Use `he.quasiMeasurePreserving.ae key` as an intermediate fact. Use `filter_upwards [this] with x hx`. Simplify using `using hx`.
-/
theorem ae_eval_ne_zero_of_ne_zero_fin : ∀ (m : ℕ) (f : MvPolynomial (Fin m) ℂ), f ≠ 0 →
    ∀ᵐ x ∂(volume : Measure (Fin m → ℂ)), MvPolynomial.eval x f ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro f hf
    refine Filter.Eventually.of_forall fun x => ?_
    rw [MvPolynomial.eq_C_of_isEmpty f] at hf ⊢
    simpa using hf
  | succ m ih =>
    intro f hf
    set P := MvPolynomial.finSuccEquiv ℂ m f with hPdef
    have hP : P ≠ 0 := by
      intro h
      apply hf
      exact (MvPolynomial.finSuccEquiv ℂ m).injective (by rw [← hPdef, h, map_zero])
    obtain ⟨k, hk⟩ : ∃ k, P.coeff k ≠ 0 := by
      by_contra h
      push Not at h
      exact hP (Polynomial.ext fun k => by simpa using h k)
    have h1 := ih _ hk
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) 0
    have he : MeasurePreserving e volume volume := volume_preserving_piFinSuccAbove _ 0
    have hmeas : MeasurableSet {z : ℂ × (Fin m → ℂ) | MvPolynomial.eval (e.symm z) f ≠ 0} :=
      ((MvPolynomial.continuous_eval f).measurable.comp e.symm.measurable)
        (measurableSet_singleton 0).compl
    have key : ∀ᵐ z ∂(volume : Measure (ℂ × (Fin m → ℂ))), MvPolynomial.eval (e.symm z) f ≠ 0 := by
      rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas]
      rw [Measure.ae_ae_comm (p := fun y s => MvPolynomial.eval (e.symm (y, s)) f ≠ 0) hmeas]
      filter_upwards [h1] with s hs
      have hQ : Polynomial.map (MvPolynomial.eval s) P ≠ 0 := by
        intro h
        apply hs
        have := congrArg (fun q => Polynomial.coeff q k) h
        simpa [Polynomial.coeff_map] using this
      have hfin : ({y : ℂ | Polynomial.eval y (Polynomial.map (MvPolynomial.eval s) P) = 0}).Finite :=
        Polynomial.finite_setOfPred_isRoot hQ
      have hnull := hfin.measure_zero (volume : Measure ℂ)
      rw [measure_eq_zero_iff_ae_notMem] at hnull
      filter_upwards [hnull] with y hy
      have hc : (e.symm (y, s) : Fin (m + 1) → ℂ) = Fin.cons y s := by
        simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl
      rw [hc, MvPolynomial.eval_eq_eval_mv_eval']
      exact hy
    have := he.quasiMeasurePreserving.ae key
    filter_upwards [this] with x hx
    simpa using hx

/- English proof (translation)
Use `set e := Fintype.equivFin ι`. Use `set g := MvPolynomial.rename e f`. Establish `hg : g ≠ 0`. Introduce `h`. Apply `hf` to reduce the goal to its premises.

Conclude with `MvPolynomial.rename_injective _ e.injective (by rw [map_zero]; exact h)`. Use `set L' : V ≃ₗ[ℂ] (Fin (Fintype.card ι) → ℂ) := L.trans (LinearEquiv.funCongrLeft ℂ ℂ e.symm)`. Establish `hL' : ∀ x, MvPolynomial.eval (L' x) g = MvPolynomial.eval (L x) f`. Introduce `x`. Establish `hc : (L' x : Fin (Fintype.card ι) → ℂ) ∘ e = L x`.

Use function extensionality and compare the values at `i`. Simplify using `[L', LinearEquiv.funCongrLeft_apply]`. Simplify using `only [g, MvPolynomial.eval_rename, hc]`. Establish `hac : μ.map L' ≪ volume` using `Measure.absolutelyContinuous_isAddHaarMeasure _ _`. Establish `h1 : ∀ᵐ y ∂(μ.map L'), MvPolynomial.eval y g ≠ 0` using `hac.ae_le (ae_eval_ne_zero_of_ne_zero_fin _ g hg)`.

Establish `hmeasL : Measurable L'` using `L'.toContinuousLinearEquiv.continuous.measurable`. Establish `hmeasS : MeasurableSet {y : Fin (Fintype.card ι) → ℂ | MvPolynomial.eval y g ≠ 0}` using `(MvPolynomial.continuous_eval g).measurable (measurableSet_singleton 0).compl`. Rewrite `h1` using `[ae_map_iff hmeasL.aemeasurable hmeasS]`. Use `filter_upwards [h1] with x hx`. Rewrite using `[← hL']` and apply the resulting hypothesis.
-/
theorem ae_eval_ne_zero_linear {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] {ι : Type*} [Fintype ι] (L : V ≃ₗ[ℂ] (ι → ℂ))
    (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    ∀ᵐ x ∂μ, MvPolynomial.eval (L x) f ≠ 0 := by
  set e := Fintype.equivFin ι
  set g := MvPolynomial.rename e f
  have hg : g ≠ 0 := by
    intro h
    apply hf
    exact MvPolynomial.rename_injective _ e.injective (by rw [map_zero]; exact h)
  set L' : V ≃ₗ[ℂ] (Fin (Fintype.card ι) → ℂ) := L.trans (LinearEquiv.funCongrLeft ℂ ℂ e.symm)
  have hL' : ∀ x, MvPolynomial.eval (L' x) g = MvPolynomial.eval (L x) f := by
    intro x
    have hc : (L' x : Fin (Fintype.card ι) → ℂ) ∘ e = L x := by
      funext i
      simp [L', LinearEquiv.funCongrLeft_apply]
    simp only [g, MvPolynomial.eval_rename, hc]
  have hac : μ.map L' ≪ volume := Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have h1 : ∀ᵐ y ∂(μ.map L'), MvPolynomial.eval y g ≠ 0 :=
    hac.ae_le (ae_eval_ne_zero_of_ne_zero_fin _ g hg)
  have hmeasL : Measurable L' := L'.toContinuousLinearEquiv.continuous.measurable
  have hmeasS : MeasurableSet {y : Fin (Fintype.card ι) → ℂ | MvPolynomial.eval y g ≠ 0} :=
    (MvPolynomial.continuous_eval g).measurable (measurableSet_singleton 0).compl
  rw [ae_map_iff hmeasL.aemeasurable hmeasS] at h1
  filter_upwards [h1] with x hx
  rwa [← hL']

/- English proof (translation)
Rewrite using `[MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Establish `h1 : ∏ p, (r p.1 * x p) ^ s p = (∏ b, r b ^ a b) * ∏ p, x p ^ s p`. Repeatedly rewrite using `[mul_pow, Finset.prod_mul_distrib]`. Use `congr 1`.

Rewrite using `[Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `show ∏ j, r b ^ s (b, j) = r b ^ a b`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hF s hs b]`. Rewrite using `[h1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_blockScale_eq_prod_pow_mul {B n : ℕ} (a : Fin B → ℕ) (F : MvPolynomial (Fin B × Fin n) ℂ)
    (hF : IsMultiHomogeneous a F) (r : Fin B → ℂ) (x : Fin B × Fin n → ℂ) :
    MvPolynomial.eval (fun p => r p.1 * x p) F = (∏ b, r b ^ a b) * MvPolynomial.eval x F := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h1 : ∏ p, (r p.1 * x p) ^ s p = (∏ b, r b ^ a b) * ∏ p, x p ^ s p := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun b _ => ?_
    show ∏ j, r b ^ s (b, j) = r b ^ a b
    rw [Finset.prod_pow_eq_pow_sum, hF s hs b]
  rw [h1]
  ring

def blockCoordEquiv (B n : ℕ) : (Fin B → EuclideanSpace ℂ (Fin n)) ≃ₗ[ℂ] (Fin B × Fin n → ℂ) :=
  (LinearEquiv.piCongrRight fun _ => WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).trans
    (LinearEquiv.curry ℂ ℂ (Fin B) (Fin n)).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blockCoordEquiv_apply {B n : ℕ} (y : Fin B → EuclideanSpace ℂ (Fin n)) (p : Fin B × Fin n) :
    blockCoordEquiv B n y p = WithLp.ofLp (y p.1) p.2 := rfl

/- English proof (translation)
Use `set E := EuclideanSpace ℂ (Fin n)`. Use `set νS := (volume : Measure E).toSphere`. Use `set ρ := Measure.volumeIoiPow (Module.finrank ℝ E - 1)`. Use `set Z : Set (Fin B → sphere (0 : E) 1) := {z | MvPolynomial.eval (blockPoint z) F = 0}`. Establish `hZ : MeasurableSet Z`.

Establish `: Continuous fun z : Fin B → sphere (0 : E) 1 => MvPolynomial.eval (blockPoint z) F`. Use `(MvPolynomial.continuous_eval F).comp ?_` and prove the remaining obligations. Use `continuous_pi fun p => ?_` and prove the remaining obligations. Unfold `blockPoint spherePoint`. Use `fun_prop`.

Conclude with `this.measurable (measurableSet_singleton 0)`. Establish `: (Measure.pi fun _ : Fin B => (volume : Measure E)).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`. Establish `: IsFiniteMeasure νS` using `by show IsFiniteMeasure ((volume : Measure E).toSphere); infer_instance`. Establish `: SigmaFinite ρ` using `by show SigmaFinite (Measure.volumeIoiPow (Module.finrank ℝ E - 1)); infer_instance`. Establish `hlin : ∀ᵐ y ∂(Measure.pi fun _ : Fin B => (volume : Measure E)), MvPolynomial.eval (blockCoordEquiv B n y) F ≠ 0` using `ae_eval_ne_zero_linear _ (blockCoordEquiv B n) F hF0`.

Use `set S : Set (Fin B → E) := {y | MvPolynomial.eval (blockCoordEquiv B n y) F = 0}`. Establish `hS0 : (Measure.pi fun _ : Fin B => (volume : Measure E)) S = 0`. Rewrite using `[measure_eq_zero_iff_ae_notMem]`. Use `filter_upwards [hlin] with y hy`. Conclude with `hy`.

Establish `hSm : MeasurableSet S`. Establish `: Continuous fun y : Fin B → E => MvPolynomial.eval (blockCoordEquiv B n y) F`. Use `(MvPolynomial.continuous_eval F).comp ?_` and prove the remaining obligations. Conclude with `(blockCoordEquiv B n).toContinuousLinearEquiv.continuous`. Conclude with `this.measurable (measurableSet_singleton 0)`.

Establish `h1` using `Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure E)`. Establish `hprodSF : SigmaFinite (νS.prod ρ)` using `inferInstance`. Establish `hT` using `measurePreserving_pi (hν := fun _ => hprodSF) (fun _ : Fin B => (volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)) (fun _ => νS.prod ρ) (fun _ => h1)`. Establish `hA` using `measurePreserving_arrowProdEquivProdArrow (sphere (0 : E) 1) (Set.Ioi (0 : ℝ)) (Fin B) (fun _ => νS) (fun _ => ρ)`. Use `set A := MeasurableEquiv.arrowProdEquivProdArrow (sphere (0 : E) 1) (Set.Ioi (0 : ℝ)) (Fin B)`.

Use `set T : (Fin B → ({0}ᶜ : Set E)) → (Fin B → sphere (0 : E) 1 × Set.Ioi (0 : ℝ)) := fun x b => homeomorphUnitSphereProd E (x b)`. Establish `hW : MeasurableSet (Z ×ˢ (Set.univ : Set (Fin B → Set.Ioi (0 : ℝ))))` using `hZ.prod MeasurableSet.univ`. Establish `hAW : MeasurableSet (A ⁻¹' (Z ×ˢ Set.univ))` using `A.measurable hW`. Establish `e1` using `Measure.prod_prod (μ := Measure.pi fun _ : Fin B => νS) (ν := Measure.pi fun _ : Fin B => ρ) Z Set.univ`. Rewrite `e1` using `[← hA.measure_preimage hW.nullMeasurableSet, ← hT.measure_preimage hAW.nullMeasurableSet]`.

Use `set G : (Fin B → ({0}ᶜ : Set E)) → (Fin B → E) := fun x b => (x b : E)`. Establish `hsub : T ⁻¹' (A ⁻¹' (Z ×ˢ Set.univ)) ⊆ G ⁻¹' S`. Introduce `x hx`. Simplify using `only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true] at hx`. Establish `hx' : MvPolynomial.eval (blockPoint fun b => (homeomorphUnitSphereProd E (x b)).1) F = 0`.

Simplify `hx` using `[A, T, Z, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]`. Establish `hcoord : blockCoordEquiv B n (G x) = fun p => ((‖(x p.1 : E)‖ : ℝ) : ℂ) * blockPoint (fun b => (homeomorphUnitSphereProd E (x b)).1) p`. Use function extensionality and compare the values at `p`. Establish `hne : ‖(x p.1 : E)‖ ≠ 0` using `norm_ne_zero_iff.2 (x p.1).2`. Simplify using `only [blockCoordEquiv_apply, G, blockPoint, spherePoint, homeomorphUnitSphereProd_apply_fst_coe]`.

Rewrite using `[← Complex.coe_smul, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hne, Complex.ofReal_one, one_mul]`. Use `show MvPolynomial.eval (blockCoordEquiv B n (G x)) F = 0`. Establish `hsc` using `eval_blockScale_eq_prod_pow_mul a F hF (fun b => ((‖(x b : E)‖ : ℝ) : ℂ)) (blockPoint (fun b => (homeomorphUnitSphereProd E (x b)).1))`. Rewrite using `[hcoord, hsc, hx', mul_zero]`. Establish `hmap : ∀ _ : Fin B, ((volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map Subtype.val = (volume : Measure E).restrict {0}ᶜ` using `fun _ => map_comap_subtype_coe (measurableSet_singleton 0).compl _`.

Establish `hmSF : ∀ i : Fin B, SigmaFinite (((volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map Subtype.val)`. Introduce `i`. Rewrite using `[hmap i]`. Use `infer_instance`. Establish `hG : (Measure.pi fun _ : Fin B => (volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map G = Measure.pi fun _ : Fin B => (volume : Measure E).restrict {0}ᶜ`.

Rewrite using `[Measure.pi_map_pi (hμ := hmSF) (fun _ => measurable_subtype_coe.aemeasurable)]`. Conclude with `congrArg _ (funext hmap)`. Establish `hGm : Measurable G` using `measurable_pi_lambda _ fun b => measurable_subtype_coe.comp (measurable_pi_apply b)`. Establish `hzero : (Measure.pi fun _ : Fin B => (volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)) (T ⁻¹' (A ⁻¹' (Z ×ˢ Set.univ))) = 0`. Use `measure_mono_null hsub ?_` and prove the remaining obligations.

Rewrite using `[← Measure.map_apply hGm hSm, hG, ← Measure.restrict_pi_pi]`. Conclude with `nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hS0.le)`. Establish `hρ : ρ Set.univ ≠ 0`. Introduce `h`. Establish `h2` using `measure_mono_null (Set.subset_univ (Set.Iio (⟨1, by norm_num⟩ : Set.Ioi (0 : ℝ)))) h`.

Establish `h3` using `Measure.volumeIoiPow_apply_Iio (Module.finrank ℝ E - 1) ⟨1, by norm_num⟩`. Rewrite `h2` using `[show ρ (Set.Iio ⟨1, by norm_num⟩) = _ from h3]`. Rewrite `h2` using `[ENNReal.ofReal_eq_zero]`. Establish `h4 : (0 : ℝ) < (1 : ℝ) ^ (Module.finrank ℝ E - 1 + 1) / ((Module.finrank ℝ E - 1 : ℕ) + 1)`. Check the signs of the components of the expression.

Conclude with `absurd h2 (not_le.2 h4)`. Establish `hpiρ : (Measure.pi fun _ : Fin B => ρ) Set.univ ≠ 0`. Rewrite using `[Measure.pi_univ]`. Conclude with `Finset.prod_ne_zero_iff.2 fun _ _ => hρ`. Rewrite `e1` using `[hzero]`.

Establish `hZ0 : (Measure.pi fun _ : Fin B => νS) Z = 0`. Break down `mul_eq_zero.1 e1.symm with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hpiρ`. Rewrite `hZ0` using `[measure_eq_zero_iff_ae_notMem]`.

Use `filter_upwards [hZ0] with z hz`. Conclude with `hz`.
-/
theorem ae_toSphere (B n : ℕ) (a : Fin B → ℕ) (F : MvPolynomial (Fin B × Fin n) ℂ)
    (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    ∀ᵐ z ∂(Measure.pi fun _ : Fin B => (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere),
      MvPolynomial.eval (blockPoint z) F ≠ 0 := by
  set E := EuclideanSpace ℂ (Fin n)
  set νS := (volume : Measure E).toSphere
  set ρ := Measure.volumeIoiPow (Module.finrank ℝ E - 1)
  set Z : Set (Fin B → sphere (0 : E) 1) := {z | MvPolynomial.eval (blockPoint z) F = 0}
  have hZ : MeasurableSet Z := by
    have : Continuous fun z : Fin B → sphere (0 : E) 1 => MvPolynomial.eval (blockPoint z) F := by
      refine (MvPolynomial.continuous_eval F).comp ?_
      refine continuous_pi fun p => ?_
      unfold blockPoint spherePoint
      fun_prop
    exact this.measurable (measurableSet_singleton 0)
  have : (Measure.pi fun _ : Fin B => (volume : Measure E)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have : IsFiniteMeasure νS := by show IsFiniteMeasure ((volume : Measure E).toSphere); infer_instance
  have : SigmaFinite ρ := by show SigmaFinite (Measure.volumeIoiPow (Module.finrank ℝ E - 1)); infer_instance
  have hlin : ∀ᵐ y ∂(Measure.pi fun _ : Fin B => (volume : Measure E)),
      MvPolynomial.eval (blockCoordEquiv B n y) F ≠ 0 :=
    ae_eval_ne_zero_linear _ (blockCoordEquiv B n) F hF0
  set S : Set (Fin B → E) := {y | MvPolynomial.eval (blockCoordEquiv B n y) F = 0}
  have hS0 : (Measure.pi fun _ : Fin B => (volume : Measure E)) S = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hlin] with y hy
    exact hy
  have hSm : MeasurableSet S := by
    have : Continuous fun y : Fin B → E => MvPolynomial.eval (blockCoordEquiv B n y) F := by
      refine (MvPolynomial.continuous_eval F).comp ?_
      exact (blockCoordEquiv B n).toContinuousLinearEquiv.continuous
    exact this.measurable (measurableSet_singleton 0)
  have h1 := Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure E)
  have hprodSF : SigmaFinite (νS.prod ρ) := inferInstance
  have hT := measurePreserving_pi (hν := fun _ => hprodSF)
    (fun _ : Fin B => (volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E))
    (fun _ => νS.prod ρ) (fun _ => h1)
  have hA := measurePreserving_arrowProdEquivProdArrow (sphere (0 : E) 1) (Set.Ioi (0 : ℝ)) (Fin B)
    (fun _ => νS) (fun _ => ρ)
  set A := MeasurableEquiv.arrowProdEquivProdArrow (sphere (0 : E) 1) (Set.Ioi (0 : ℝ)) (Fin B)
  set T : (Fin B → ({0}ᶜ : Set E)) → (Fin B → sphere (0 : E) 1 × Set.Ioi (0 : ℝ)) :=
    fun x b => homeomorphUnitSphereProd E (x b)
  have hW : MeasurableSet (Z ×ˢ (Set.univ : Set (Fin B → Set.Ioi (0 : ℝ)))) :=
    hZ.prod MeasurableSet.univ
  have hAW : MeasurableSet (A ⁻¹' (Z ×ˢ Set.univ)) := A.measurable hW
  have e1 := Measure.prod_prod (μ := Measure.pi fun _ : Fin B => νS)
    (ν := Measure.pi fun _ : Fin B => ρ) Z Set.univ
  rw [← hA.measure_preimage hW.nullMeasurableSet, ← hT.measure_preimage hAW.nullMeasurableSet] at e1
  set G : (Fin B → ({0}ᶜ : Set E)) → (Fin B → E) := fun x b => (x b : E)
  have hsub : T ⁻¹' (A ⁻¹' (Z ×ˢ Set.univ)) ⊆ G ⁻¹' S := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true] at hx
    have hx' : MvPolynomial.eval (blockPoint fun b => (homeomorphUnitSphereProd E (x b)).1) F = 0 := by
      simpa [A, T, Z, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow] using hx
    have hcoord : blockCoordEquiv B n (G x) = fun p => ((‖(x p.1 : E)‖ : ℝ) : ℂ) *
        blockPoint (fun b => (homeomorphUnitSphereProd E (x b)).1) p := by
      funext p
      have hne : ‖(x p.1 : E)‖ ≠ 0 := norm_ne_zero_iff.2 (x p.1).2
      simp only [blockCoordEquiv_apply, G, blockPoint, spherePoint, homeomorphUnitSphereProd_apply_fst_coe]
      rw [← Complex.coe_smul, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc,
        ← Complex.ofReal_mul, mul_inv_cancel₀ hne, Complex.ofReal_one, one_mul]
    show MvPolynomial.eval (blockCoordEquiv B n (G x)) F = 0
    have hsc := eval_blockScale_eq_prod_pow_mul a F hF (fun b => ((‖(x b : E)‖ : ℝ) : ℂ))
      (blockPoint (fun b => (homeomorphUnitSphereProd E (x b)).1))
    rw [hcoord, hsc, hx', mul_zero]
  have hmap : ∀ _ : Fin B, ((volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map
      Subtype.val = (volume : Measure E).restrict {0}ᶜ :=
    fun _ => map_comap_subtype_coe (measurableSet_singleton 0).compl _
  have hmSF : ∀ i : Fin B, SigmaFinite
      (((volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map Subtype.val) := by
    intro i; rw [hmap i]; infer_instance
  have hG : (Measure.pi fun _ : Fin B =>
      (volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map G =
      Measure.pi fun _ : Fin B => (volume : Measure E).restrict {0}ᶜ := by
    rw [Measure.pi_map_pi (hμ := hmSF) (fun _ => measurable_subtype_coe.aemeasurable)]
    exact congrArg _ (funext hmap)
  have hGm : Measurable G := measurable_pi_lambda _ fun b => measurable_subtype_coe.comp
    (measurable_pi_apply b)
  have hzero : (Measure.pi fun _ : Fin B =>
      (volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E))
      (T ⁻¹' (A ⁻¹' (Z ×ˢ Set.univ))) = 0 := by
    refine measure_mono_null hsub ?_
    rw [← Measure.map_apply hGm hSm, hG, ← Measure.restrict_pi_pi]
    exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hS0.le)
  have hρ : ρ Set.univ ≠ 0 := by
    intro h
    have h2 := measure_mono_null (Set.subset_univ (Set.Iio (⟨1, by norm_num⟩ : Set.Ioi (0 : ℝ)))) h
    have h3 := Measure.volumeIoiPow_apply_Iio (Module.finrank ℝ E - 1) ⟨1, by norm_num⟩
    rw [show ρ (Set.Iio ⟨1, by norm_num⟩) = _ from h3] at h2
    rw [ENNReal.ofReal_eq_zero] at h2
    have h4 : (0 : ℝ) < (1 : ℝ) ^ (Module.finrank ℝ E - 1 + 1) / ((Module.finrank ℝ E - 1 : ℕ) + 1) := by
      positivity
    exact absurd h2 (not_le.2 h4)
  have hpiρ : (Measure.pi fun _ : Fin B => ρ) Set.univ ≠ 0 := by
    rw [Measure.pi_univ]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => hρ
  rw [hzero] at e1
  have hZ0 : (Measure.pi fun _ : Fin B => νS) Z = 0 := by
    rcases mul_eq_zero.1 e1.symm with h | h
    · exact h
    · exact absurd h hpiρ
  rw [measure_eq_zero_iff_ae_notMem] at hZ0
  filter_upwards [hZ0] with z hz
  exact hz

/- English proof (translation)
Unfold `blockSphereProb`. Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Rewrite using `[Measure.smul_apply, Measure.pi_pi, smul_eq_mul]`. Simplify using `only [sphereProb, ProbabilityTheory.cond_apply MeasurableSet.univ, Set.univ_inter, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem blockSphereMeasure_eq (B n : ℕ) :
    blockSphereProb B n = ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ)⁻¹ ^ B •
      Measure.pi fun _ : Fin B => (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
  unfold blockSphereProb
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [sphereProb, ProbabilityTheory.cond_apply MeasurableSet.univ, Set.univ_inter,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/- English proof (translation)
Rewrite using `[blockSphereMeasure_eq]`. Conclude with `Measure.ae_smul_measure (ae_toSphere B n a F hF0 hF) _`.
-/
theorem ae_blockSphere_eval_ne_zero (B n : ℕ) (a : Fin B → ℕ) (F : MvPolynomial (Fin B × Fin n) ℂ)
    (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    ∀ᵐ z ∂(blockSphereProb B n), MvPolynomial.eval (blockPoint z) F ≠ 0 := by
  rw [blockSphereMeasure_eq]
  exact Measure.ae_smul_measure (ae_toSphere B n a F hF0 hF) _

end ReciprocityTheory.MultiplicativeHeights
