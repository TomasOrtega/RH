import ReciprocityTheory.SemistableReduction.IntCoresA

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric

def BlockPoly (k n : ℕ) (a : Fin k → ℕ) (F : (Fin k → Fin n → ℂ) → ℂ) : Prop :=
  Continuous F ∧ ∀ (b : Fin k) (p : Fin k → Fin n → ℂ), ∃ g : MvPolynomial (Fin n) ℂ,
    g.IsHomogeneous (a b) ∧ ∀ w, F (Function.update p b w) = MvPolynomial.eval w g

def onSpheres {k n : ℕ} (F : (Fin k → Fin n → ℂ) → ℂ) (z : Fin k → UnitSphereC n) : ℂ :=
  F fun b => spherePoint (z b)

/- English proof (translation)
Use `⟨hF.1.comp (continuous_const.finCons continuous_id), fun b p => ?_⟩` and prove the remaining obligations. Take `⟨g, hg, hgF⟩` from `hF.2 b.succ (Fin.cons v p)`. Use `⟨g, hg, fun w => ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Fin.cons_update]`.

Conclude with `hgF w`.
-/
theorem BlockPoly.restrict {k n : ℕ} {a : Fin (k + 1) → ℕ} {F : (Fin (k + 1) → Fin n → ℂ) → ℂ}
    (hF : BlockPoly (k + 1) n a F) (v : Fin n → ℂ) :
    BlockPoly k n (fun j => a j.succ) (fun p => F (Fin.cons v p)) := by
  refine ⟨hF.1.comp (continuous_const.finCons continuous_id), fun b p => ?_⟩
  obtain ⟨g, hg, hgF⟩ := hF.2 b.succ (Fin.cons v p)
  refine ⟨g, hg, fun w => ?_⟩
  simp only
  rw [Fin.cons_update]
  exact hgF w

/- English proof (translation)
Use `haveI : IsFiniteMeasure (sphereProb n) := by unfold sphereProb; infer_instance`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `a F hF z0 hz0`.

Establish `hconst : ∀ z : Fin 0 → UnitSphereC n, onSpheres F z = onSpheres F z0`. Introduce `z`. Unfold `onSpheres`. Use `congr 1`. Use function extensionality and compare the values at `b`.

Conclude with `b.elim0`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Repeatedly rewrite using `[hconst]`. Conclude with `integrable_const _`. Repeatedly rewrite using `[hconst]`.

Simplify using `[hz0]`. Consider the case `succ k ih`. Introduce `a F hF z0 hz0`. Use `set μ := sphereProb n with hμ`. Use `set ν := Measure.pi fun _ : Fin k => sphereProb n with hν`.

Set `e` to `MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => UnitSphereC n) 0`. Establish `mp : MeasurePreserving e (Measure.pi fun _ : Fin (k + 1) => sphereProb n) (μ.prod ν)` using `measurePreserving_piFinSuccAbove (fun _ => sphereProb n) 0`. Set `e2` to `e.trans MeasurableEquiv.prodComm`. Establish `mp2 : MeasurePreserving e2 (Measure.pi fun _ : Fin (k + 1) => sphereProb n) (ν.prod μ)` using `(Measure.measurePreserving_swap).comp mp`. Establish `hcont : Continuous (onSpheres F : (Fin (k + 1) → UnitSphereC n) → ℂ)` using `hF.1.comp (continuous_pi fun b => (continuous_spherePoint n).comp (continuous_apply b))`.

Set `H : (Fin k → UnitSphereC n) × UnitSphereC n → ℂ` to `fun q => onSpheres F (e2.symm q)`. Establish `hHm : Measurable H` using `hcont.measurable.comp e2.symm.measurable`. Establish `hsymm : ∀ z' w, e2.symm (z', w) = Fin.cons w z'`. Introduce `z' w`. Simplify using `[e2, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero']`.

Both sides reduce to the same expression. Establish `hH : ∀ z' w, H (z', w) = F (Fin.cons (spherePoint w) (fun b => spherePoint (z' b)))`. Introduce `z' w`. Simplify using `only [H, onSpheres, hsymm]`. Use `congr 1`.

Use function extensionality and compare the values at `b`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) b <;> simp`. Establish `hcomp : ∀ z, onSpheres F z = H (e2 z)`. Introduce `z`. Simplify using `only [H, MeasurableEquiv.symm_apply_apply]`.

Use `set v0 := spherePoint (z0 0) with hv0`. Establish `hR` using `hF.restrict v0`. Establish `hG : ∀ z', onSpheres (fun p => F (Fin.cons v0 p)) z' = H (z', z0 0)`. Introduce `z'`. Rewrite using `[hH]`.

Both sides reduce to the same expression. Establish `hz0' : onSpheres (fun p => F (Fin.cons v0 p)) (fun j => z0 j.succ) ≠ 0`. Simplify using `only [onSpheres] at hz0 ⊢`. Use `hz0 using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `b`.

Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) b <;> simp [v0]`. Take `⟨ihInt, ihNull⟩` from `ih _ _ hR _ hz0'`. Rewrite `ihInt`, `ihNull` using `[hG]`. Establish `hgood : ∀ᵐ z' ∂ν, H (z', z0 0) ≠ 0`. Rewrite using `[ae_iff]`.

Simplify using `using ihNull`. Establish `hslice : ∀ z', H (z', z0 0) ≠ 0 → Integrable (fun w => Real.log ‖H (z', w)‖) μ ∧ Real.log ‖H (z', z0 0)‖ - (a 0 : ℝ) / 2 * (harmonic (n - 1) : ℝ) ≤ ∫ w, Real.log ‖H (z', w)‖ ∂μ ∧ μ {w | H (z', w) = 0} = 0`. Introduce `z' hz'`. Take `⟨g, hg, hgF⟩` from `hF.2 0 (Fin.cons 0 (fun b => spherePoint (z' b)))`. Establish `hHw : ∀ w, H (z', w) = MvPolynomial.eval (spherePoint w) g`.

Introduce `w`. Rewrite using `[hH, ← hgF, Fin.update_cons_zero]`. Establish `hu : ‖(z0 0 : EuclideanSpace ℂ (Fin n))‖ = 1` using `norm_eq_of_mem_sphere _`. Establish `hgu : MvPolynomial.eval (WithLp.ofLp (z0 0 : EuclideanSpace ℂ (Fin n))) g ≠ 0`. Rewrite `hz'` using `[hHw]`.

Conclude with `hz'`. Take `⟨hI, hL⟩` from `hSJ n (a 0) g _ hg hu hgu`. Establish `hN` using `sphere_zero_null hSJ g hg _ hu hgu`. Repeatedly rewrite using `[hHw]`. Conclude with `⟨hI, hL, hN⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨C, hC⟩ : ∃ C, ∀ z, ‖onSpheres F z‖ ≤ C := by`. Take `⟨C, hC⟩` from `isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn`. Conclude with `⟨C, fun z => hC z (Set.mem_univ _)⟩`. Use `set M := Real.log (max C 1) with hMdef`. Establish `hM0 : 0 ≤ M` using `Real.log_nonneg (le_max_right _ _)`.

Establish `hLM : ∀ q, Real.log ‖H q‖ ≤ M`. Introduce `q`. Break down `(norm_nonneg (H q)).eq_or_lt with h0 | hpos` into its components or cases. Rewrite using `[← h0, Real.log_zero]`. Conclude with `hM0`.

Conclude with `Real.log_le_log hpos ((hC _).trans (le_max_left _ _))`. Establish `habs : ∀ q, ‖Real.log ‖H q‖‖ ≤ 2 * M - Real.log ‖H q‖`. Introduce `q`. Rewrite using `[Real.norm_eq_abs]`. Use `hLM q` as an intermediate fact.

Break down `le_total 0 (Real.log ‖H q‖) with h | h` into its components or cases. Rewrite using `[abs_of_nonneg h]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[abs_of_nonpos h]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hfm : AEStronglyMeasurable (fun q => Real.log ‖H q‖) (ν.prod μ)` using `(Real.measurable_log.comp hHm.norm).aestronglyMeasurable`. Establish `hInt2 : Integrable (fun q => Real.log ‖H q‖) (ν.prod μ)`. Rewrite using `[integrable_prod_iff hfm]`. Use `⟨hgood.mono fun z' hz' => (hslice z' hz').1, ?_⟩` and prove the remaining obligations. Use `Integrable.mono' (g := fun z' => ∫ _w, (2 * M) ∂μ - (Real.log ‖H (z', z0 0)‖ - (a 0 : ℝ) / 2 * (harmonic (n - 1) : ℝ))) ((integrable_const _).sub (ihInt.sub (integrable_const _))) hfm.norm.integral_prod_right' ?_` and prove the remaining obligations.

Use `filter_upwards [hgood] with z' hz'`. Take `⟨hI, hL, -⟩` from `hslice z' hz'`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]`. Combine the equalities or inequalities in the displayed calculation. Establish `hNull2 : (ν.prod μ) {q | H q = 0} = 0`.

Establish `hms : MeasurableSet {q | H q = 0}` using `hHm (measurableSet_singleton 0)`. Rewrite using `[Measure.measure_prod_null hms]`. Use `filter_upwards [hgood] with z' hz'`. Simplify `(hslice z' hz').2.2` using `[Set.preimage]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : (fun z => Real.log ‖onSpheres F z‖) = (fun q => Real.log ‖H q‖) ∘ e2`. Use function extensionality and compare the values at `z`. Simplify using `only [Function.comp_apply]`. Rewrite using `[hcomp z]`. Rewrite using `[h1, mp2.integrable_comp_emb e2.measurableEmbedding]`.

Conclude with `hInt2`. Establish `h1 : {z | onSpheres F z = 0} = e2 ⁻¹' {q | H q = 0}`. Use extensionality with `z`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage]`. Rewrite using `[hcomp z]`.

Rewrite using `[h1, mp2.measure_preimage_emb e2.measurableEmbedding]`. Conclude with `hNull2`.
-/
theorem blockPoly_claim (hSJ : SJStatement) (n : ℕ) : ∀ (k : ℕ) (a : Fin k → ℕ)
    (F : (Fin k → Fin n → ℂ) → ℂ), BlockPoly k n a F → ∀ z0 : Fin k → UnitSphereC n,
    onSpheres F z0 ≠ 0 →
    Integrable (fun z => Real.log ‖onSpheres F z‖) (Measure.pi fun _ : Fin k => sphereProb n) ∧
      Measure.pi (fun _ : Fin k => sphereProb n) {z | onSpheres F z = 0} = 0 := by
  haveI : IsFiniteMeasure (sphereProb n) := by unfold sphereProb; infer_instance
  intro k
  induction k with
  | zero =>
    intro a F hF z0 hz0
    have hconst : ∀ z : Fin 0 → UnitSphereC n, onSpheres F z = onSpheres F z0 := by
      intro z
      unfold onSpheres
      congr 1
      funext b
      exact b.elim0
    refine ⟨?_, ?_⟩
    · simp_rw [hconst]
      exact integrable_const _
    · simp_rw [hconst]
      simp [hz0]
  | succ k ih =>
    intro a F hF z0 hz0
    set μ := sphereProb n with hμ
    set ν := Measure.pi fun _ : Fin k => sphereProb n with hν
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => UnitSphereC n) 0
    have mp : MeasurePreserving e (Measure.pi fun _ : Fin (k + 1) => sphereProb n) (μ.prod ν) :=
      measurePreserving_piFinSuccAbove (fun _ => sphereProb n) 0
    let e2 := e.trans MeasurableEquiv.prodComm
    have mp2 : MeasurePreserving e2 (Measure.pi fun _ : Fin (k + 1) => sphereProb n) (ν.prod μ) :=
      (Measure.measurePreserving_swap).comp mp
    have hcont : Continuous (onSpheres F : (Fin (k + 1) → UnitSphereC n) → ℂ) :=
      hF.1.comp (continuous_pi fun b => (continuous_spherePoint n).comp (continuous_apply b))
    let H : (Fin k → UnitSphereC n) × UnitSphereC n → ℂ := fun q => onSpheres F (e2.symm q)
    have hHm : Measurable H := hcont.measurable.comp e2.symm.measurable
    have hsymm : ∀ z' w, e2.symm (z', w) = Fin.cons w z' := by
      intro z' w
      simp [e2, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero']
      rfl
    have hH : ∀ z' w, H (z', w) = F (Fin.cons (spherePoint w) (fun b => spherePoint (z' b))) := by
      intro z' w
      simp only [H, onSpheres, hsymm]
      congr 1
      funext b
      refine Fin.cases ?_ (fun j => ?_) b <;> simp
    have hcomp : ∀ z, onSpheres F z = H (e2 z) := by
      intro z
      simp only [H, MeasurableEquiv.symm_apply_apply]
    set v0 := spherePoint (z0 0) with hv0
    have hR := hF.restrict v0
    have hG : ∀ z', onSpheres (fun p => F (Fin.cons v0 p)) z' = H (z', z0 0) := by
      intro z'
      rw [hH]
      rfl
    have hz0' : onSpheres (fun p => F (Fin.cons v0 p)) (fun j => z0 j.succ) ≠ 0 := by
      simp only [onSpheres] at hz0 ⊢
      convert hz0 using 2
      funext b
      refine Fin.cases ?_ (fun j => ?_) b <;> simp [v0]
    obtain ⟨ihInt, ihNull⟩ := ih _ _ hR _ hz0'
    simp_rw [hG] at ihInt ihNull
    have hgood : ∀ᵐ z' ∂ν, H (z', z0 0) ≠ 0 := by
      rw [ae_iff]
      simpa using ihNull
    have hslice : ∀ z', H (z', z0 0) ≠ 0 →
        Integrable (fun w => Real.log ‖H (z', w)‖) μ ∧
        Real.log ‖H (z', z0 0)‖ - (a 0 : ℝ) / 2 * (harmonic (n - 1) : ℝ) ≤
          ∫ w, Real.log ‖H (z', w)‖ ∂μ ∧ μ {w | H (z', w) = 0} = 0 := by
      intro z' hz'
      obtain ⟨g, hg, hgF⟩ := hF.2 0 (Fin.cons 0 (fun b => spherePoint (z' b)))
      have hHw : ∀ w, H (z', w) = MvPolynomial.eval (spherePoint w) g := by
        intro w
        rw [hH, ← hgF, Fin.update_cons_zero]
      have hu : ‖(z0 0 : EuclideanSpace ℂ (Fin n))‖ = 1 := norm_eq_of_mem_sphere _
      have hgu : MvPolynomial.eval (WithLp.ofLp (z0 0 : EuclideanSpace ℂ (Fin n))) g ≠ 0 := by
        rw [hHw] at hz'
        exact hz'
      obtain ⟨hI, hL⟩ := hSJ n (a 0) g _ hg hu hgu
      have hN := sphere_zero_null hSJ g hg _ hu hgu
      simp_rw [hHw]
      exact ⟨hI, hL, hN⟩
    obtain ⟨C, hC⟩ : ∃ C, ∀ z, ‖onSpheres F z‖ ≤ C := by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
      exact ⟨C, fun z => hC z (Set.mem_univ _)⟩
    set M := Real.log (max C 1) with hMdef
    have hM0 : 0 ≤ M := Real.log_nonneg (le_max_right _ _)
    have hLM : ∀ q, Real.log ‖H q‖ ≤ M := by
      intro q
      rcases (norm_nonneg (H q)).eq_or_lt with h0 | hpos
      · rw [← h0, Real.log_zero]
        exact hM0
      · exact Real.log_le_log hpos ((hC _).trans (le_max_left _ _))
    have habs : ∀ q, ‖Real.log ‖H q‖‖ ≤ 2 * M - Real.log ‖H q‖ := by
      intro q
      rw [Real.norm_eq_abs]
      have := hLM q
      rcases le_total 0 (Real.log ‖H q‖) with h | h
      · rw [abs_of_nonneg h]; linarith
      · rw [abs_of_nonpos h]; linarith
    have hfm : AEStronglyMeasurable (fun q => Real.log ‖H q‖) (ν.prod μ) :=
      (Real.measurable_log.comp hHm.norm).aestronglyMeasurable
    have hInt2 : Integrable (fun q => Real.log ‖H q‖) (ν.prod μ) := by
      rw [integrable_prod_iff hfm]
      refine ⟨hgood.mono fun z' hz' => (hslice z' hz').1, ?_⟩
      refine Integrable.mono'
        (g := fun z' => ∫ _w, (2 * M) ∂μ -
          (Real.log ‖H (z', z0 0)‖ - (a 0 : ℝ) / 2 * (harmonic (n - 1) : ℝ)))
        ((integrable_const _).sub (ihInt.sub (integrable_const _)))
        hfm.norm.integral_prod_right' ?_
      filter_upwards [hgood] with z' hz'
      obtain ⟨hI, hL, -⟩ := hslice z' hz'
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      calc ∫ w, ‖Real.log ‖H (z', w)‖‖ ∂μ ≤ ∫ w, (2 * M - Real.log ‖H (z', w)‖) ∂μ :=
            integral_mono hI.norm ((integrable_const _).sub hI) (fun w => habs _)
        _ = ∫ _w, (2 * M) ∂μ - ∫ w, Real.log ‖H (z', w)‖ ∂μ :=
            integral_sub (integrable_const _) hI
        _ ≤ _ := by linarith
    have hNull2 : (ν.prod μ) {q | H q = 0} = 0 := by
      have hms : MeasurableSet {q | H q = 0} := hHm (measurableSet_singleton 0)
      rw [Measure.measure_prod_null hms]
      filter_upwards [hgood] with z' hz'
      simpa [Set.preimage] using (hslice z' hz').2.2
    refine ⟨?_, ?_⟩
    · have h1 : (fun z => Real.log ‖onSpheres F z‖) = (fun q => Real.log ‖H q‖) ∘ e2 := by
        funext z
        simp only [Function.comp_apply]
        rw [hcomp z]
      rw [h1, mp2.integrable_comp_emb e2.measurableEmbedding]
      exact hInt2
    · have h1 : {z | onSpheres F z = 0} = e2 ⁻¹' {q | H q = 0} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_preimage]
        rw [hcomp z]
      rw [h1, mp2.measure_preimage_emb e2.measurableEmbedding]
      exact hNull2

end ReciprocityTheory.MultiplicativeHeights
