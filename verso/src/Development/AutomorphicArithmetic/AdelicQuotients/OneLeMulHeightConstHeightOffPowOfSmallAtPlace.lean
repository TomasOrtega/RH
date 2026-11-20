import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

/- English proof (translation)
Use `set s : Finset ι := (hN.toFinset ∪ hb.toFinset) ∪ {i₀} with hs`. Establish `hi : i₀ ∈ s` using `by simp [hs]`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset N (s := s) (fun v hv => by simp only [hs, Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inl (Or.inl hv)), finprod_eq_prod_of_mulSupport_subset b (s := s) (fun v hv => by simp only [hs, Finset.coe_union, Set.Finite.coe_toFinset]; exact …`. Conclude with `mul_le_mul h0 (Finset.prod_le_prod (fun i _ => N0 i) fun i hi' => h i (Finset.ne_of_mem_erase hi')) (Finset.prod_nonneg fun i _ => N0 i) ((N0 _).trans h0)`.
-/
private theorem finprod_le_mul_finprod_pow {ι : Type*} {N b : ι → ℝ} (hN : (Function.mulSupport N).Finite)
    (hb : (Function.mulSupport b).Finite) (i₀ : ι) (ε : ℝ) (m : ℕ) (N0 : ∀ i, 0 ≤ N i)
    (hi₀ : b i₀ = 1) (h0 : N i₀ ≤ ε) (h : ∀ i, i ≠ i₀ → N i ≤ b i ^ m) :
    ∏ᶠ i, N i ≤ ε * (∏ᶠ i, b i) ^ m := by
  classical
  set s : Finset ι := (hN.toFinset ∪ hb.toFinset) ∪ {i₀} with hs
  have hi : i₀ ∈ s := by simp [hs]
  rw [finprod_eq_prod_of_mulSupport_subset N (s := s)
      (fun v hv => by simp only [hs, Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inl (Or.inl hv)),
    finprod_eq_prod_of_mulSupport_subset b (s := s)
      (fun v hv => by simp only [hs, Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inl (Or.inr hv)),
    ← Finset.mul_prod_erase s N hi, ← Finset.mul_prod_erase s b hi, hi₀, one_mul, ← Finset.prod_pow]
  exact mul_le_mul h0 (Finset.prod_le_prod (fun i _ => N0 i) fun i hi' => h i (Finset.ne_of_mem_erase hi'))
    (Finset.prod_nonneg fun i _ => N0 i) ((N0 _).trans h0)

/- English proof (translation)
Introduce `F E _ _ _ _ _ n q w₀ g a ε ha hinf hfin hq h0`. Establish `hprod : (∏ w : InfinitePlace E, ‖algebraMap E w.Completion a‖ ^ w.mult) * ∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖algebraMap E (v.adicCompletion E) a‖ = 1` using `prod_norm_mul_finprod_norm ha`. Establish `hNfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 E) => ‖algebraMap E (v.adicCompletion E) a‖).Finite` using `Filter.eventually_cofinite.1 (eventually_norm_eq_one ha)`. Use `set b : HeightOneSpectrum (𝓞 E) → ℝ := fun v => if below F v ≠ q then AutomorphicForm.locHeight (finAt v g) else 1 with hb`. Establish `hbfin : (Function.mulSupport b).Finite`.

Use `(AutomorphicForm.finite_mulSupport_locHeight_finAt g).subset fun v hv => ?_` and prove the remaining obligations. Simplify using `only [Function.mem_mulSupport, hb] at hv ⊢`. Introduce `h1`. Conclude with `hv (by simp [h1])`. Establish `hw₀ : below F w₀.1 = q`.

Use `w₀.2.over` as an intermediate fact. Conclude with `HeightOneSpectrum.ext this.symm`. Establish `hF : ∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖algebraMap E (v.adicCompletion E) a‖ ≤ ε * (∏ᶠ v, b v) ^ n`. Use `finprod_le_mul_finprod_pow hNfin hbfin w₀.1 ε n (fun _ => norm_nonneg _) (by simp [hb, hw₀]) h0 fun v _ => ?_` and prove the remaining obligations. Distinguish the cases in `hv : below F v = q`.

Establish `hl : v.asIdeal.LiesOver q.asIdeal` using `⟨(congrArg HeightOneSpectrum.asIdeal hv).symm⟩`. Use `hq ⟨v, hl⟩` as an intermediate fact. Simplify `this` using `[hb, hv]`. Simplify `hfin v` using `[hb, hv]`. Use `set A : ℝ := ∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w g) ^ w.mult with hA`.

Establish `hI : (∏ w : InfinitePlace E, ‖algebraMap E w.Completion a‖ ^ w.mult) ≤ (AutomorphicForm.heightConst E n * A) ^ n`. Establish `e : (AutomorphicForm.heightConst E n * A) ^ n = ∏ w : InfinitePlace E, ((max 1 (n : ℝ) * AutomorphicForm.locHeight (infAt w g)) ^ n) ^ w.mult`. Rewrite using `[AutomorphicForm.heightConst, hA, ← Finset.prod_mul_distrib, ← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_pow, ← pow_mul, ← pow_mul, mul_comm n]`.

Rewrite using `[e]`. Conclude with `Finset.prod_le_prod (fun _ _ => pow_nonneg (norm_nonneg _) _) fun w _ => pow_le_pow_left₀ (norm_nonneg _) (hinf w) _`. Establish `hoff : heightOff q g = A * ∏ᶠ v, b v`. Simplify using `only [heightOff, hA, hb, finprod_eq_if]`. Establish `hC : 0 ≤ (AutomorphicForm.heightConst E n * A) ^ n`.

Use `pow_nonneg (mul_nonneg (zero_le_one.trans AutomorphicForm.one_le_heightConst) ?_) _` and prove the remaining obligations. Conclude with `Finset.prod_nonneg fun _ _ => pow_nonneg (AutomorphicForm.locHeight_pos _).le _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hoff]`. Simplify using `only [mul_pow]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.one_le_mul_heightConst_heightOff_pow_of_small_at_place :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (q : HeightOneSpectrum (𝓞 F)) (w₀ : PlacesOver E q) (g : AdelicGLn.AdelicGL E n) (a : E) (ε : ℝ), a ≠ 0 →
        (∀ w : InfinitePlace E, ‖algebraMap E w.Completion a‖ ≤ (max 1 (n : ℝ) * AutomorphicForm.locHeight (infAt w g)) ^ n) →
        (∀ w : HeightOneSpectrum (𝓞 E), ‖algebraMap E (w.adicCompletion E) a‖ ≤ AutomorphicForm.locHeight (finAt w g) ^ n) →
        (∀ w : PlacesOver E q, ‖algebraMap E (w.1.adicCompletion E) a‖ ≤ 1) →
        ‖algebraMap E (w₀.1.adicCompletion E) a‖ ≤ ε →
        1 ≤ ε * (AutomorphicForm.heightConst E n * heightOff q g) ^ n := by
  intro F E _ _ _ _ _ n q w₀ g a ε ha hinf hfin hq h0
  classical
  have hprod : (∏ w : InfinitePlace E, ‖algebraMap E w.Completion a‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖algebraMap E (v.adicCompletion E) a‖ = 1 :=
    prod_norm_mul_finprod_norm ha
  have hNfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 E) =>
      ‖algebraMap E (v.adicCompletion E) a‖).Finite :=
    Filter.eventually_cofinite.1 (eventually_norm_eq_one ha)
  set b : HeightOneSpectrum (𝓞 E) → ℝ := fun v =>
    if below F v ≠ q then AutomorphicForm.locHeight (finAt v g) else 1 with hb
  have hbfin : (Function.mulSupport b).Finite := by
    refine (AutomorphicForm.finite_mulSupport_locHeight_finAt g).subset fun v hv => ?_
    simp only [Function.mem_mulSupport, hb] at hv ⊢
    intro h1
    exact hv (by simp [h1])
  have hw₀ : below F w₀.1 = q := by
    have := w₀.2.over
    exact HeightOneSpectrum.ext this.symm
  have hF : ∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖algebraMap E (v.adicCompletion E) a‖ ≤
      ε * (∏ᶠ v, b v) ^ n := by
    refine finprod_le_mul_finprod_pow hNfin hbfin w₀.1 ε n (fun _ => norm_nonneg _) (by simp [hb, hw₀]) h0 fun v _ => ?_
    by_cases hv : below F v = q
    · have hl : v.asIdeal.LiesOver q.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hv).symm⟩
      have := hq ⟨v, hl⟩
      simpa [hb, hv] using this
    · simpa [hb, hv] using hfin v
  set A : ℝ := ∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w g) ^ w.mult with hA
  have hI : (∏ w : InfinitePlace E, ‖algebraMap E w.Completion a‖ ^ w.mult) ≤
      (AutomorphicForm.heightConst E n * A) ^ n := by
    have e : (AutomorphicForm.heightConst E n * A) ^ n =
        ∏ w : InfinitePlace E, ((max 1 (n : ℝ) * AutomorphicForm.locHeight (infAt w g)) ^ n) ^ w.mult := by
      rw [AutomorphicForm.heightConst, hA, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [← mul_pow, ← pow_mul, ← pow_mul, mul_comm n]
    rw [e]
    exact Finset.prod_le_prod (fun _ _ => pow_nonneg (norm_nonneg _) _) fun w _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hinf w) _
  have hoff : heightOff q g = A * ∏ᶠ v, b v := by
    simp only [heightOff, hA, hb, finprod_eq_if]
  have hC : 0 ≤ (AutomorphicForm.heightConst E n * A) ^ n := by
    refine pow_nonneg (mul_nonneg (zero_le_one.trans AutomorphicForm.one_le_heightConst) ?_) _
    exact Finset.prod_nonneg fun _ _ => pow_nonneg (AutomorphicForm.locHeight_pos _).le _
  calc (1 : ℝ) = _ := hprod.symm
    _ ≤ (AutomorphicForm.heightConst E n * A) ^ n * (ε * (∏ᶠ v, b v) ^ n) :=
        mul_le_mul hI hF (finprod_nonneg fun _ => norm_nonneg _) hC
    _ = ε * (AutomorphicForm.heightConst E n * heightOff q g) ^ n := by
        rw [hoff]; simp only [mul_pow]; ring
