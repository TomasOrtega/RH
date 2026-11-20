import Mathlib

open MeasureTheory
open scoped BigOperators

namespace GlobalTheory.LatticeMean

/- English proof (translation)
Take `⟨w₁, w₂, hli, hΛ⟩` from `h`. Set `b : Module.Basis (Fin 2) ℝ ℂ` to `basisOfLinearIndependentOfCardEqFinrank hli (by simp)`. Establish `hb : Set.range b = {w₁, w₂}`. Simplify using `only [b, coe_basisOfLinearIndependentOfCardEqFinrank]`. Use extensionality with `x`.

Simplify using `[or_comm]`. Establish `hΛ' : Λ = (Submodule.span ℤ (Set.range b)).toAddSubgroup`. Rewrite using `[hΛ, hb, Submodule.span_int_eq_addSubgroupClosure]`. Substitute `hΛ'` using the available equality. Use `⟨?_, ZSpan.fundamentalDomain b, ZSpan.fundamentalDomain_measurableSet b, fun x => ?_⟩` and prove the remaining obligations.

Conclude with `inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))`. Conclude with `ZSpan.exist_unique_vadd_mem_fundamentalDomain b x`.
-/
theorem exists_strict_domain (Λ : AddSubgroup ℂ)
    (h : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    Countable Λ ∧ ∃ F : Set ℂ, MeasurableSet F ∧ ∀ x : ℂ, ∃! g : Λ, (g : ℂ) + x ∈ F := by
  obtain ⟨w₁, w₂, hli, hΛ⟩ := h
  let b : Module.Basis (Fin 2) ℝ ℂ :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : Set.range b = {w₁, w₂} := by
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank]
    ext x
    simp [or_comm]
  have hΛ' : Λ = (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    rw [hΛ, hb, Submodule.span_int_eq_addSubgroupClosure]
  subst hΛ'
  refine ⟨?_, ZSpan.fundamentalDomain b, ZSpan.fundamentalDomain_measurableSet b, fun x => ?_⟩
  · exact inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  · exact ZSpan.exist_unique_vadd_mem_fundamentalDomain b x

/- English proof (translation)
Establish `hE` using `Classical.epsilon_spec (p := fun Fd : Set V => IsAddFundamentalDomain A Fd μ) ⟨P, hP⟩`. Rewrite using `[setAverage_eq, setAverage_eq, hE.setIntegral_eq hP (fun g x => hf g g.2 x), measureReal_def, measureReal_def, hE.measure_eq hP]`.
-/
theorem setAverage_eq_of_domain {V : Type} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]
    (μ : Measure V) [μ.IsAddLeftInvariant] (A : AddSubgroup V) [Countable A] (f : V → ℝ)
    (hf : ∀ a ∈ A, ∀ z, f (a + z) = f z) (P : Set V) (hP : IsAddFundamentalDomain A P μ) :
    ⨍ z in Classical.epsilon (fun Fd : Set V => IsAddFundamentalDomain A Fd μ), f z ∂μ
      = ⨍ z in P, f z ∂μ := by
  have hE := Classical.epsilon_spec (p := fun Fd : Set V => IsAddFundamentalDomain A Fd μ) ⟨P, hP⟩
  rw [setAverage_eq, setAverage_eq, hE.setIntegral_eq hP (fun g x => hf g g.2 x),
    measureReal_def, measureReal_def, hE.measure_eq hP]

/- English proof (translation)
Rewrite using `[setAverage_eq, setAverage_eq, volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_pow, measureReal_def, Measure.pi_pi]`. Simplify using `[measureReal_def, mul_pow]`.
-/
theorem setAverage_pi (r : ℕ) (F : Set ℂ) (f : ℂ → ℝ) :
    ⨍ z in Set.univ.pi (fun _ : Fin r => F), ∏ k, f (z k) = (⨍ z in F, f z) ^ r := by
  rw [setAverage_eq, setAverage_eq, volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_pow, measureReal_def, Measure.pi_pi]
  simp [measureReal_def, mul_pow]

/- English proof (translation)
Introduce `Λ hΛ f hf V _ _ _ _ _ μ _ r e A hA`. Take `⟨hc, F, hFm, hF⟩` from `exists_strict_domain Λ hΛ`. Set `ec : V ≃L[ℝ] (Fin r → ℂ)` to `e.toContinuousLinearEquiv`. Set `em : V ≃ᵐ (Fin r → ℂ)` to `ec.toHomeomorph.toMeasurableEquiv`. Establish `hem : ∀ x, em x = e x` using `fun _ => rfl`.

Establish `hAc : Countable A`. Use `Function.Injective.countable (f := fun (a : A) (k : Fin r) => (⟨e a k, (hA a).1 a.2 k⟩ : Λ)) ?_` and prove the remaining obligations. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `e.injective` to reduce the goal to its premises.

Use function extensionality and compare the values at `k`. Conclude with `congrArg Subtype.val (congrFun hab k)`. Establish `hQm : MeasurableSet (Set.univ.pi (fun _ : Fin r => F))` using `MeasurableSet.univ_pi fun _ => hFm`. Establish `hP : IsAddFundamentalDomain A (em ⁻¹' Set.univ.pi (fun _ : Fin r => F)) μ`. Use `IsAddFundamentalDomain.mk' (em.measurable hQm).nullMeasurableSet fun x => ?_` and prove the remaining obligations.

Use `choose g hg hu using fun k => hF (e x k)`. Use `⟨⟨e.symm fun k => (g k : ℂ), (hA _).2 fun k => by simp⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `k _ show e (e.symm (fun k => (g k : ℂ)) + x) k ∈ F`. Simplify using `using hg k`. Introduce `a ha`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `e.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Establish `h1 : e ((a : V) + x) k ∈ F` using `ha k (Set.mem_univ k)`. Establish `h2` using `hu k ⟨e a k, (hA a).1 a.2 k⟩ (by simpa using h1)`.

Simplify using `using congrArg Subtype.val h2`. Establish `hF' : IsAddFundamentalDomain Λ F volume` using `IsAddFundamentalDomain.mk' hFm.nullMeasurableSet hF`. Rewrite using `[setAverage_eq_of_domain μ A (fun z => ∏ k, f (e z k)) ?_ _ hP, setAverage_eq_of_domain volume Λ f hf F hF', ← setAverage_pi]`. Use `swap`. Introduce `a ha z`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_add, Pi.add_apply, hf _ ((hA a).1 ha k)]`. Use `haveI : (μ.map em).IsAddHaarMeasure := ec.isAddHaarMeasure_map μ`. Establish `hs` using `Measure.isAddLeftInvariant_eq_smul (μ.map em) (volume : Measure (Fin r → ℂ))`. Establish `hc0 : Measure.addHaarScalarFactor (μ.map em) (volume : Measure (Fin r → ℂ)) ≠ 0` using `(Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'`.

Establish `h1 : ⨍ z in em ⁻¹' Set.univ.pi (fun _ : Fin r => F), ∏ k, f (e z k) ∂μ = ⨍ z in Set.univ.pi (fun _ : Fin r => F), ∏ k, f (z k) ∂(μ.map em)`. Rewrite using `[setAverage_eq, setAverage_eq, setIntegral_map_equiv, measureReal_def, measureReal_def, em.map_apply]`. Both sides reduce to the same expression. Rewrite using `[h1, hs, setAverage_eq, setAverage_eq, Measure.restrict_smul, integral_smul_nnreal_measure, measureReal_nnreal_smul_apply]`. Establish `hc1 : ((Measure.addHaarScalarFactor (μ.map em) (volume : Measure (Fin r → ℂ)) : NNReal) : ℝ) ≠ 0`.

Conclude with `hc0` after adjusting the coercions. Rewrite using `[NNReal.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_inv]`. Clear the denominators using the available nonvanishing facts.
-/
theorem mean_prod_eq_pow : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → ∀ (f : ℂ → ℝ), (∀ ω ∈ Λ, ∀ z, f (ω + z) = f z) → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (r : ℕ) (e : V ≃ₗ[ℝ] (Fin r → ℂ)) (A : AddSubgroup V), (∀ x, x ∈ A ↔ ∀ k, e x k ∈ Λ) → ⨍ z in Classical.epsilon (fun Fd : Set V => MeasureTheory.IsAddFundamentalDomain A Fd μ), ∏ k, f (e z k) ∂μ = (⨍ z in Classical.epsilon (fun Fd : Set ℂ => MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume), f z) ^ r := by
  intro Λ hΛ f hf V _ _ _ _ _ μ _ r e A hA
  obtain ⟨hc, F, hFm, hF⟩ := exists_strict_domain Λ hΛ
  let ec : V ≃L[ℝ] (Fin r → ℂ) := e.toContinuousLinearEquiv
  let em : V ≃ᵐ (Fin r → ℂ) := ec.toHomeomorph.toMeasurableEquiv
  have hem : ∀ x, em x = e x := fun _ => rfl
  have hAc : Countable A := by
    refine Function.Injective.countable
      (f := fun (a : A) (k : Fin r) => (⟨e a k, (hA a).1 a.2 k⟩ : Λ)) ?_
    intro a b hab
    apply Subtype.ext
    apply e.injective
    funext k
    exact congrArg Subtype.val (congrFun hab k)
  have hQm : MeasurableSet (Set.univ.pi (fun _ : Fin r => F)) :=
    MeasurableSet.univ_pi fun _ => hFm
  have hP : IsAddFundamentalDomain A (em ⁻¹' Set.univ.pi (fun _ : Fin r => F)) μ := by
    refine IsAddFundamentalDomain.mk' (em.measurable hQm).nullMeasurableSet fun x => ?_
    choose g hg hu using fun k => hF (e x k)
    refine ⟨⟨e.symm fun k => (g k : ℂ), (hA _).2 fun k => by simp⟩, ?_, ?_⟩
    · intro k _
      show e (e.symm (fun k => (g k : ℂ)) + x) k ∈ F
      simpa using hg k
    · intro a ha
      apply Subtype.ext
      apply e.injective
      funext k
      have h1 : e ((a : V) + x) k ∈ F := ha k (Set.mem_univ k)
      have h2 := hu k ⟨e a k, (hA a).1 a.2 k⟩ (by simpa using h1)
      simpa using congrArg Subtype.val h2
  have hF' : IsAddFundamentalDomain Λ F volume :=
    IsAddFundamentalDomain.mk' hFm.nullMeasurableSet hF
  rw [setAverage_eq_of_domain μ A (fun z => ∏ k, f (e z k)) ?_ _ hP,
    setAverage_eq_of_domain volume Λ f hf F hF', ← setAverage_pi]
  swap
  · intro a ha z
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_add, Pi.add_apply, hf _ ((hA a).1 ha k)]
  haveI : (μ.map em).IsAddHaarMeasure := ec.isAddHaarMeasure_map μ
  have hs := Measure.isAddLeftInvariant_eq_smul (μ.map em) (volume : Measure (Fin r → ℂ))
  have hc0 : Measure.addHaarScalarFactor (μ.map em) (volume : Measure (Fin r → ℂ)) ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  have h1 : ⨍ z in em ⁻¹' Set.univ.pi (fun _ : Fin r => F), ∏ k, f (e z k) ∂μ
      = ⨍ z in Set.univ.pi (fun _ : Fin r => F), ∏ k, f (z k) ∂(μ.map em) := by
    rw [setAverage_eq, setAverage_eq, setIntegral_map_equiv, measureReal_def, measureReal_def,
      em.map_apply]
    rfl
  rw [h1, hs, setAverage_eq, setAverage_eq, Measure.restrict_smul, integral_smul_nnreal_measure,
    measureReal_nnreal_smul_apply]
  have hc1 : ((Measure.addHaarScalarFactor (μ.map em) (volume : Measure (Fin r → ℂ)) : NNReal) : ℝ) ≠ 0 := by
    exact_mod_cast hc0
  rw [NNReal.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_inv]
  field_simp

end GlobalTheory.LatticeMean
