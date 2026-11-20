import Mathlib
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `o _ _ em I _ m B θ hB hBc hBne hθ`. Establish `: Countable (MvPolynomial I o)` using `Function.Surjective.countable (f := (AddMonoidAlgebra.ofCoeff : ((I →₀ ℕ) →₀ o) → MvPolynomial I o)) fun F => ⟨AddMonoidAlgebra.coeff F, rfl⟩`. Use `set Ω : Set (Fin (m + 1) → ℂ) := {p | Fin.tail p ∈ B ∧ p 0 ∈ ({0}ᶜ : Set ℂ)} with hΩ`. Establish `htail : Differentiable ℂ (fun p : Fin (m + 1) → ℂ => Fin.tail p)` using `differentiable_pi.2 fun i => differentiable_apply _`. Establish `hhead : Differentiable ℂ (fun p : Fin (m + 1) → ℂ => p 0)` using `differentiable_apply _`.

Establish `hΩo : IsOpen Ω` using `(hB.preimage htail.continuous).inter (isOpen_compl_singleton.preimage hhead.continuous)`. Establish `hΩimg : Ω = (fun q : (Fin m → ℂ) × ℂ => (Fin.cons q.2 q.1 : Fin (m + 1) → ℂ)) '' (B ×ˢ ({0}ᶜ : Set ℂ))`. Use extensionality with `p`. Prove the components needed by the constructor for the conclusion. Introduce `hp`.

Conclude with `⟨(Fin.tail p, p 0), ⟨hp.1, hp.2⟩, Fin.cons_self_tail p⟩`. Introduce and unpack `⟨⟨z, c⟩, ⟨hz, hc⟩, rfl⟩`. Conclude with `⟨by simpa using hz, by simpa using hc⟩`. Establish `hΩc : IsPreconnected Ω`. Rewrite using `[hΩimg]`.

Use `(hBc.prod (isConnected_compl_singleton_of_one_lt_rank ?_ 0).isPreconnected).image _ ?_` and prove the remaining obligations. Rewrite using `[Complex.rank_real_complex]`. Evaluate the numerical expressions. Conclude with `(Continuous.finCons (A := fun _ => ℂ) continuous_snd continuous_fst).continuousOn`. Establish `hΩne : Ω.Nonempty`.

Take `⟨z₀, hz₀⟩` from `hBne`. Conclude with `⟨Fin.cons 1 z₀, by simpa using hz₀, by simp⟩`. Set `f : MvPolynomial I o → (Fin (m + 1) → ℂ) → ℂ` to `fun F p => MvPolynomial.eval₂ em (p 0 • θ (Fin.tail p)) F`. Establish `hfd : ∀ F, DifferentiableOn ℂ (f F) Ω`. Introduce `F`.

Proceed by induction on `F using MvPolynomial.induction_on with`. Consider the case `C a`. Simplify using `only [f, MvPolynomial.eval₂_C]`. Conclude with `differentiableOn_const _`. Consider the case `add F G hF hG`.

Simplify using `only [f, MvPolynomial.eval₂_add]`. Conclude with `hF.add hG`. Consider the case `mul_X F a hF`. Establish `ha : DifferentiableOn ℂ (fun p : Fin (m + 1) → ℂ => θ (Fin.tail p) a) Ω` using `(hθ a).comp htail.differentiableOn fun p hp => hp.1`. Simplify using `only [f, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Pi.smul_apply, smul_eq_mul]`.

Conclude with `hF.mul (hhead.differentiableOn.mul ha)`. Establish `hfa : ∀ F, AnalyticOnNhd ℂ (f F) Ω` using `fun F => ReciprocityTheory.AnForm.Osgood.osgood (m + 1) Ω (f F) hΩo (hfd F)`. Set `W : MvPolynomial I o → Set (Fin (m + 1) → ℂ)` to `fun F => if Set.EqOn (f F) 0 Ω then Set.univ else (Ω ∩ f F ⁻¹' {0}ᶜ) ∪ (closure Ω)ᶜ`. Establish `hWo : ∀ F, IsOpen (W F)`. Introduce `F`.

Distinguish the cases in `h : Set.EqOn (f F) 0 Ω`. Simplify using `only [W, if_pos h]`. Conclude with `isOpen_univ`. Simplify using `only [W, if_neg h]`. Conclude with `((hfd F).continuousOn.isOpen_inter_preimage hΩo isOpen_compl_singleton).union isClosed_closure.isOpen_compl`.

Establish `hWd : ∀ F, Dense (W F)`. Introduce `F`. Distinguish the cases in `h : Set.EqOn (f F) 0 Ω`. Simplify using `only [W, if_pos h]`. Conclude with `dense_univ`.

Simplify using `only [W, if_neg h]`. Establish `hsub : Ω ⊆ closure (Ω ∩ f F ⁻¹' {0}ᶜ)`. Introduce `q hq`. Assume the negation of the conclusion as `hq'`. Apply `h` to reduce the goal to its premises.

Use `(hfa F).eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩc hq ?_` and prove the remaining obligations. Establish `hn : (closure (Ω ∩ f F ⁻¹' {0}ᶜ))ᶜ ∩ Ω ∈ nhds q` using `Filter.inter_mem (isClosed_closure.isOpen_compl.mem_nhds hq') (hΩo.mem_nhds hq)`. Use `filter_upwards [hn] with p hp`. Assume the negation of the conclusion as `hne`. Conclude with `hp.1 (subset_closure ⟨hp.2, hne⟩)`.

Introduce `x`. Distinguish the cases in `hx : x ∈ closure Ω`. Conclude with `closure_mono Set.subset_union_left (closure_minimal hsub isClosed_closure hx)`. Conclude with `subset_closure (Or.inr hx)`. Take `⟨p, hpΩ, hpW⟩` from `(dense_iInter_of_isOpen hWo hWd).inter_open_nonempty Ω hΩo hΩne`.

Use `⟨Fin.tail p, hpΩ.1, p 0, hpΩ.2, fun F hF z' hz' c' hc' => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : Set.EqOn (f F) 0 Ω`. Establish `hmem : (Fin.cons c' z' : Fin (m + 1) → ℂ) ∈ Ω` using `⟨by simpa using hz', by simpa using hc'⟩`. Simplify `h hmem` using `[f]`. Establish `hpW'` using `Set.mem_iInter.1 hpW F`.

Simplify using `only [W, if_neg h] at hpW'`. Break down `hpW' with hp' | hp'` into its components or cases. Conclude with `absurd hF hp'.2`. Conclude with `absurd (subset_closure hpΩ) hp'`.
-/
theorem exists_veryGeneral_point_of_holomorphic_family :
    ∀ (o : Type) [CommRing o] [Countable o] (em : o →+* ℂ) (I : Type) [Countable I] (m : ℕ) (B : Set (Fin m → ℂ)) (θ : (Fin m → ℂ) → I → ℂ), IsOpen B → IsPreconnected B → B.Nonempty → (∀ a, DifferentiableOn ℂ (fun z => θ z a) B) → ∃ z ∈ B, ∃ c : ℂ, c ≠ 0 ∧ ∀ F : MvPolynomial I o, MvPolynomial.eval₂ em (c • θ z) F = 0 → ∀ z' ∈ B, ∀ c' : ℂ, c' ≠ 0 → MvPolynomial.eval₂ em (c' • θ z') F = 0 := by
  intro o _ _ em I _ m B θ hB hBc hBne hθ
  classical
  have : Countable (MvPolynomial I o) :=
    Function.Surjective.countable
      (f := (AddMonoidAlgebra.ofCoeff : ((I →₀ ℕ) →₀ o) → MvPolynomial I o))
      fun F => ⟨AddMonoidAlgebra.coeff F, rfl⟩

  set Ω : Set (Fin (m + 1) → ℂ) := {p | Fin.tail p ∈ B ∧ p 0 ∈ ({0}ᶜ : Set ℂ)} with hΩ
  have htail : Differentiable ℂ (fun p : Fin (m + 1) → ℂ => Fin.tail p) :=
    differentiable_pi.2 fun i => differentiable_apply _
  have hhead : Differentiable ℂ (fun p : Fin (m + 1) → ℂ => p 0) := differentiable_apply _
  have hΩo : IsOpen Ω :=
    (hB.preimage htail.continuous).inter (isOpen_compl_singleton.preimage hhead.continuous)
  have hΩimg : Ω = (fun q : (Fin m → ℂ) × ℂ => (Fin.cons q.2 q.1 : Fin (m + 1) → ℂ)) ''
      (B ×ˢ ({0}ᶜ : Set ℂ)) := by
    ext p
    constructor
    · intro hp
      exact ⟨(Fin.tail p, p 0), ⟨hp.1, hp.2⟩, Fin.cons_self_tail p⟩
    · rintro ⟨⟨z, c⟩, ⟨hz, hc⟩, rfl⟩
      exact ⟨by simpa using hz, by simpa using hc⟩
  have hΩc : IsPreconnected Ω := by
    rw [hΩimg]
    refine (hBc.prod (isConnected_compl_singleton_of_one_lt_rank ?_ 0).isPreconnected).image _ ?_
    · rw [Complex.rank_real_complex]; norm_num
    · exact (Continuous.finCons (A := fun _ => ℂ) continuous_snd continuous_fst).continuousOn
  have hΩne : Ω.Nonempty := by
    obtain ⟨z₀, hz₀⟩ := hBne
    exact ⟨Fin.cons 1 z₀, by simpa using hz₀, by simp⟩

  let f : MvPolynomial I o → (Fin (m + 1) → ℂ) → ℂ :=
    fun F p => MvPolynomial.eval₂ em (p 0 • θ (Fin.tail p)) F
  have hfd : ∀ F, DifferentiableOn ℂ (f F) Ω := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a =>
      simp only [f, MvPolynomial.eval₂_C]
      exact differentiableOn_const _
    | add F G hF hG =>
      simp only [f, MvPolynomial.eval₂_add]
      exact hF.add hG
    | mul_X F a hF =>
      have ha : DifferentiableOn ℂ (fun p : Fin (m + 1) → ℂ => θ (Fin.tail p) a) Ω :=
        (hθ a).comp htail.differentiableOn fun p hp => hp.1
      simp only [f, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Pi.smul_apply, smul_eq_mul]
      exact hF.mul (hhead.differentiableOn.mul ha)
  have hfa : ∀ F, AnalyticOnNhd ℂ (f F) Ω := fun F =>
    ReciprocityTheory.AnForm.Osgood.osgood (m + 1) Ω (f F) hΩo (hfd F)

  let W : MvPolynomial I o → Set (Fin (m + 1) → ℂ) := fun F =>
    if Set.EqOn (f F) 0 Ω then Set.univ else (Ω ∩ f F ⁻¹' {0}ᶜ) ∪ (closure Ω)ᶜ
  have hWo : ∀ F, IsOpen (W F) := by
    intro F
    by_cases h : Set.EqOn (f F) 0 Ω
    · simp only [W, if_pos h]
      exact isOpen_univ
    · simp only [W, if_neg h]
      exact ((hfd F).continuousOn.isOpen_inter_preimage hΩo isOpen_compl_singleton).union
        isClosed_closure.isOpen_compl
  have hWd : ∀ F, Dense (W F) := by
    intro F
    by_cases h : Set.EqOn (f F) 0 Ω
    · simp only [W, if_pos h]
      exact dense_univ
    · simp only [W, if_neg h]
      have hsub : Ω ⊆ closure (Ω ∩ f F ⁻¹' {0}ᶜ) := by
        intro q hq
        by_contra hq'
        apply h
        refine (hfa F).eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩc hq ?_
        have hn : (closure (Ω ∩ f F ⁻¹' {0}ᶜ))ᶜ ∩ Ω ∈ nhds q :=
          Filter.inter_mem (isClosed_closure.isOpen_compl.mem_nhds hq') (hΩo.mem_nhds hq)
        filter_upwards [hn] with p hp
        by_contra hne
        exact hp.1 (subset_closure ⟨hp.2, hne⟩)
      intro x
      by_cases hx : x ∈ closure Ω
      · exact closure_mono Set.subset_union_left (closure_minimal hsub isClosed_closure hx)
      · exact subset_closure (Or.inr hx)

  obtain ⟨p, hpΩ, hpW⟩ := (dense_iInter_of_isOpen hWo hWd).inter_open_nonempty Ω hΩo hΩne
  refine ⟨Fin.tail p, hpΩ.1, p 0, hpΩ.2, fun F hF z' hz' c' hc' => ?_⟩
  by_cases h : Set.EqOn (f F) 0 Ω
  · have hmem : (Fin.cons c' z' : Fin (m + 1) → ℂ) ∈ Ω := ⟨by simpa using hz', by simpa using hc'⟩
    simpa [f] using h hmem
  · have hpW' := Set.mem_iInter.1 hpW F
    simp only [W, if_neg h] at hpW'
    rcases hpW' with hp' | hp'
    · exact absurd hF hp'.2
    · exact absurd (subset_closure hpΩ) hp'

end GlobalTheory
