import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional

noncomputable section

open Matrix

namespace GlobalTheory.LinRed.Model

variable {n : ℕ}

/- English proof (translation)
Use `⟨isUnit_one, fun g hg h hh => IsUnit.mul hg hh, fun g hg => hg, fun g hg => ?_, fun g hg _ => hg, ?_, fun g hg => ?_⟩` and prove the remaining obligations. Conclude with `Matrix.isUnit_nonsing_inv_iff.2 hg`. Use `isPreconnected_of_forall (1 : Matrix (Fin n) (Fin n) ℂ) fun g hg => ?_` and prove the remaining obligations. Set `p : Polynomial ℂ` to `(1 + (Polynomial.X : Polynomial ℂ) • (g - 1).map Polynomial.C).det`. Establish `hp : ∀ t : ℂ, p.eval t = (1 + t • (g - 1)).det` using `fun t => by`.

Use `(Polynomial.evalRingHom t).map_det (1 + (Polynomial.X : Polynomial ℂ) • (g - 1).map Polynomial.C)` as an intermediate fact. Simplify using `only [Polynomial.coe_evalRingHom] at this`. Rewrite using `[this]`. Use `congr 1`. Use extensionality with `i j`.

Distinguish the cases in `h : i = j`. Apply the tactic sequence `simp [h, Matrix.one_apply] try ring`. Apply the tactic sequence `simp [h, Matrix.one_apply] try ring`. Establish `hp0 : p ≠ 0` using `fun h => by simpa [h] using hp 0`. Establish `hfin : {t : ℂ | p.IsRoot t}.Finite` using `Polynomial.finite_setOf_isRoot hp0`.

Establish `hc : IsPathConnected {t : ℂ | p.IsRoot t}ᶜ` using `hfin.countable.isPathConnected_compl_of_one_lt_rank (by simp)`. Establish `hcont : Continuous fun t : ℂ => (1 : Matrix (Fin n) (Fin n) ℂ) + t • (g - 1)` using `by fun_prop`. Use `⟨(fun t : ℂ => (1 : Matrix (Fin n) (Fin n) ℂ) + t • (g - 1)) '' {t : ℂ | p.IsRoot t}ᶜ, ?_, ?_, ?_, hc.isConnected.isPreconnected.image _ hcont.continuousOn⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Establish `: p.eval t ≠ 0` using `ht`.

Rewrite `this` using `[hp]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit this)`. Use `⟨0, ?_, by simp⟩ show ¬ p.eval 0 = 0` and prove the remaining obligations. Simplify using `[hp]`. Use `⟨1, ?_, by simp⟩ show ¬ p.eval 1 = 0` and prove the remaining obligations.

Simplify `((Matrix.isUnit_iff_isUnit_det _).1 hg).ne_zero` using `[hp]`. Conclude with `IsUnit.star hg`.
-/
theorem isLinRed_units (n : ℕ) : IsLinRed {g : Matrix (Fin n) (Fin n) ℂ | IsUnit g} := by
  refine ⟨isUnit_one, fun g hg h hh => IsUnit.mul hg hh, fun g hg => hg, fun g hg => ?_, fun g hg _ => hg, ?_,
    fun g hg => ?_⟩
  · exact Matrix.isUnit_nonsing_inv_iff.2 hg
  · refine isPreconnected_of_forall (1 : Matrix (Fin n) (Fin n) ℂ) fun g hg => ?_
    let p : Polynomial ℂ := (1 + (Polynomial.X : Polynomial ℂ) • (g - 1).map Polynomial.C).det
    have hp : ∀ t : ℂ, p.eval t = (1 + t • (g - 1)).det := fun t => by
      have := (Polynomial.evalRingHom t).map_det (1 + (Polynomial.X : Polynomial ℂ) • (g - 1).map Polynomial.C)
      simp only [Polynomial.coe_evalRingHom] at this
      rw [this]
      congr 1
      ext i j
      by_cases h : i = j
      · simp [h, Matrix.one_apply]
        try ring
      · simp [h, Matrix.one_apply]
        try ring
    have hp0 : p ≠ 0 := fun h => by simpa [h] using hp 0
    have hfin : {t : ℂ | p.IsRoot t}.Finite := Polynomial.finite_setOf_isRoot hp0
    have hc : IsPathConnected {t : ℂ | p.IsRoot t}ᶜ :=
      hfin.countable.isPathConnected_compl_of_one_lt_rank (by simp)
    have hcont : Continuous fun t : ℂ => (1 : Matrix (Fin n) (Fin n) ℂ) + t • (g - 1) := by fun_prop
    refine ⟨(fun t : ℂ => (1 : Matrix (Fin n) (Fin n) ℂ) + t • (g - 1)) '' {t : ℂ | p.IsRoot t}ᶜ, ?_, ?_, ?_,
      hc.isConnected.isPreconnected.image _ hcont.continuousOn⟩
    · rintro _ ⟨t, ht, rfl⟩
      have : p.eval t ≠ 0 := ht
      rw [hp] at this
      exact (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit this)
    · refine ⟨0, ?_, by simp⟩
      show ¬ p.eval 0 = 0
      simp [hp]
    · refine ⟨1, ?_, by simp⟩
      show ¬ p.eval 1 = 0
      simpa [hp] using ((Matrix.isUnit_iff_isUnit_det _).1 hg).ne_zero
  · exact IsUnit.star hg

/- English proof (translation)
Introduce `h` and use `by simpa using h.isUnit 0 trivial`.
-/
theorem not_isLinRed_univ : ¬ IsLinRed (Set.univ : Set (Matrix (Fin 1) (Fin 1) ℂ)) := fun h => by
  simpa using h.isUnit 0 trivial

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Break down `subsingleton_or_nontrivial H with hs | hs` into its components or cases. Use `infer_instance`. Take `⟨v, hv⟩` from `exists_ne (0 : H)`. Establish `hat : IsAtom (Submodule.span ℂ {v})` using `(Submodule.isAtom_iff_finrank_eq_one).2 (finrank_span_singleton hv)`. Use `h.2.2.2 (Submodule.span ℂ {v}) inferInstance (fun _ _ w hw => hw) (fun S' hS _ => hat.le_iff.1 hS)` as an intermediate fact.

Establish `htop : (sSup {S' | ∃ T : H →ₗ[ℂ] H, S' = (Submodule.span ℂ {v}).map T ∧ ∀ k ∈ maxCpt G, ∀ w ∈ Submodule.span ℂ {v}, T ((1 : H →L[ℂ] H) w) = (1 : H →L[ℂ] H) (T w)} : Submodule ℂ H) = ⊤`. Use `eq_top_iff.2 fun w _ => ?_` and prove the remaining obligations. Take `⟨f, hf⟩` from `Module.Projective.exists_dual_eq_one ℂ hv`. Establish `hw : w ∈ (Submodule.span ℂ {v}).map (f.smulRight w)` using `⟨v, Submodule.mem_span_singleton_self v, by simp [hf]⟩`. Use `(le_sSup ?_ : (Submodule.span ℂ {v}).map (f.smulRight w) ≤ _) hw` and prove the remaining obligations.

Conclude with `⟨f.smulRight w, rfl, fun _ _ _ _ => rfl⟩`. Rewrite `this` using `[htop]`. Conclude with `Module.Finite.equiv (Submodule.topEquiv (R := ℂ) (M := H))`.
-/
theorem finiteDimensional_of_trivial_isAdmOn {G : Set (Matrix (Fin n) (Fin n) ℂ)}
    (h : IsAdmOn G (fun _ => (1 : H →L[ℂ] H))) : FiniteDimensional ℂ H := by
  rcases subsingleton_or_nontrivial H with hs | hs
  · infer_instance
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  have hat : IsAtom (Submodule.span ℂ {v}) := (Submodule.isAtom_iff_finrank_eq_one).2 (finrank_span_singleton hv)
  have := h.2.2.2 (Submodule.span ℂ {v}) inferInstance (fun _ _ w hw => hw) (fun S' hS _ => hat.le_iff.1 hS)
  have htop : (sSup {S' | ∃ T : H →ₗ[ℂ] H, S' = (Submodule.span ℂ {v}).map T ∧
        ∀ k ∈ maxCpt G, ∀ w ∈ Submodule.span ℂ {v}, T ((1 : H →L[ℂ] H) w) = (1 : H →L[ℂ] H) (T w)} :
        Submodule ℂ H) = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hv
    have hw : w ∈ (Submodule.span ℂ {v}).map (f.smulRight w) :=
      ⟨v, Submodule.mem_span_singleton_self v, by simp [hf]⟩
    refine (le_sSup ?_ : (Submodule.span ℂ {v}).map (f.smulRight w) ≤ _) hw
    exact ⟨f.smulRight w, rfl, fun _ _ _ _ => rfl⟩
  rw [htop] at this
  exact Module.Finite.equiv (Submodule.topEquiv (R := ℂ) (M := H))

/- English proof (translation)
Introduce `g₀ _` and use `⟨Set.univ, fun z => z i j, isOpen_univ, trivial, fun z _ => ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℂ) i)).analyticAt z, fun _ _ _ => rfl⟩`.
-/
theorem analyticOnGroup_entry (G : Set (Matrix (Fin n) (Fin n) ℂ)) (i j : Fin n) :
    AnalyticOnGroup G fun g => g i j := fun g₀ _ =>
  ⟨Set.univ, fun z => z i j, isOpen_univ, trivial, fun z _ =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℂ) i)).analyticAt z, fun _ _ _ => rfl⟩

/- English proof (translation)
Introduce `g hg` and use `by obtain ⟨U, F, hU, hgU, hF, hf⟩ := h g hg have h1 : ContinuousAt (fun z : Matrix (Fin n) (Fin n) ℂ => F z) g := (hF g hgU).continuousAt refine h1.continuousWithinAt.congr_of_eventuallyEq ?_ (hf g hgU hg) filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hU.mem_nh …`.
-/
theorem continuousOn_of_analyticOnGroup {G : Set (Matrix (Fin n) (Fin n) ℂ)} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : AnalyticOnGroup G f) : ContinuousOn f G := fun g hg => by
  obtain ⟨U, F, hU, hgU, hF, hf⟩ := h g hg
  have h1 : ContinuousAt (fun z : Matrix (Fin n) (Fin n) ℂ => F z) g := (hF g hgU).continuousAt
  refine h1.continuousWithinAt.congr_of_eventuallyEq ?_ (hf g hgU hg)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hgU)] with z hz hzU
  exact hf z hzU hz

/- English proof (translation)
Establish `hU : IsClosed (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))` using `isClosed_unitary`. Use `isClosed_of_closure_subset fun g hg => ?_` and prove the remaining obligations. Establish `h2 : g ∈ Matrix.unitaryGroup (Fin n) ℂ` using `hU.closure_subset (closure_mono Set.inter_subset_right hg)`. Conclude with `⟨h.closed g (IsUnit.of_mul_eq_one _ h2.2) (closure_mono Set.inter_subset_left hg), h2⟩`.
-/
theorem isClosed_maxCpt {G : Set (Matrix (Fin n) (Fin n) ℂ)} (h : IsLinRed G) : IsClosed (maxCpt G) := by
  have hU : IsClosed (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := isClosed_unitary
  refine isClosed_of_closure_subset fun g hg => ?_
  have h2 : g ∈ Matrix.unitaryGroup (Fin n) ℂ := hU.closure_subset (closure_mono Set.inter_subset_right hg)
  exact ⟨h.closed g (IsUnit.of_mul_eq_one _ h2.2) (closure_mono Set.inter_subset_left hg), h2⟩

end GlobalTheory.LinRed.Model

end
