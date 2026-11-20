import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.PSmooth

noncomputable section

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]

/- English proof (translation)
Apply the tactic sequence `funext n; cases n <;> rfl`.
-/
theorem cons_mul (a γ : Γ) (σ : ℕ → Γ) :
    (fun n => a * cons γ σ n) = cons (a * γ) (fun n => a * σ n) := by
  funext n; cases n <;> rfl

/- English proof (translation)
Simplify using `only [extDeriv, h.fderiv_eq]`.
-/
theorem extDeriv_congr_nhds {n : ℕ} {ω₁ ω₂ : V → V [⋀^Fin n]→L[ℝ] ℝ} {x : V} (h : ω₁ =ᶠ[𝓝 x] ω₂) :
    extDeriv ω₁ x = extDeriv ω₂ x := by
  simp only [extDeriv, h.fderiv_eq]

/- English proof (translation)
Take `⟨s, W, hW, -, hs⟩` from `hL H (B h) (hB h hh)`. Establish `hfin : Function.HasFiniteSupport (fun γ => psi A φ γ (B h) • β (cons γ σ) (B h))`. Use `s.finite_toSet.subset ?_` and prove the remaining obligations. Introduce `γ hγ`. Assume the negation of the conclusion as `hγs`.

Apply `hγ` to reduce the goal to its premises. Simplify using `[hs γ hγs (B h) (mem_of_mem_nhds hW)]`. Establish `key : ∀ γ, ContinuousAlternatingMap.compContinuousLinearMapCLM B (psi A φ γ (B h) • β (cons γ σ) (B h)) = psi A φ (a * γ) h • β (cons (a * γ) (fun n => a * σ n)) h`. Introduce `γ`. Rewrite using `[map_smul, ← cons_mul, ← hβ _ h hh, ← hψ γ h hh]`.

Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation.
-/
theorem kf_equiv {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (hL : PLoc U A φ) (H : Hyp U A φ)
    {q : ℕ} (β : (ℕ → Γ) → V → V [⋀^Fin q]→L[ℝ] ℝ) (B : V →L[ℝ] V) (a : Γ)
    (hB : ∀ h ∈ U, B h ∈ U) (hψ : ∀ γ, ∀ h ∈ U, psi A φ γ (B h) = psi A φ (a * γ) h)
    (hβ : ∀ σ, ∀ h ∈ U, (β σ (B h)).compContinuousLinearMap B = β (fun n => a * σ n) h)
    (σ : ℕ → Γ) {h : V} (hh : h ∈ U) :
    (Kf A φ β σ (B h)).compContinuousLinearMap B = Kf A φ β (fun n => a * σ n) h := by
  obtain ⟨s, W, hW, -, hs⟩ := hL H (B h) (hB h hh)
  have hfin : Function.HasFiniteSupport
      (fun γ => psi A φ γ (B h) • β (cons γ σ) (B h)) := by
    refine s.finite_toSet.subset ?_
    intro γ hγ
    by_contra hγs
    apply hγ
    simp [hs γ hγs (B h) (mem_of_mem_nhds hW)]
  have key : ∀ γ, ContinuousAlternatingMap.compContinuousLinearMapCLM B
      (psi A φ γ (B h) • β (cons γ σ) (B h))
        = psi A φ (a * γ) h • β (cons (a * γ) (fun n => a * σ n)) h := by
    intro γ
    rw [map_smul, ← cons_mul, ← hβ _ h hh, ← hψ γ h hh]
    rfl
  calc (Kf A φ β σ (B h)).compContinuousLinearMap B
      = ContinuousAlternatingMap.compContinuousLinearMapCLM B
          (∑ᶠ γ, psi A φ γ (B h) • β (cons γ σ) (B h)) := rfl
    _ = ∑ᶠ γ, ContinuousAlternatingMap.compContinuousLinearMapCLM B
          (psi A φ γ (B h) • β (cons γ σ) (B h)) := map_finsum _ hfin
    _ = ∑ᶠ γ, psi A φ (a * γ) h • β (cons (a * γ) (fun n => a * σ n)) h := finsum_congr key
    _ = Kf A φ β (fun n => a * σ n) h :=
      finsum_comp_equiv (Equiv.mulLeft a)
        (f := fun γ => psi A φ γ h • β (cons γ (fun n => a * σ n)) h)

/- English proof (translation)
Introduce `H k c hc B a hB hψ`. Establish `hfd : ∀ x, fderiv ℝ B x = B` using `fun x => B.fderiv`. Establish `he : ∀ j σ, ∀ h ∈ U, (eta A φ c j σ (B h)).compContinuousLinearMap B = eta A φ c j (fun n => a * σ n) h`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero`. Introduce `σ h hh`. Rewrite using `[eta.eq_1, eta.eq_1]`. Use extensionality with `m`. Simplify using `[hc a (fun i => σ i)]`.

Consider the case `succ j ih`. Introduce `σ h hh`. Establish `hK : ∀ x ∈ U, (Kf A φ (eta A φ c j) σ (B x)).compContinuousLinearMap B = Kf A φ (eta A φ c j) (fun n => a * σ n) x` using `fun x hx => kf_equiv hL H (eta A φ c j) B a hB hψ ih σ hx`. Establish `hdiff : DifferentiableAt ℝ (Kf A φ (eta A φ c j) σ) (B h)` using `((hS H k c j σ).2.contDiffAt (H.isOpen.mem_nhds (hB h hh))).differentiableAt (by simp)`. Establish `hpb` using `extDeriv_pullback (f := B) (x := h) (r := ⊤) hdiff B.contDiff.contDiffAt le_top`.

Simplify using `only [hfd] at hpb`. Rewrite using `[eta.eq_2, eta.eq_2, ← hpb]`. Apply `extDeriv_congr_nhds` to reduce the goal to its premises. Use `filter_upwards [H.isOpen.mem_nhds hh] with x hx`. Conclude with `hK x hx`.

Introduce `j σ h hh`. Conclude with `⟨he j σ h hh, kf_equiv hL H (eta A φ c j) B a hB hψ (he j) σ hh⟩`.
-/
theorem pEquiv (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) (hL : PLoc U A φ)
    (hS : PSmooth U A φ) : PEquiv U A φ := by
  intro H k c hc B a hB hψ
  have hfd : ∀ x, fderiv ℝ B x = B := fun x => B.fderiv
  have he : ∀ j σ, ∀ h ∈ U, (eta A φ c j σ (B h)).compContinuousLinearMap B
      = eta A φ c j (fun n => a * σ n) h := by
    intro j
    induction j with
    | zero =>
      intro σ h hh
      rw [eta.eq_1, eta.eq_1]
      ext m
      simp [hc a (fun i => σ i)]
    | succ j ih =>
      intro σ h hh
      have hK : ∀ x ∈ U, (Kf A φ (eta A φ c j) σ (B x)).compContinuousLinearMap B
          = Kf A φ (eta A φ c j) (fun n => a * σ n) x :=
        fun x hx => kf_equiv hL H (eta A φ c j) B a hB hψ ih σ hx
      have hdiff : DifferentiableAt ℝ (Kf A φ (eta A φ c j) σ) (B h) :=
        ((hS H k c j σ).2.contDiffAt (H.isOpen.mem_nhds (hB h hh))).differentiableAt (by simp)
      have hpb := extDeriv_pullback (f := B) (x := h) (r := ⊤) hdiff B.contDiff.contDiffAt le_top
      simp only [hfd] at hpb
      rw [eta.eq_2, eta.eq_2, ← hpb]
      apply extDeriv_congr_nhds
      filter_upwards [H.isOpen.mem_nhds hh] with x hx
      exact hK x hx
  intro j σ h hh
  exact ⟨he j σ h hh, kf_equiv hL H (eta A φ c j) B a hB hψ (he j) σ hh⟩

end PositivityTheory.KB.WhittakerCocycle

end
