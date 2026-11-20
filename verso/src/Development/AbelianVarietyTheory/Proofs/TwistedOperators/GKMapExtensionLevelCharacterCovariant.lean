import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKFinOfMemLowT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmoothCuspFormFrechetModerateGrowthRepStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevFormEqZeroOnSmoothOfKFiniteDiscreteSeriesStatement
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GKExtLevel

/- English proof (translation)
Take `⟨S₁, C₁, hS₁, hC₁⟩` from `h₁`. Take `⟨S₂, C₂, hS₂, hC₂⟩` from `h₂`. Use `⟨S₁ ++ S₂, |C₁| + ‖c‖ * |C₂|, fun l hl X hX => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Break down `List.mem_append.1 hl with h | h exacts [hS₁ l h X hX, hS₂ l h X hX]` into its components or cases. Establish `nn : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ (S.map fun l => ‖l.foldr (dRep σ) w‖).sum` using `fun S => List.sum_nonneg fun x hx => by`.

Take `⟨l, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `norm_nonneg _`. Establish `n1` using `nn S₁`. Establish `n2` using `nn S₂`. Rewrite using `[List.map_append, List.sum_append]`.

Establish `b1` using `(hC₁ w hw).trans (mul_le_mul_of_nonneg_right (le_abs_self C₁) n1)`. Establish `b2` using `(hC₂ w hw).trans (mul_le_mul_of_nonneg_right (le_abs_self C₂) n2)`. Establish `e : ‖(ℓ₁ - c • ℓ₂) w‖ ≤ ‖ℓ₁ w‖ + ‖c‖ * ‖ℓ₂ w‖`. Rewrite using `[← norm_mul]`. Simplify using `using norm_sub_le (ℓ₁ w) (c * ℓ₂ w)`.

Establish `h3` using `mul_le_mul_of_nonneg_left b2 (norm_nonneg c)`. Establish `p1 : 0 ≤ |C₁| * (S₂.map fun l => ‖l.foldr (dRep σ) w‖).sum` using `mul_nonneg (abs_nonneg _) n2`. Establish `p2 : 0 ≤ ‖c‖ * |C₂| * (S₁.map fun l => ‖l.foldr (dRep σ) w‖).sum` using `mul_nonneg (mul_nonneg (norm_nonneg _) (abs_nonneg _)) n1`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sobCont_sub_smul {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ₁ ℓ₂ : H →ₗ[ℂ] ℂ}
    (c : ℂ) (h₁ : Sobolev₂ Lie σ ℓ₁) (h₂ : Sobolev₂ Lie σ ℓ₂) : Sobolev₂ Lie σ (ℓ₁ - c • ℓ₂) := by
  obtain ⟨S₁, C₁, hS₁, hC₁⟩ := h₁
  obtain ⟨S₂, C₂, hS₂, hC₂⟩ := h₂
  refine ⟨S₁ ++ S₂, |C₁| + ‖c‖ * |C₂|, fun l hl X hX => ?_, fun w hw => ?_⟩
  · rcases List.mem_append.1 hl with h | h
    exacts [hS₁ l h X hX, hS₂ l h X hX]
  · have nn : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ (S.map fun l => ‖l.foldr (dRep σ) w‖).sum :=
      fun S => List.sum_nonneg fun x hx => by
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg _
    have n1 := nn S₁
    have n2 := nn S₂
    rw [List.map_append, List.sum_append]
    have b1 := (hC₁ w hw).trans (mul_le_mul_of_nonneg_right (le_abs_self C₁) n1)
    have b2 := (hC₂ w hw).trans (mul_le_mul_of_nonneg_right (le_abs_self C₂) n2)
    have e : ‖(ℓ₁ - c • ℓ₂) w‖ ≤ ‖ℓ₁ w‖ + ‖c‖ * ‖ℓ₂ w‖ := by
      rw [← norm_mul]
      simpa using norm_sub_le (ℓ₁ w) (c * ℓ₂ w)
    have h3 := mul_le_mul_of_nonneg_left b2 (norm_nonneg c)
    have p1 : 0 ≤ |C₁| * (S₂.map fun l => ‖l.foldr (dRep σ) w‖).sum := mul_nonneg (abs_nonneg _) n2
    have p2 : 0 ≤ ‖c‖ * |C₂| * (S₁.map fun l => ‖l.foldr (dRep σ) w‖).sum :=
      mul_nonneg (mul_nonneg (norm_nonneg _) (abs_nonneg _)) n1
    nlinarith

/- English proof (translation)
Introduce `hHC D θ _ V S M J χ μ 𝓕 T₀ hT₀ T hext hcont v k hk g`. Establish `hsm : ∀ τ, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, w ∈ M.sm τ` using `fun τ w hw => by haveI := (M.ds τ).1`. Conclude with `Submodule.subset_span (GlobalTheory.Published.HarishChandraModules.smoothVec hHC (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 hw (M.fr_unit τ) (M.fr_gram τ))`. Establish `key : ∀ s : Finset D.what₂.Tau, ∀ v : M.Vec, (∀ τ ∉ s, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → T v (g * k) = χ k * T v g`. Introduce `s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `v hv`. Rewrite using `[hext v (fun τ => ⟨v τ, hv τ (Finset.notMem_empty τ)⟩) (fun τ => rfl)]`. Conclude with `hT₀.2.2.2.2.2.1 _ k hk g`.

Consider the case `@insert τ s hτ ih`. Introduce `v hv`. Take `⟨ℓ₁, h₁, e₁⟩` from `hcont τ v (g * k)`. Take `⟨ℓ₂, h₂, e₂⟩` from `hcont τ v g`. Establish `h0 : ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, (ℓ₁ - χ k • ℓ₂) w = 0`.

Introduce `w hw`. Establish `hi` using `ih (Function.update v τ ⟨w, hsm τ w hw⟩) (fun τ' hτ' => by`. Distinguish the cases in `h : τ' = τ`. Substitute `h` using the available equality. Simplify using `using hw`.

Rewrite using `[Function.update_of_ne h]`. Conclude with `hv τ' (by simp [h, hτ']))`. Establish `a1` using `e₁ ⟨w, hsm τ w hw⟩`. Establish `a2` using `e₂ ⟨w, hsm τ w hw⟩`. Simplify using `only at a1 a2`.

Rewrite using `[LinearMap.sub_apply, LinearMap.smul_apply, a1, a2, hi, smul_eq_mul, sub_self]`. Establish `hz` using `GlobalTheory.T.sobolevForm_eq_zero_on_smooth_of_kFinite_discreteSeries hHC D V S M τ _ (sobCont_sub_smul (χ k) h₁ h₂) h0 (v τ) (v τ).2`. Establish `a1` using `e₁ (v τ)`. Establish `a2` using `e₂ (v τ)`. Rewrite `a1`, `a2` using `[Function.update_eq_self]`.

Rewrite `hz` using `[LinearMap.sub_apply, LinearMap.smul_apply, a1, a2, smul_eq_mul, sub_eq_zero]`. Conclude with `hz`. Conclude with `key Finset.univ v fun τ h => absurd (Finset.mem_univ τ) h`.
-/
theorem lev : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M), GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ M J χ μ 𝓕 T₀ →
    ∀ T : MMap M, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.Extends T T₀ →
    (∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
      ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x) →
    ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  intro hHC D θ _ V S M J χ μ 𝓕 T₀ hT₀ T hext hcont v k hk g
  have hsm : ∀ τ, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, w ∈ M.sm τ := fun τ w hw => by
    haveI := (M.ds τ).1
    exact Submodule.subset_span (GlobalTheory.Published.HarishChandraModules.smoothVec hHC (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 hw
      (M.fr_unit τ) (M.fr_gram τ))
  have key : ∀ s : Finset D.what₂.Tau, ∀ v : M.Vec, (∀ τ ∉ s, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) →
      T v (g * k) = χ k * T v g := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro v hv
      rw [hext v (fun τ => ⟨v τ, hv τ (Finset.notMem_empty τ)⟩) (fun τ => rfl)]
      exact hT₀.2.2.2.2.2.1 _ k hk g
    | @insert τ s hτ ih =>
      intro v hv
      obtain ⟨ℓ₁, h₁, e₁⟩ := hcont τ v (g * k)
      obtain ⟨ℓ₂, h₂, e₂⟩ := hcont τ v g
      have h0 : ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, (ℓ₁ - χ k • ℓ₂) w = 0 := by
        intro w hw
        have hi := ih (Function.update v τ ⟨w, hsm τ w hw⟩) (fun τ' hτ' => by
          by_cases h : τ' = τ
          · subst h
            simpa using hw
          · rw [Function.update_of_ne h]
            exact hv τ' (by simp [h, hτ']))
        have a1 := e₁ ⟨w, hsm τ w hw⟩
        have a2 := e₂ ⟨w, hsm τ w hw⟩
        simp only at a1 a2
        rw [LinearMap.sub_apply, LinearMap.smul_apply, a1, a2, hi, smul_eq_mul, sub_self]
      have hz := GlobalTheory.T.sobolevForm_eq_zero_on_smooth_of_kFinite_discreteSeries hHC D V S M τ _ (sobCont_sub_smul (χ k) h₁ h₂) h0 (v τ) (v τ).2
      have a1 := e₁ (v τ)
      have a2 := e₂ (v τ)
      rw [Function.update_eq_self] at a1 a2
      rw [LinearMap.sub_apply, LinearMap.smul_apply, a1, a2, smul_eq_mul, sub_eq_zero] at hz
      exact hz
  exact key Finset.univ v fun τ h => absurd (Finset.mem_univ τ) h

end GlobalTheory.GKExtLevel
