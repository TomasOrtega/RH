import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit

noncomputable section

open UpperTheory.V.Sd.S2 ReciprocityTheory.Gal

namespace UpperTheory

/- English proof (translation)
Establish `a : ∀ i j, Continuous fun x => A x i j` using `fun i j => hA.matrix_elem i j`. Establish `b : ∀ i j, Continuous fun x => B x i j` using `fun i j => hB.matrix_elem i j`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [mix, div_eq_mul_inv] <;> fun_prop`.
-/
private theorem mix_cont {k X : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [TopologicalSpace X] (γ : kˣ)
    {A B : X → Matrix (Fin 2) (Fin 2) k} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => mix γ (A x) (B x) := by
  have a : ∀ i j, Continuous fun x => A x i j := fun i j => hA.matrix_elem i j
  have b : ∀ i j, Continuous fun x => B x i j := fun i j => hB.matrix_elem i j
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [mix, div_eq_mul_inv] <;> fun_prop

/- English proof (translation)
Introduce `l _ Γ₀ Γ _ _ _ _ _ j t α β ρ R hM hj hρ`. Use `haveI hN : j.range.Normal := Subgroup.normal_of_index_eq_two hM.index`. Establish `hc : ∀ h : Γ₀, ∃ h', j h' = t⁻¹ * j h * t` using `fun h => by`. Use `hN.conj_mem (j h) ⟨h, rfl⟩ t⁻¹` as an intermediate fact. Simplify using `using this`.

Use `choose c hc using hc`. Establish `cc : Continuous c`. Rewrite using `[hj.isInducing.continuous_iff]`. Establish `: (j ∘ c) = fun h => t⁻¹ * j h * t` using `funext hc`. Rewrite using `[this]`.

Use `hj.continuous` as an intermediate fact. Use `fun_prop`. Establish `ci : Continuous fun h : Γ₀ => h⁻¹`. Rewrite using `[hj.isInducing.continuous_iff]`. Establish `: (j ∘ fun h : Γ₀ => h⁻¹) = fun h => (j h)⁻¹` using `funext fun h => by simp`.

Rewrite using `[this]`. Conclude with `hj.continuous.inv`. Establish `hv : Continuous fun h => (ρ h).val` using `Units.continuous_val.comp hρ`. Establish `h1 : Continuous fun h => (R (j h)).val`. Establish `: (fun h => (R (j h)).val) = fun h => mix (β / α) (ρ h) (ρ (c h))`.

Use function extensionality and compare the values at `fun h => hM.on h (c h) (hc h)`. Rewrite using `[this]`. Conclude with `mix_cont _ hv (hv.comp cc)`. Establish `h2 : Continuous (R ∘ j)`. Rewrite using `[Units.continuous_iff]`.

Use `⟨h1, ?_⟩` and prove the remaining obligations. Use `h1.comp ci` as an intermediate fact. Use `this.congr fun h => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, map_inv]`. Use `continuous_of_continuousAt_one R ?_` and prove the remaining obligations.

Use `(hj.continuousAt_iff (g := R) (x := 1)).1 h2.continuousAt` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis.
-/
theorem continuous_mix_family : UpperTheory.V.Sd.S2.MixCont := by
  intro l _ Γ₀ Γ _ _ _ _ _ j t α β ρ R hM hj hρ
  haveI hN : j.range.Normal := Subgroup.normal_of_index_eq_two hM.index
  have hc : ∀ h : Γ₀, ∃ h', j h' = t⁻¹ * j h * t := fun h => by
    have := hN.conj_mem (j h) ⟨h, rfl⟩ t⁻¹
    simpa using this
  choose c hc using hc
  have cc : Continuous c := by
    rw [hj.isInducing.continuous_iff]
    have : (j ∘ c) = fun h => t⁻¹ * j h * t := funext hc
    rw [this]
    have := hj.continuous
    fun_prop
  have ci : Continuous fun h : Γ₀ => h⁻¹ := by
    rw [hj.isInducing.continuous_iff]
    have : (j ∘ fun h : Γ₀ => h⁻¹) = fun h => (j h)⁻¹ := funext fun h => by simp
    rw [this]
    exact hj.continuous.inv
  have hv : Continuous fun h => (ρ h).val := Units.continuous_val.comp hρ
  have h1 : Continuous fun h => (R (j h)).val := by
    have : (fun h => (R (j h)).val) = fun h => mix (β / α) (ρ h) (ρ (c h)) :=
      funext fun h => hM.on h (c h) (hc h)
    rw [this]
    exact mix_cont _ hv (hv.comp cc)
  have h2 : Continuous (R ∘ j) := by
    rw [Units.continuous_iff]
    refine ⟨h1, ?_⟩
    have := h1.comp ci
    refine this.congr fun h => ?_
    simp only [Function.comp, map_inv]
  refine continuous_of_continuousAt_one R ?_
  have := (hj.continuousAt_iff (g := R) (x := 1)).1 h2.continuousAt
  rwa [map_one] at this

end UpperTheory
