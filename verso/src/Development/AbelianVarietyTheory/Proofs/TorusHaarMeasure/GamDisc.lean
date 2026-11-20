import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.GamDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Introduce `r X H _`. Establish `hS` using `GlobalTheory.LatFin.latFin.2 r X 2`. Use `set S := {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r), ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 2} with hSdef`. Set `F : GL (Fin r) E → Set H` to `fun γ => {g : H | ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1}`. Establish `hF : ∀ γ, (F γ).Finite`.

Introduce `γ`. Use `Set.Subsingleton.finite ?_` and prove the remaining obligations. Introduce `g hg g' hg'`. Use `Subtype.ext (funext fun τ => Units.ext ?_)` and prove the remaining obligations. Conclude with `(hg τ).trans (hg' τ).symm`.

Establish `hT : (⋃ γ ∈ S, F γ).Finite` using `hS.biUnion fun γ _ => hF γ`. Establish `hC : ((⋃ γ ∈ S, F γ) \ {1})ᶜ ∈ 𝓝 (1 : H)` using `(hT.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)`. Establish `hV : ∀ᶠ g : H in 𝓝 1, ∀ (τ : X.Ψ) (a b : Fin r), ‖((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b‖ < 2`. Simplify using `only [Filter.eventually_all]`. Introduce `τ a b`.

Establish `hc : Continuous fun g : H => ‖((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b‖` using `((Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)).matrix_elem a b).norm`. Use `hc.continuousAt.eventually_lt continuousAt_const ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : a = b <;> simp [Matrix.one_apply, h]`. Use `⟨_, Filter.inter_mem hC hV, ?_⟩` and prove the remaining obligations. Introduce and unpack `g ⟨γ, hγ, hg⟩ ⟨h1, h2⟩`.

Assume the negation of the conclusion as `hne`. Use `h1 ⟨Set.mem_biUnion (x := γ) ⟨hγ, fun τ a b => ?_⟩ hg, hne⟩` and prove the remaining obligations. Use `h2 τ a b` as an intermediate fact. Rewrite `this` using `[hg τ]`. Conclude with `this.le`.
-/
theorem gamDisc : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∃ U ∈ 𝓝 (1 : H), ∀ g : H, (∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) → g ∈ U → g = 1) := by
  intro r X H _
  have hS := GlobalTheory.LatFin.latFin.2 r X 2
  set S := {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r),
    ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 2} with hSdef
  let F : GL (Fin r) E → Set H := fun γ => {g : H | ∀ τ : X.Ψ,
    ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1}
  have hF : ∀ γ, (F γ).Finite := by
    intro γ
    refine Set.Subsingleton.finite ?_
    intro g hg g' hg'
    refine Subtype.ext (funext fun τ => Units.ext ?_)
    exact (hg τ).trans (hg' τ).symm
  have hT : (⋃ γ ∈ S, F γ).Finite := hS.biUnion fun γ _ => hF γ
  have hC : ((⋃ γ ∈ S, F γ) \ {1})ᶜ ∈ 𝓝 (1 : H) :=
    (hT.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  have hV : ∀ᶠ g : H in 𝓝 1, ∀ (τ : X.Ψ) (a b : Fin r),
      ‖((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b‖ < 2 := by
    simp only [Filter.eventually_all]
    intro τ a b
    have hc : Continuous fun g : H =>
        ‖((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b‖ :=
      ((Units.continuous_val.comp
        ((continuous_apply τ).comp continuous_subtype_val)).matrix_elem a b).norm
    refine hc.continuousAt.eventually_lt continuousAt_const ?_
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  refine ⟨_, Filter.inter_mem hC hV, ?_⟩
  rintro g ⟨γ, hγ, hg⟩ ⟨h1, h2⟩
  by_contra hne
  refine h1 ⟨Set.mem_biUnion (x := γ) ⟨hγ, fun τ a b => ?_⟩ hg, hne⟩
  have := h2 τ a b
  rw [hg τ] at this
  exact this.le

end GlobalTheory.GamDisc
