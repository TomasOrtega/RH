import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.TransposeUnitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoA

noncomputable section

open MeasureTheory ComplexConjugate
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open ConjugateHilbertSpace

/- English proof (translation)
Introduce `G _ _ _ _ _ μ _ _ _ H _ _ _ _ θ ρ hθc hθm hθθ hmap hρ1 hρm hiso hcont hsq hirr`. Establish `hθ1 : θ 1 = 1`. Establish `h` using `hθm 1 1`. Rewrite `h` using `[one_mul]`. Conclude with `mul_left_cancel (a := θ 1) (by rw [mul_one]; exact h.symm)`.

Establish `hθinv : ∀ a, θ a⁻¹ = (θ a)⁻¹`. Introduce `a`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← hθm, mul_inv_cancel, hθ1]`. Establish `hθmp : MeasurePreserving θ μ μ` using `⟨hθc.measurable, hmap⟩`.

Establish `hR : Formalism.MainNotions.BridgeCSchur.SqRep μ ρ` using `⟨hρ1, hρm, hiso, hcont, hsq⟩`. Take `⟨τ, hτ⟩ : ∃ τ : G → (Cj H →L[ℂ] Cj H), ∀ g v, τ g v = toCj (ρ (θ g)⁻¹ (ofCj v))` from `⟨fun g => opCj (ρ (θ g)⁻¹), fun g v => opCj_apply _ _⟩`. Establish `hcoef : ∀ g (v w : Cj H), ⟪w, τ g v⟫_ℂ = ⟪ofCj v, ρ (θ g) (ofCj w)⟫_ℂ`. Introduce `g v w`. Rewrite using `[inner_def, hτ]`.

Establish `h` using `hR.inner_left (θ g)⁻¹ (ofCj v) (ofCj w)`. Rewrite `h` using `[inv_inv]`. Conclude with `h`. Establish `hT : Formalism.MainNotions.BridgeCSchur.SqRep μ τ`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `v`. Simplify using `only [hτ, hθ1, inv_one, hρ1]`. Both sides reduce to the same expression. Introduce `a b`. Use extensionality with `v`.

Simplify using `only [ContinuousLinearMap.comp_apply, hτ]`. Rewrite using `[hθm, mul_inv_rev, hρm]`. Both sides reduce to the same expression. Introduce `g v`. Rewrite using `[hτ]`.

Conclude with `hiso _ _`. Introduce `v`. Establish `e : (fun g => τ g v) = fun g => toCj (ρ (θ g)⁻¹ (ofCj v))` using `funext fun g => hτ g v`. Rewrite using `[e]`. Conclude with `(hcont (ofCj v)).comp hθc.inv`.

Introduce `v w`. Establish `e : (fun g => ⟪w, τ g v⟫_ℂ) = fun g => ⟪ofCj v, ρ (θ g) (ofCj w)⟫_ℂ`. Use function extensionality and compare the values at `fun g => hcoef g v w`. Rewrite using `[e]`. Conclude with `(hsq (ofCj w) (ofCj v)).comp_measurePreserving hθmp`.

Establish `hirrT : ∀ S : Submodule ℂ (Cj H), IsClosed (S : Set (Cj H)) → (∀ g, ∀ v ∈ S, τ g v ∈ S) → S = ⊥ ∨ S = ⊤`. Introduce `S hS hSi`. Set `S' : Submodule ℂ H` to `{ carrier := {x | toCj x ∈ S} add_mem' := fun ha hb => S.add_mem ha hb zero_mem' := S.zero_mem smul_mem' := fun c x hx => by`. Establish `h2` using `S.smul_mem (conj c) (show toCj x ∈ S from hx)`. Rewrite `h2` using `[smul_def, Complex.conj_conj]`.

Use `show toCj (c • x) ∈ S`. Conclude with `h2 }`. Establish `hS'c : IsClosed (S' : Set H)` using `hS.preimage (eCj (H := H)).symm.continuous`. Establish `hS'i : ∀ h, ∀ x ∈ S', ρ h x ∈ S'`. Introduce `h x hx`.

Establish `h2` using `hSi (θ h⁻¹) (toCj x) hx`. Rewrite `h2` using `[hτ, hθθ, inv_inv]`. Conclude with `h2`. Break down `hirr S' hS'c hS'i with h | h` into its components or cases. Use `left`.

Rewrite using `[eq_bot_iff]`. Introduce `v hv`. Establish `h3 : ofCj v ∈ S'` using `hv`. Rewrite `h3` using `[h, Submodule.mem_bot]`. Conclude with `h3`.

Use `right`. Rewrite using `[eq_top_iff]`. Introduce `v _`. Establish `h3 : ofCj v ∈ S'` using `by rw [h]; trivial`. Conclude with `h3`.

Distinguish the cases in `hne : ∃ U : Cj H ≃ₗᵢ[ℂ] H, ∀ g v, U (τ g v) = ρ g (U v)`. Use `right`. Take `⟨U, hU⟩` from `hne`. Use `⟨((eCj (H := H)).symm.trans U : H ≃ₗᵢ⋆[ℂ] H), ?_, ?_⟩` and prove the remaining obligations. Introduce `g x y`.

Combine the equalities or inequalities in the displayed calculation. Introduce `h v`. Establish `h2` using `hU (θ h)⁻¹ (toCj v)`. Rewrite `h2` using `[hτ, hθinv, hθθ, inv_inv]`. Conclude with `h2`.

Use `left`. Introduce `x y x' y'`. Establish `h0` using `Formalism.MainNotions.BridgeCSchur.schur_orth_ineq hT hR hirrT hirr hne (toCj y) (toCj x) x' y'`. Establish `e : (fun g => ⟪y, ρ (θ g) x⟫_ℂ * star ⟪y', ρ g x'⟫_ℂ) = fun g => ⟪toCj x, τ g (toCj y)⟫_ℂ * star ⟪y', ρ g x'⟫_ℂ`. Use function extensionality and compare the values at `fun g => congrArg (· * star ⟪y', ρ g x'⟫_ℂ) (hcoef g (toCj y) (toCj x)).symm`.

Conclude with `(congrArg (fun f => ∫ g, f g ∂μ) e).trans h0`.
-/
theorem schurDichotomy : SchurDichotomy := by
  intro G _ _ _ _ _ μ _ _ _ H _ _ _ _ θ ρ hθc hθm hθθ hmap hρ1 hρm hiso hcont hsq hirr
  classical
  have hθ1 : θ 1 = 1 := by
    have h := hθm 1 1
    rw [one_mul] at h
    exact mul_left_cancel (a := θ 1) (by rw [mul_one]; exact h.symm)
  have hθinv : ∀ a, θ a⁻¹ = (θ a)⁻¹ := by
    intro a
    apply eq_inv_of_mul_eq_one_left
    rw [← hθm, mul_inv_cancel, hθ1]
  have hθmp : MeasurePreserving θ μ μ := ⟨hθc.measurable, hmap⟩
  have hR : Formalism.MainNotions.BridgeCSchur.SqRep μ ρ := ⟨hρ1, hρm, hiso, hcont, hsq⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : G → (Cj H →L[ℂ] Cj H),
      ∀ g v, τ g v = toCj (ρ (θ g)⁻¹ (ofCj v)) :=
    ⟨fun g => opCj (ρ (θ g)⁻¹), fun g v => opCj_apply _ _⟩
  have hcoef : ∀ g (v w : Cj H), ⟪w, τ g v⟫_ℂ = ⟪ofCj v, ρ (θ g) (ofCj w)⟫_ℂ := by
    intro g v w
    rw [inner_def, hτ]
    have h := hR.inner_left (θ g)⁻¹ (ofCj v) (ofCj w)
    rw [inv_inv] at h
    exact h
  have hT : Formalism.MainNotions.BridgeCSchur.SqRep μ τ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · ext v
      simp only [hτ, hθ1, inv_one, hρ1]
      rfl
    · intro a b
      ext v
      simp only [ContinuousLinearMap.comp_apply, hτ]
      rw [hθm, mul_inv_rev, hρm]
      rfl
    · intro g v
      rw [hτ]
      exact hiso _ _
    · intro v
      have e : (fun g => τ g v) = fun g => toCj (ρ (θ g)⁻¹ (ofCj v)) := funext fun g => hτ g v
      rw [e]
      exact (hcont (ofCj v)).comp hθc.inv
    · intro v w
      have e : (fun g => ⟪w, τ g v⟫_ℂ) = fun g => ⟪ofCj v, ρ (θ g) (ofCj w)⟫_ℂ :=
        funext fun g => hcoef g v w
      rw [e]
      exact (hsq (ofCj w) (ofCj v)).comp_measurePreserving hθmp
  have hirrT : ∀ S : Submodule ℂ (Cj H), IsClosed (S : Set (Cj H)) →
      (∀ g, ∀ v ∈ S, τ g v ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS hSi
    let S' : Submodule ℂ H :=
      { carrier := {x | toCj x ∈ S}
        add_mem' := fun ha hb => S.add_mem ha hb
        zero_mem' := S.zero_mem
        smul_mem' := fun c x hx => by
          have h2 := S.smul_mem (conj c) (show toCj x ∈ S from hx)
          rw [smul_def, Complex.conj_conj] at h2
          show toCj (c • x) ∈ S
          exact h2 }
    have hS'c : IsClosed (S' : Set H) := hS.preimage (eCj (H := H)).symm.continuous
    have hS'i : ∀ h, ∀ x ∈ S', ρ h x ∈ S' := by
      intro h x hx
      have h2 := hSi (θ h⁻¹) (toCj x) hx
      rw [hτ, hθθ, inv_inv] at h2
      exact h2
    rcases hirr S' hS'c hS'i with h | h
    · left
      rw [eq_bot_iff]
      intro v hv
      have h3 : ofCj v ∈ S' := hv
      rw [h, Submodule.mem_bot] at h3
      exact h3
    · right
      rw [eq_top_iff]
      intro v _
      have h3 : ofCj v ∈ S' := by rw [h]; trivial
      exact h3
  by_cases hne : ∃ U : Cj H ≃ₗᵢ[ℂ] H, ∀ g v, U (τ g v) = ρ g (U v)
  · right
    obtain ⟨U, hU⟩ := hne
    refine ⟨((eCj (H := H)).symm.trans U : H ≃ₗᵢ⋆[ℂ] H), ?_, ?_⟩
    · intro g x y
      calc ⟪y, ρ (θ g) x⟫_ℂ = ⟪toCj x, τ g (toCj y)⟫_ℂ := (hcoef g (toCj y) (toCj x)).symm
        _ = ⟪U (toCj x), U (τ g (toCj y))⟫_ℂ := (U.inner_map_map _ _).symm
        _ = ⟪U (toCj x), ρ g (U (toCj y))⟫_ℂ := by rw [hU]
    · intro h v
      have h2 := hU (θ h)⁻¹ (toCj v)
      rw [hτ, hθinv, hθθ, inv_inv] at h2
      exact h2
  · left
    intro x y x' y'
    have h0 := Formalism.MainNotions.BridgeCSchur.schur_orth_ineq hT hR hirrT hirr hne (toCj y) (toCj x) x' y'
    have e : (fun g => ⟪y, ρ (θ g) x⟫_ℂ * star ⟪y', ρ g x'⟫_ℂ) =
        fun g => ⟪toCj x, τ g (toCj y)⟫_ℂ * star ⟪y', ρ g x'⟫_ℂ :=
      funext fun g => congrArg (· * star ⟪y', ρ g x'⟫_ℂ) (hcoef g (toCj y) (toCj x)).symm
    exact (congrArg (fun f => ∫ g, f g ∂μ) e).trans h0

end ReciprocityTheory.ChartRestriction.DS.Mult1
