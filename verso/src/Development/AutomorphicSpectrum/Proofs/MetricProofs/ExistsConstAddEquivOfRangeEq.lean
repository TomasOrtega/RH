import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionTensorPullbackRingHomBijective
open Set

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce `n g Λ Λ' _ _ _ _ B hB hc hne P P' hP hP' h`. Establish `h1 : ∀ x : Λ', ∃ y : Λ, ∀ b ∈ B, P' b x = P b y` using `fun x => exists_const_of_section_mem_range n g Λ B hB hc hne P (fun b => P' b x) hP (hP' x) (fun b hb => by rw [(h b hb).2.2]; exact ⟨x, rfl⟩)`. Establish `h2 : ∀ y : Λ, ∃ x : Λ', ∀ b ∈ B, P b y = P' b x` using `fun y => exists_const_of_section_mem_range n g Λ' B hB hc hne P' (fun b => P b y) hP' (hP y) (fun b hb => by rw [← (h b hb).2.2]; exact ⟨y, rfl⟩)`. Use `choose f hf using h1`. Use `choose k hk using h2`.

Take `⟨b₀, hb₀⟩` from `hne`. Take `⟨hi, hi', -⟩` from `h b₀ hb₀`. Use `⟨{ toFun := f, invFun := k, left_inv := ?_, right_inv := ?_, map_add' := ?_ }, ?_⟩` and prove the remaining obligations. Introduce `x`. Apply `hi'` to reduce the goal to its premises.

Rewrite using `[← hk _ b₀ hb₀, ← hf _ b₀ hb₀]`. Introduce `y`. Apply `hi` to reduce the goal to its premises. Rewrite using `[← hf _ b₀ hb₀, ← hk _ b₀ hb₀]`. Introduce `x x'`.

Apply `hi` to reduce the goal to its premises. Rewrite using `[map_add, ← hf _ b₀ hb₀, ← hf _ b₀ hb₀, ← hf _ b₀ hb₀, map_add]`. Introduce `b hb x`. Conclude with `hf x b hb`.
-/
theorem exists_const_addEquiv_of_range_eq : ∀ (n g : ℕ) (Λ Λ' : Type) [AddCommGroup Λ] [Countable Λ] [AddCommGroup Λ'] [Countable Λ'] (B : Set (Fin n → ℂ)), IsOpen B → IsPreconnected B → B.Nonempty → ∀ (P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))) (P' : (Fin n → ℂ) → (Λ' →+ (Fin g → ℂ))), (∀ x, DifferentiableOn ℂ (fun b => P b x) B) → (∀ x, DifferentiableOn ℂ (fun b => P' b x) B) → (∀ b ∈ B, Function.Injective (P b) ∧ Function.Injective (P' b) ∧ (P b).range = (P' b).range) → ∃ T : Λ' ≃+ Λ, ∀ b ∈ B, ∀ x, P' b x = P b (T x) := by
  intro n g Λ Λ' _ _ _ _ B hB hc hne P P' hP hP' h
  have h1 : ∀ x : Λ', ∃ y : Λ, ∀ b ∈ B, P' b x = P b y := fun x =>
    exists_const_of_section_mem_range n g Λ B hB hc hne P (fun b => P' b x) hP (hP' x)
      (fun b hb => by rw [(h b hb).2.2]; exact ⟨x, rfl⟩)
  have h2 : ∀ y : Λ, ∃ x : Λ', ∀ b ∈ B, P b y = P' b x := fun y =>
    exists_const_of_section_mem_range n g Λ' B hB hc hne P' (fun b => P b y) hP' (hP y)
      (fun b hb => by rw [← (h b hb).2.2]; exact ⟨y, rfl⟩)
  choose f hf using h1
  choose k hk using h2
  obtain ⟨b₀, hb₀⟩ := hne
  obtain ⟨hi, hi', -⟩ := h b₀ hb₀
  refine ⟨{ toFun := f, invFun := k, left_inv := ?_, right_inv := ?_, map_add' := ?_ }, ?_⟩
  · intro x
    apply hi'
    rw [← hk _ b₀ hb₀, ← hf _ b₀ hb₀]
  · intro y
    apply hi
    rw [← hf _ b₀ hb₀, ← hk _ b₀ hb₀]
  · intro x x'
    apply hi
    rw [map_add, ← hf _ b₀ hb₀, ← hf _ b₀ hb₀, ← hf _ b₀ hb₀, map_add]
  · intro b hb x
    exact hf x b hb

end GlobalTheory.CompanionTheory.Ar.Flat
