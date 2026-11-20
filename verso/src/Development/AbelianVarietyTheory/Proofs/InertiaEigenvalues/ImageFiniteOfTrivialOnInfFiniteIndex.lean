import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `G Q _ _ ρ J H hH hρ`. Use `haveI := hH`. Use `haveI : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex`. Apply `(Set.finite_range (fun q : G ⧸ H => if h : ∃ g ∈ J, (g : G ⧸ H) = q then ρ h.choose else 1)).subset` to reduce the goal to its premises. Introduce and unpack `_ ⟨g, hg, rfl⟩`.

Use `⟨(g : G ⧸ H), ?_⟩` and prove the remaining obligations. Establish `hex : ∃ g' ∈ J, (g' : G ⧸ H) = g` using `⟨g, hg, rfl⟩`. Simplify using `only`. Rewrite using `[dif_pos hex]`. Take `⟨hJ, hq⟩` from `hex.choose_spec`.

Establish `hmem : (hex.choose)⁻¹ * g ∈ H` using `QuotientGroup.eq.mp hq`. Establish `h1` using `hρ _ (J.mul_mem (J.inv_mem hJ) hg) hmem`. Rewrite `h1` using `[map_mul, map_inv, inv_mul_eq_one]`. Conclude with `h1`.
-/
theorem image_finite_of_trivial_on_inf_finiteIndex : ∀ (G Q : Type) [Group G] [Group Q] (ρ : G →* Q) (J H : Subgroup G), H.FiniteIndex → (∀ g ∈ J, g ∈ H → ρ g = 1) → (ρ '' (J : Set G)).Finite := by
  intro G Q _ _ ρ J H hH hρ
  classical
  haveI := hH
  haveI : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  apply (Set.finite_range (fun q : G ⧸ H =>
    if h : ∃ g ∈ J, (g : G ⧸ H) = q then ρ h.choose else 1)).subset
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨(g : G ⧸ H), ?_⟩
  have hex : ∃ g' ∈ J, (g' : G ⧸ H) = g := ⟨g, hg, rfl⟩
  dsimp only
  rw [dif_pos hex]
  obtain ⟨hJ, hq⟩ := hex.choose_spec
  have hmem : (hex.choose)⁻¹ * g ∈ H := QuotientGroup.eq.mp hq
  have h1 := hρ _ (J.mul_mem (J.inv_mem hJ) hg) hmem
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

end GlobalTheory
