import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLiftDef

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open NumberField

/- English proof (translation)
Introduce `E _ _ _ h`. Take `⟨_, _, hun⟩` from `h`. Set `σ : 𝓞 E →+* 𝓞 E` to `RingOfIntegers.mapRingHom (starRingEnd E)`. Establish `hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = star (x : E)` using `fun x => rfl`. Establish `hσσ : ∀ x, σ (σ x) = x` using `fun x => RingOfIntegers.ext (by rw [hσ, hσ, star_star])`.

Set `J : Ideal (𝓞 E)` to `Ideal.span {t | ∃ x, t = x + σ x}`. Establish `hJ : J = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal J hne`. Take `⟨θ, t, ht, hnot⟩` from `hun P hP`.

Establish `htσ : t = σ θ` using `RingOfIntegers.ext (by rw [hσ]; exact ht)`. Apply `hnot` to reduce the goal to its premises. Establish `h1 : θ + σ θ ∈ P` using `hle (Ideal.subset_span ⟨θ, rfl⟩)`. Establish `h2 : (1 : 𝓞 E) + σ 1 ∈ P` using `hle (Ideal.subset_span ⟨1, rfl⟩)`. Rewrite `h2` using `[map_one]`.

Establish `h3 : θ - t = (θ + σ θ) - (1 + 1) * σ θ` using `by rw [htσ]; ring`. Rewrite using `[h3]`. Conclude with `P.sub_mem h1 (P.mul_mem_right _ h2)`. Establish `key : ∀ y ∈ J, ∃ x, y * σ y = x + σ x`. Introduce `y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem t ht`. Take `⟨x, rfl⟩` from `ht`. Conclude with `⟨(x + σ x) * x, by simp only [map_add, map_mul, hσσ]; ring⟩`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `add y y' _ _ ih ih'`. Take `⟨x, hx⟩` from `ih`. Take `⟨x', hx'⟩` from `ih'`. Conclude with `⟨x + x' + y * σ y', by simp only [map_add, map_mul, hσσ]; linear_combination hx + hx'⟩`. Consider the case `smul a y _ ih`.

Take `⟨x, hx⟩` from `ih`. Conclude with `⟨a * σ a * x, by simp only [smul_eq_mul, map_mul, hσσ]; linear_combination (a * σ a) * hx⟩`. Take `⟨x, hx⟩` from `key 1 (by rw [hJ]; exact Submodule.mem_top)`. Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[map_one, mul_one]`.

Establish `h4` using `congrArg (fun z : 𝓞 E => (z : E)) hx`. Simplify using `only [map_add, map_one] at h4`. Rewrite using `[← hσ]`. Conclude with `h4.symm`.
-/
theorem l_theta : IntegralTraceSurjective := by
  intro E _ _ _ h
  obtain ⟨_, _, hun⟩ := h
  let σ : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)
  have hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = star (x : E) := fun x => rfl
  have hσσ : ∀ x, σ (σ x) = x := fun x => RingOfIntegers.ext (by rw [hσ, hσ, star_star])
  let J : Ideal (𝓞 E) := Ideal.span {t | ∃ x, t = x + σ x}
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨θ, t, ht, hnot⟩ := hun P hP
    have htσ : t = σ θ := RingOfIntegers.ext (by rw [hσ]; exact ht)
    apply hnot
    have h1 : θ + σ θ ∈ P := hle (Ideal.subset_span ⟨θ, rfl⟩)
    have h2 : (1 : 𝓞 E) + σ 1 ∈ P := hle (Ideal.subset_span ⟨1, rfl⟩)
    rw [map_one] at h2
    have h3 : θ - t = (θ + σ θ) - (1 + 1) * σ θ := by rw [htσ]; ring
    rw [h3]
    exact P.sub_mem h1 (P.mul_mem_right _ h2)
  have key : ∀ y ∈ J, ∃ x, y * σ y = x + σ x := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨x, rfl⟩ := ht
      exact ⟨(x + σ x) * x, by simp only [map_add, map_mul, hσσ]; ring⟩
    | zero => exact ⟨0, by simp⟩
    | add y y' _ _ ih ih' =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨x', hx'⟩ := ih'
      exact ⟨x + x' + y * σ y', by simp only [map_add, map_mul, hσσ]; linear_combination hx + hx'⟩
    | smul a y _ ih =>
      obtain ⟨x, hx⟩ := ih
      exact ⟨a * σ a * x, by simp only [smul_eq_mul, map_mul, hσσ]; linear_combination (a * σ a) * hx⟩
  obtain ⟨x, hx⟩ := key 1 (by rw [hJ]; exact Submodule.mem_top)
  refine ⟨x, ?_⟩
  rw [map_one, mul_one] at hx
  have h4 := congrArg (fun z : 𝓞 E => (z : E)) hx
  simp only [map_add, map_one] at h4
  rw [← hσ]
  exact h4.symm

end Formalism.MainNotions.BridgeLemma

end
