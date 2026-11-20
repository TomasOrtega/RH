import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

/- English proof (translation)
Introduce `Γ Γ' _ _ f H H' hc hle hp ⟨τ, hτ, hτ'⟩`. Establish `hN : H'.Normal`. Use `⟨fun n hn g => ?_⟩` and prove the remaining obligations. Establish `h1 : g * n * g⁻¹ * n⁻¹ ∈ H'` using `hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))`. Establish `h2 : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n` using `by group`.

Rewrite using `[h2]`. Conclude with `H'.mul_mem h1 hn`. Rewrite using `[Subgroup.relIndex_comap]`. Use `set J := (H.comap f).map f with hJ`. Establish `hJH : J ≤ H` using `Subgroup.map_comap_le _ _`.

Establish `hmul : H'.relIndex (H' ⊔ J) * (H' ⊔ J).relIndex H = H'.relIndex H` using `Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hle hJH)`. Rewrite `hmul` using `[Subgroup.relIndex_sup_left]`. Establish `hne : H'.relIndex J ≠ 1`. Introduce `h`. Rewrite `h` using `[Subgroup.relIndex_eq_one]`.

Conclude with `hτ' (h ⟨τ, hτ, rfl⟩)`. Conclude with `(hp.eq_one_or_self_of_dvd _ ⟨_, hmul.symm⟩).resolve_left hne`.
-/
theorem indexComap : IndexComap := by
  intro Γ Γ' _ _ f H H' hc hle hp ⟨τ, hτ, hτ'⟩
  have hN : H'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ H' :=
      hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    have h2 : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n := by group
    rw [h2]
    exact H'.mul_mem h1 hn
  rw [Subgroup.relIndex_comap]
  set J := (H.comap f).map f with hJ
  have hJH : J ≤ H := Subgroup.map_comap_le _ _
  have hmul : H'.relIndex (H' ⊔ J) * (H' ⊔ J).relIndex H = H'.relIndex H :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hle hJH)
  rw [Subgroup.relIndex_sup_left] at hmul
  have hne : H'.relIndex J ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    exact hτ' (h ⟨τ, hτ, rfl⟩)
  exact (hp.eq_one_or_self_of_dvd _ ⟨_, hmul.symm⟩).resolve_left hne

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
