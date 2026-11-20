import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMap

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Far

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}

/- English proof (translation)
Establish `hK` using `isCompact_KR (n := n)`. Establish `hs : Continuous (sL Q)` using `hL.cont Q`. Establish `hF : Continuous (F0 (n` using `n) p q e) := continuous_weight_factor hD p q e`. Take `⟨B, hB⟩` from `hK.exists_bound_of_continuousOn hs.continuousOn`. Establish `hne : ((KR n : Subgroup (GR n)) : Set (GR n)).Nonempty` using `⟨1, (KR n).one_mem⟩`.

Take `⟨k0, -, hmin⟩` from `hK.exists_isMinOn hne hF.norm.continuousOn`. Use `set δ := ‖F0 p q e k0‖ with hδdef`. Establish `hδ : 0 < δ` using `norm_pos_iff.mpr (weight_factor_ne_zero hD p q e k0)`. Use `⟨max B 0 / δ, div_nonneg (le_max_right _ _) hδ.le, fun y => ?_⟩` and prove the remaining obligations. Take `⟨u, k, hu, hk, rfl⟩` from `hI n y`.

Establish `hmk : δ ≤ ‖F0 p q e k‖` using `hmin hk`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sL_bound (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ) (Q : PX m n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : GR n, ‖sL Q y‖ ≤ C * ‖F0 p q e y‖ := by
  have hK := isCompact_KR (n := n)
  have hs : Continuous (sL Q) := hL.cont Q
  have hF : Continuous (F0 (n := n) p q e) := continuous_weight_factor hD p q e
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hs.continuousOn
  have hne : ((KR n : Subgroup (GR n)) : Set (GR n)).Nonempty := ⟨1, (KR n).one_mem⟩
  obtain ⟨k0, -, hmin⟩ := hK.exists_isMinOn hne hF.norm.continuousOn
  set δ := ‖F0 p q e k0‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.mpr (weight_factor_ne_zero hD p q e k0)
  refine ⟨max B 0 / δ, div_nonneg (le_max_right _ _) hδ.le, fun y => ?_⟩
  obtain ⟨u, k, hu, hk, rfl⟩ := hI n y
  have hmk : δ ≤ ‖F0 p q e k‖ := hmin hk
  calc ‖sL Q (u * k)‖ = ‖F0 p q e u‖ * ‖sL Q k‖ := by rw [hL.law Q u k hu, norm_mul]
    _ ≤ ‖F0 p q e u‖ * max B 0 :=
        mul_le_mul_of_nonneg_left ((hB k hk).trans (le_max_left _ _)) (norm_nonneg _)
    _ = (max B 0 / δ) * (‖F0 p q e u‖ * δ) := by field_simp
    _ ≤ (max B 0 / δ) * (‖F0 p q e u‖ * ‖F0 p q e k‖) := by gcongr
    _ = (max B 0 / δ) * ‖F0 p q e (u * k)‖ := by rw [((hM n p q e).1 u k hk).1, norm_mul]

/- English proof (translation)
Break down `le_total 1 a with h | h` into its components or cases. Conclude with `(Real.rpow_le_rpow_of_exponent_le h h₂).trans (le_add_of_nonneg_left (Real.rpow_nonneg ha.le _))`. Conclude with `(Real.rpow_le_rpow_of_exponent_ge ha h h₁).trans (le_add_of_nonneg_right (Real.rpow_nonneg ha.le _))`.
-/
theorem rpow_le_add {a x₁ x₂ s : ℝ} (ha : 0 < a) (h₁ : x₁ ≤ s) (h₂ : s ≤ x₂) : a ^ s ≤ a ^ x₁ + a ^ x₂ := by
  rcases le_total 1 a with h | h
  · exact (Real.rpow_le_rpow_of_exponent_le h h₂).trans (le_add_of_nonneg_left (Real.rpow_nonneg ha.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge ha h h₁).trans (le_add_of_nonneg_right (Real.rpow_nonneg ha.le _))

section Glob

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

/- English proof (translation)
Take `⟨x₀, y, S, r, hr, rfl, h⟩` from `hG.split x`. Rewrite using `[(h y).1]`. Conclude with `mul_pos hr (hLoc_pos hD y)`.
-/
theorem Ht_pos (hD : CayleyBlocksInvertible) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (x : G) : 0 < (Ht x : ℝ) := by
  obtain ⟨x₀, y, S, r, hr, rfl, h⟩ := hG.split x
  rw [(h y).1]
  exact mul_pos hr (hLoc_pos hD y)

/- English proof (translation)
Take `⟨C, hC0, hC⟩` from `sL_bound hI hM hD hL Q`. Use `⟨C, hC0, fun x => ?_⟩` and prove the remaining obligations. Take `⟨x₀, y, S, r, hr, rfl, h⟩` from `hG.split x`. Rewrite using `[(h y).2 Q, (h y).2 1, hL.vac y, norm_mul, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sec_bound (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (Q : PX m n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : G, ‖sec Q x‖ ≤ C * ‖sec 1 x‖ := by
  obtain ⟨C, hC0, hC⟩ := sL_bound hI hM hD hL Q
  refine ⟨C, hC0, fun x => ?_⟩
  obtain ⟨x₀, y, S, r, hr, rfl, h⟩ := hG.split x
  rw [(h y).2 Q, (h y).2 1, hL.vac y, norm_mul, norm_mul]
  calc ‖S‖ * ‖sL Q y‖ ≤ ‖S‖ * (C * ‖F0 p q e y‖) := mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _)
    _ = C * (‖S‖ * ‖F0 p q e y‖) := by ring

/- English proof (translation)
Unfold `hz`. Rewrite using `[norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (Ht_pos hD hG x), Complex.sub_re]`.
-/
theorem norm_hz (hD : CayleyBlocksInvertible) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (z : ℂ) (Q : PX m n) (x : G) :
    ‖hz Ht sec s₀ z Q x‖ = (Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec Q x‖ := by
  unfold hz
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (Ht_pos hD hG x), Complex.sub_re]

end Glob

end PositivityTheory.Rg.Sw.AbsSt.Far
