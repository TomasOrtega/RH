import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsChartMax
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartHomogenise

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F : Type} [Field F] {n : ℕ}

/- English proof (translation)
Use `⟨∑ d ∈ Finset.range (g.totalDegree + 1), ℓ ^ (g.totalDegree - d) * homogeneousComponent d g, g.totalDegree, ?_, ?_⟩` and prove the remaining obligations. Use `IsHomogeneous.sum _ _ _ fun d hd => ?_` and prove the remaining obligations. Establish `hdD : d ≤ g.totalDegree` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)`. Establish `h` using `(hℓ.pow (g.totalDegree - d)).mul (homogeneousComponent_isHomogeneous d g)`. Rewrite `h` using `[one_mul, Nat.sub_add_cancel hdD]`. Then use the resulting hypothesis.

Establish `e : ∑ d ∈ Finset.range (g.totalDegree + 1), ℓ ^ (g.totalDegree - d) * homogeneousComponent d g - g = ∑ d ∈ Finset.range (g.totalDegree + 1), (ℓ ^ (g.totalDegree - d) - 1) * homogeneousComponent d g`. Simplify using `only [sub_one_mul, Finset.sum_sub_distrib, sum_homogeneousComponent]`. Rewrite using `[e]`. Use `Ideal.sum_mem _ fun d _ => Ideal.mul_mem_right _ _ ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_span_singleton]`.

Simplify using `using sub_dvd_pow_sub_pow ℓ 1 (g.totalDegree - d)`.
-/
theorem exists_homogeneous_sub_mem_span (ℓ g : MvPolynomial (Fin n) F) (hℓ : ℓ.IsHomogeneous 1) :
    ∃ (G : MvPolynomial (Fin n) F) (D : ℕ), G.IsHomogeneous D ∧ G - g ∈ Ideal.span {ℓ - 1} := by
  classical
  refine ⟨∑ d ∈ Finset.range (g.totalDegree + 1), ℓ ^ (g.totalDegree - d) * homogeneousComponent d g,
    g.totalDegree, ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ fun d hd => ?_
    have hdD : d ≤ g.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    have h := (hℓ.pow (g.totalDegree - d)).mul (homogeneousComponent_isHomogeneous d g)
    rwa [one_mul, Nat.sub_add_cancel hdD] at h
  · have e : ∑ d ∈ Finset.range (g.totalDegree + 1), ℓ ^ (g.totalDegree - d) * homogeneousComponent d g - g =
        ∑ d ∈ Finset.range (g.totalDegree + 1), (ℓ ^ (g.totalDegree - d) - 1) * homogeneousComponent d g := by
      simp only [sub_one_mul, Finset.sum_sub_distrib, sum_homogeneousComponent]
    rw [e]
    refine Ideal.sum_mem _ fun d _ => Ideal.mul_mem_right _ _ ?_
    rw [Ideal.mem_span_singleton]
    simpa using sub_dvd_pow_sub_pow ℓ 1 (g.totalDegree - d)

/- English proof (translation)
Introduce `F _ n Q t hQ ht`. Use `set 𝒜 := homogeneousSubmodule (Fin n) F`. Use `set W : Ideal (MvPolynomial (Fin n) F) := (Q.homogeneousCore 𝒜).toIdeal with hW`. Establish `hWQ : W ≤ Q` using `Ideal.toIdeal_homogeneousCore_le _ _`. Establish `hWprime : W.IsPrime` using `hQ.homogeneousCore`.

Establish `hWhom : IsHomogIdeal W` using `(isHomogIdeal_iff W).mpr (Q.homogeneousCore 𝒜).isHomogeneous`. Establish `hℓ : (linForm t).IsHomogeneous 1` using `IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _`. Establish `hℓQ : linForm t ∉ Q`. Introduce `h`. Apply `hQ.ne_top` to reduce the goal to its premises.

Rewrite using `[Ideal.eq_top_iff_one]`. Simplify using `using Q.sub_mem h ht`. Establish `hℓW : linForm t ∉ W` using `fun h => hℓQ (hWQ h)`. Establish `hrel : IsRelevant W`. Assume the negation of the conclusion as `h`.

Simplify using `only [IsRelevant, not_exists, not_not] at h`. Conclude with `hℓW (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (h j))`. Use `⟨W, ⟨hWprime, hWhom, hrel⟩, hℓW, le_antisymm ?_ ?_, ?_⟩` and prove the remaining obligations. Conclude with `sup_le hWQ ((Ideal.span_singleton_le_iff_mem _).mpr ht)`. Introduce `g hg`.

Take `⟨G, D, hG, hGg⟩` from `exists_homogeneous_sub_mem_span (linForm t) g hℓ`. Establish `hspan : Ideal.span {linForm t - 1} ≤ Q` using `(Ideal.span_singleton_le_iff_mem _).mpr ht`. Establish `hGQ : G ∈ Q` using `by simpa using Q.add_mem (hspan hGg) hg`. Establish `hGW : G ∈ W` using `Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨D, (mem_homogeneousSubmodule D G).mpr hG⟩ hGQ`. Establish `: g = G - (G - g)` using `by ring`.

Rewrite using `[this]`. Conclude with `Ideal.sub_mem _ (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hGg)`. Introduce `J hJ hJQ`. Establish `hJh` using `(isHomogIdeal_iff J).mp hJ`. Rewrite using `[← hJh.toIdeal_homogeneousCore_eq_self]`.

Conclude with `Ideal.homogeneousCore_mono _ hJQ`.
-/
theorem proof : ChartHomogenise.Statement := by
  intro F _ n Q t hQ ht
  set 𝒜 := homogeneousSubmodule (Fin n) F
  set W : Ideal (MvPolynomial (Fin n) F) := (Q.homogeneousCore 𝒜).toIdeal with hW
  have hWQ : W ≤ Q := Ideal.toIdeal_homogeneousCore_le _ _
  have hWprime : W.IsPrime := hQ.homogeneousCore
  have hWhom : IsHomogIdeal W := (isHomogIdeal_iff W).mpr (Q.homogeneousCore 𝒜).isHomogeneous
  have hℓ : (linForm t).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _
  have hℓQ : linForm t ∉ Q := by
    intro h
    apply hQ.ne_top
    rw [Ideal.eq_top_iff_one]
    simpa using Q.sub_mem h ht
  have hℓW : linForm t ∉ W := fun h => hℓQ (hWQ h)
  have hrel : IsRelevant W := by
    by_contra h
    simp only [IsRelevant, not_exists, not_not] at h
    exact hℓW (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (h j))
  refine ⟨W, ⟨hWprime, hWhom, hrel⟩, hℓW, le_antisymm ?_ ?_, ?_⟩
  · exact sup_le hWQ ((Ideal.span_singleton_le_iff_mem _).mpr ht)
  · intro g hg
    obtain ⟨G, D, hG, hGg⟩ := exists_homogeneous_sub_mem_span (linForm t) g hℓ
    have hspan : Ideal.span {linForm t - 1} ≤ Q := (Ideal.span_singleton_le_iff_mem _).mpr ht
    have hGQ : G ∈ Q := by simpa using Q.add_mem (hspan hGg) hg
    have hGW : G ∈ W :=
      Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨D, (mem_homogeneousSubmodule D G).mpr hG⟩ hGQ
    have : g = G - (G - g) := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hGg)
  · intro J hJ hJQ
    have hJh := (isHomogIdeal_iff J).mp hJ
    rw [← hJh.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono _ hJQ

end ChartHomogenise

end

end GroundTheory.Heights₂.Heights
