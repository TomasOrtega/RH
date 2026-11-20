import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ Γ _ _ _ _ a J x θ C hC hA ε hε g`. Take `⟨s, c, hs, hP⟩` from `hA (ε / 2) (by linarith)`. Establish `hmem : ∀ η ∈ s, ∃ ρ ∈ C, (fun j => trc ρ (x j)) = η` using `fun η hη => hs hη`. Use `choose! R hRC hRη using hmem`. Use `set F : Γ → PadicAlgCl l := fun h => ∑ η ∈ s, c η * trc (R η) h with hF`.

Establish `hFc : Continuous F`. Use `continuous_finset_sum _ fun η hη => continuous_const.mul ?_` and prove the remaining obligations. Establish `h1 : Continuous fun h => ((R η h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))` using `Units.continuous_val.comp (hC _ (hRC η hη))`. Conclude with `(continuous_id.matrix_trace).comp h1`. Use `⟨F ⁻¹' Metric.ball (F g) (ε / 4), hFc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by linarith)), ?_⟩` and prove the remaining obligations.

Introduce `i j hi hj`. Establish `key` using `hP (MvPolynomial.X i - MvPolynomial.X j)`. Simplify using `only [map_sub, MvPolynomial.aeval_X] at key`. Establish `hsum : ∑ η ∈ s, c η * (η i - η j) = F (x i) - F (x j)`. Rewrite using `[hF]`.

Simplify using `only`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun η hη => ?_` and prove the remaining obligations. Establish `hi2 : η i = trc (R η) (x i)` using `(congrFun (hRη η hη) i).symm`. Establish `hj2 : η j = trc (R η) (x j)` using `(congrFun (hRη η hη) j).symm`.

Rewrite using `[hi2, hj2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[hsum]`. Establish `hi' : ‖F (x i) - F g‖ < ε / 4` using `by simpa [dist_eq_norm] using hi`. Establish `hj' : ‖F (x j) - F g‖ < ε / 4` using `by simpa [dist_eq_norm] using hj`.

Establish `hd : ‖F (x i) - F (x j)‖ ≤ ε / 2`. Establish `e : F (x i) - F (x j) = (F (x i) - F g) - (F (x j) - F g)` using `by ring`. Rewrite using `[e]`. Combine the linear relations using `[norm_sub_le (F (x i) - F g) (F (x j) - F g)]`. Establish `e2 : θ i - θ j = (θ i - θ j - (F (x i) - F (x j))) + (F (x i) - F (x j))` using `by ring`.

Rewrite using `[e2]`. Combine the linear relations using `[norm_add_le (θ i - θ j - (F (x i) - F (x j))) (F (x i) - F (x j))]`.
-/
theorem polyApprox_trc_locally_cauchy : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (J : Type) (x : J → Γ) (θ : J → PadicAlgCl l) (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), (∀ ρ ∈ C, Continuous ρ) → PolyApprox θ ((fun ρ j => trc ρ (x j)) '' C) → ∀ ε : ℝ, 0 < ε → ∀ g : Γ, ∃ V ∈ nhds g, ∀ i j, x i ∈ V → x j ∈ V → ‖θ i - θ j‖ ≤ ε := by
  intro l _ Γ _ _ _ _ a J x θ C hC hA ε hε g
  obtain ⟨s, c, hs, hP⟩ := hA (ε / 2) (by linarith)
  have hmem : ∀ η ∈ s, ∃ ρ ∈ C, (fun j => trc ρ (x j)) = η := fun η hη => hs hη
  choose! R hRC hRη using hmem
  set F : Γ → PadicAlgCl l := fun h => ∑ η ∈ s, c η * trc (R η) h with hF
  have hFc : Continuous F := by
    refine continuous_finset_sum _ fun η hη => continuous_const.mul ?_
    have h1 : Continuous fun h => ((R η h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) :=
      Units.continuous_val.comp (hC _ (hRC η hη))
    exact (continuous_id.matrix_trace).comp h1
  refine ⟨F ⁻¹' Metric.ball (F g) (ε / 4), hFc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by linarith)), ?_⟩
  intro i j hi hj
  have key := hP (MvPolynomial.X i - MvPolynomial.X j)
  simp only [map_sub, MvPolynomial.aeval_X] at key
  have hsum : ∑ η ∈ s, c η * (η i - η j) = F (x i) - F (x j) := by
    rw [hF]; simp only
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun η hη => ?_
    have hi2 : η i = trc (R η) (x i) := (congrFun (hRη η hη) i).symm
    have hj2 : η j = trc (R η) (x j) := (congrFun (hRη η hη) j).symm
    rw [hi2, hj2]; ring
  rw [hsum] at key
  have hi' : ‖F (x i) - F g‖ < ε / 4 := by simpa [dist_eq_norm] using hi
  have hj' : ‖F (x j) - F g‖ < ε / 4 := by simpa [dist_eq_norm] using hj
  have hd : ‖F (x i) - F (x j)‖ ≤ ε / 2 := by
    have e : F (x i) - F (x j) = (F (x i) - F g) - (F (x j) - F g) := by ring
    rw [e]; linarith [norm_sub_le (F (x i) - F g) (F (x j) - F g)]
  have e2 : θ i - θ j = (θ i - θ j - (F (x i) - F (x j))) + (F (x i) - F (x j)) := by ring
  rw [e2]; linarith [norm_add_le (θ i - θ j - (F (x i) - F (x j))) (F (x i) - F (x j))]

end GlobalTheory
