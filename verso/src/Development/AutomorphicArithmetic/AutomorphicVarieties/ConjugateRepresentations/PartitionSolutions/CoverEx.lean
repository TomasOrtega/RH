import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PartBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PartProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Window
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Cutoff
open UpperTheory.V.Cj.A

/- English proof (translation)
Introduce `Γ V S _ _ _ _ d G hP A O hAO hA hO`. Take `⟨W, hW⟩` from `UpperTheory.V.Lit.Dr.window Γ V S d G hP`. Take `⟨u, hu⟩` from `UpperTheory.V.Lit.Dr.cutoff Γ V S d G W hW`. Establish `hB : ∀ s j, ∃ B : Set V, IsOpen B ∧ Convex ℝ B ∧ B ⊆ A s ∧ (j ∈ A s → j ∈ B)`. Introduce `s j`.

Distinguish the cases in `hj : j ∈ A s`. Take `⟨r, hr, hb⟩` from `Metric.isOpen_iff.1 (hAO s).1 j hj`. Conclude with `⟨Metric.ball j r, Metric.isOpen_ball, convex_ball j r, hb, fun _ => Metric.mem_ball_self hr⟩`. Conclude with `⟨∅, isOpen_empty, convex_empty, Set.empty_subset _, fun h => absurd h hj⟩`. Use `choose B hBo hBc hBA hBm using hB`.

Establish `hψ` using `fun s => partBase V G.Y G.isOpen (fun j => if j ∈ O s then O s else B s j) (fun j => by`. Distinguish the cases in `hj : j ∈ O s`. Simplify `(hAO s).2.2.1` using `[hj]`. Simplify `hBo s j)` using `[hj]`. Use the proof step `(fun p hp => by`.

Distinguish the cases in `hj : p ∈ O s`. Simplify using `[hj]`. Simplify `hBm s p (((hAO s).2.2.2 hp).resolve_right hj))` using `[hj]`. Use `choose ψ h1 h2 h3 h4 using hψ`. Establish `hsub : ∀ (i : Idx Γ V) s, G.ρ i.g⁻¹ ⁻¹' B (G.σ i.g⁻¹ s) i.j ⊆ A s`.

Introduce `i s p hp`. Conclude with `(hA i.g⁻¹ s p).1 (hBA _ _ hp)`. Use `⟨fun i s => G.ρ i.g⁻¹ ⁻¹' B (G.σ i.g⁻¹ s) i.j, _, ⟨?_, ?_, ?_, ?_⟩, partProd Γ V S V d G u hu ψ h1 h2 h3, hsub, ?_⟩` and prove the remaining obligations. Introduce `i s`. Conclude with `(hBo _ _).preimage (G.ρ _).continuous`.

Introduce `i s`. Conclude with `(hBc _ _).linear_preimage (G.ρ i.g⁻¹).toLinearMap`. Introduce `i s`. Conclude with `(hsub i s).trans (hAO s).2.1`. Introduce `γ i s p`.

Establish `e1 : G.ρ (γ * i.g)⁻¹ (G.ρ γ p) = G.ρ i.g⁻¹ p`. Rewrite using `[mul_inv_rev, map_mul, ContinuousLinearMap.mul_apply, G.ρ_inv_apply]`. Establish `e2 : G.σ (γ * i.g)⁻¹ (G.σ γ s) = G.σ i.g⁻¹ s`. Rewrite using `[mul_inv_rev, map_mul, Equiv.Perm.mul_apply]`. Simplify using the standard rewrite rules.

Simplify using `only [Set.mem_preimage, Idx.smul_g, Idx.smul_j, e1, e2]`. Introduce `i s p hp hne`. Establish `h5` using `h4 _ _ _ (right_ne_zero_of_mul hne)`. Establish `h6 : G.ρ i.g⁻¹ p ∉ O (G.σ i.g⁻¹ s)` using `fun h => hp ((hO i.g⁻¹ s p).1 h)`. Distinguish the cases in `hj : i.j ∈ O (G.σ i.g⁻¹ s)`.

Rewrite `h5` using `[if_pos hj]`. Conclude with `absurd h5 h6`. Rewrite `h5` using `[if_neg hj]`. Conclude with `h5`.
-/
theorem UpperTheory.V.Cj.A.coverEx :
    CoverEx := by
  classical
  intro Γ V S _ _ _ _ d G hP A O hAO hA hO
  obtain ⟨W, hW⟩ := UpperTheory.V.Lit.Dr.window Γ V S d G hP
  obtain ⟨u, hu⟩ := UpperTheory.V.Lit.Dr.cutoff Γ V S d G W hW
  have hB : ∀ s j, ∃ B : Set V, IsOpen B ∧ Convex ℝ B ∧ B ⊆ A s ∧ (j ∈ A s → j ∈ B) := by
    intro s j
    by_cases hj : j ∈ A s
    · obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 (hAO s).1 j hj
      exact ⟨Metric.ball j r, Metric.isOpen_ball, convex_ball j r, hb, fun _ => Metric.mem_ball_self hr⟩
    · exact ⟨∅, isOpen_empty, convex_empty, Set.empty_subset _, fun h => absurd h hj⟩
  choose B hBo hBc hBA hBm using hB
  have hψ := fun s => partBase V G.Y G.isOpen (fun j => if j ∈ O s then O s else B s j)
    (fun j => by
      by_cases hj : j ∈ O s
      · simpa [hj] using (hAO s).2.2.1
      · simpa [hj] using hBo s j)
    (fun p hp => by
      by_cases hj : p ∈ O s
      · simp [hj]
      · simpa [hj] using hBm s p (((hAO s).2.2.2 hp).resolve_right hj))
  choose ψ h1 h2 h3 h4 using hψ
  have hsub : ∀ (i : Idx Γ V) s, G.ρ i.g⁻¹ ⁻¹' B (G.σ i.g⁻¹ s) i.j ⊆ A s := by
    intro i s p hp
    exact (hA i.g⁻¹ s p).1 (hBA _ _ hp)
  refine ⟨fun i s => G.ρ i.g⁻¹ ⁻¹' B (G.σ i.g⁻¹ s) i.j, _, ⟨?_, ?_, ?_, ?_⟩,
    partProd Γ V S V d G u hu ψ h1 h2 h3, hsub, ?_⟩
  · intro i s
    exact (hBo _ _).preimage (G.ρ _).continuous
  · intro i s
    exact (hBc _ _).linear_preimage (G.ρ i.g⁻¹).toLinearMap
  · intro i s
    exact (hsub i s).trans (hAO s).2.1
  · intro γ i s p
    have e1 : G.ρ (γ * i.g)⁻¹ (G.ρ γ p) = G.ρ i.g⁻¹ p := by
      rw [mul_inv_rev, map_mul, ContinuousLinearMap.mul_apply, G.ρ_inv_apply]
    have e2 : G.σ (γ * i.g)⁻¹ (G.σ γ s) = G.σ i.g⁻¹ s := by
      rw [mul_inv_rev, map_mul, Equiv.Perm.mul_apply]; simp
    simp only [Set.mem_preimage, Idx.smul_g, Idx.smul_j, e1, e2]
  · intro i s p hp hne
    have h5 := h4 _ _ _ (right_ne_zero_of_mul hne)
    have h6 : G.ρ i.g⁻¹ p ∉ O (G.σ i.g⁻¹ s) := fun h => hp ((hO i.g⁻¹ s p).1 h)
    by_cases hj : i.j ∈ O (G.σ i.g⁻¹ s)
    · rw [if_pos hj] at h5
      exact absurd h5 h6
    · rw [if_neg hj] at h5
      exact h5
