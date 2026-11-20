import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI

open scoped InnerProductSpace

noncomputable section

namespace DiscreteGroups.sglob.LConv

open CompanionTheory.D.gk.admitted

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Prove the first alternative. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
-/
theorem irred_of_scalar {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : G →* (H →L[ℂ] H)) (hπ : ∀ g x, ‖π g x‖ = ‖x‖)
    (hsc : ∀ T : H →L[ℂ] H, (∀ g, T * π g = π g * T) → ∃ c : ℂ, T = c • (1 : H →L[ℂ] H))
    (S : Submodule ℂ H) (hcl : IsClosed (S : Set H)) (hS : ∀ g, ∀ v ∈ S, π g v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  have : CompleteSpace S := hcl.completeSpace_coe
  have hcomm : ∀ g, S.starProjection * π g = π g * S.starProjection := by
    intro g
    ext z
    show S.starProjection (π g z) = π g (S.starProjection z)
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact hS g _ (S.starProjection_apply_mem z)
    · intro w hw
      rw [← map_sub, FinOfPIAux.inner_left π hπ]
      exact S.starProjection_inner_eq_zero z _ (hS _ _ hw)
  obtain ⟨c, hc⟩ := hsc _ hcomm
  have hP : ∀ z, S.starProjection z = c • z := fun z => by rw [hc]; rfl
  by_cases h0 : S = ⊥
  · exact Or.inl h0
  · right
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    have h1 : c • x = x := by rw [← hP, Submodule.starProjection_eq_self_iff.mpr hx]
    have hc1 : c = 1 := by
      have h2 : (c - 1) • x = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      rcases smul_eq_zero.mp h2 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hx0
    rw [eq_top_iff]
    intro z _
    have h3 := S.starProjection_apply_mem z
    rwa [hP, hc1, one_smul] at h3

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.
-/
theorem word_eq_mul_prod {R : Type*} [Ring R] (e : R) (he : e * e = e) (l : List R) :
    word e l = e * (l.map fun a => e * a * e).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [word_cons, ih, List.map_cons, List.prod_cons, ← mul_assoc, he]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finiteOfAlt : FiniteOfAlt := by
  intro G _ H _ _ _ π hπ hsc e he d hd
  have h : ∀ g : Fin d → G, stdPoly e (fun i => π (g i)) = 0 := by
    intro g
    have h0 := congrArg (fun X => e * X) (hd g)
    simp only [mul_zero] at h0
    rw [← h0, stdPoly, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [word_eq_mul_prod e he, List.map_ofFn, mul_smul_comm, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    rfl
  obtain ⟨hfd, -⟩ := finite_rank_of_irreducible_unitary G H π hπ (irred_of_scalar π hπ hsc) e d h
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional _).mpr hfd
  refine ⟨s, fun x => ?_⟩
  rw [hs]
  exact LinearMap.mem_range_self (e : H →ₗ[ℂ] H) x

end DiscreteGroups.sglob.LConv

end
