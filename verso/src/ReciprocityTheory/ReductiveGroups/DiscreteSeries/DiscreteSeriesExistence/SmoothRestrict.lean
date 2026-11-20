import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Use `set P := S.orthogonalProjectionOnto`. Establish `hP : ∀ w : H, w ∈ S → ((P w : S) : H) = w`. Introduce `w hw`. Establish `e : P w = ⟨w, hw⟩` using `by first`. Consider the case `exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨w, hw⟩ : S)`.

Consider the case `exact Submodule.orthogonalProjection_mem_subspace_eq_self (⟨w, hw⟩ : S)`. Consider the case `exact (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := S) ⟨w, hw⟩ : _)`. Consider the case `(show P ((⟨w, hw⟩ : S) : H) = ⟨w, hw⟩; simp [P])`. Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion.

Introduce `h g₀ hg₀`. Take `⟨U, F, hU, hg₀U, hF, hFe⟩` from `h g₀ hg₀`. Use `⟨U, fun g => ((F g : S) : H), hU, hg₀U, (S.subtypeL.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩` and prove the remaining obligations. Introduce `g hgU hg`. Establish `e1` using `hFe g hgU hg`.

Establish `hmem : σ g (x : H) ∈ S` using `hSG g hg x x.2`. Simplify using `only at e1 ⊢`. Rewrite using `[← e1]`. Simplify using `only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]`. Conclude with `(hP _ hmem).symm`.

Introduce `h g₀ hg₀`. Take `⟨U, F, hU, hg₀U, hF, hFe⟩` from `h g₀ hg₀`. Use `⟨U, fun g => P (F g), hU, hg₀U, (P.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩` and prove the remaining obligations. Introduce `g hgU hg`. Establish `e1` using `hFe g hgU hg`.

Simplify using `only at e1 ⊢`. Simplify using `only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]`. Rewrite using `[e1]`.
-/
theorem isSmoothVecU_restrict {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (S : Submodule ℂ H) [S.HasOrthogonalProjection] (hSG : ∀ g ∈ UJset ε, ∀ x ∈ S, σ g x ∈ S) (x : S) :
    IsSmoothVecU ε (fun g => (S.orthogonalProjectionOnto ∘L σ g ∘L S.subtypeL : S →L[ℂ] S)) x ↔
      IsSmoothVecU ε σ (x : H) := by
  set P := S.orthogonalProjectionOnto
  have hP : ∀ w : H, w ∈ S → ((P w : S) : H) = w := by
    intro w hw
    have e : P w = ⟨w, hw⟩ := by
      first
        | exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨w, hw⟩ : S)
        | exact Submodule.orthogonalProjection_mem_subspace_eq_self (⟨w, hw⟩ : S)
        | exact (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := S) ⟨w, hw⟩ : _)
        | (show P ((⟨w, hw⟩ : S) : H) = ⟨w, hw⟩; simp [P])
    rw [e]
  constructor
  · intro h g₀ hg₀
    obtain ⟨U, F, hU, hg₀U, hF, hFe⟩ := h g₀ hg₀
    refine ⟨U, fun g => ((F g : S) : H), hU, hg₀U, (S.subtypeL.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩
    intro g hgU hg
    have e1 := hFe g hgU hg
    have hmem : σ g (x : H) ∈ S := hSG g hg x x.2
    dsimp only at e1 ⊢
    rw [← e1]
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    exact (hP _ hmem).symm
  · intro h g₀ hg₀
    obtain ⟨U, F, hU, hg₀U, hF, hFe⟩ := h g₀ hg₀
    refine ⟨U, fun g => P (F g), hU, hg₀U, (P.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩
    intro g hgU hg
    have e1 := hFe g hgU hg
    dsimp only at e1 ⊢
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    rw [e1]

end ReciprocityTheory.ChartRestriction.DS
