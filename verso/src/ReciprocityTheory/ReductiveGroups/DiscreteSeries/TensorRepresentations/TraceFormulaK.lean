import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaC

noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Introduce `x hx v hv`. Use `set x1 : S₁ := U.symm ⟨x, hx⟩ with hx1`. Use `set v1 : S₁ := U.symm ⟨v, hv⟩ with hv1`. Establish `ex : ((U x1 : S₂) : H₂) = x` using `by rw [hx1, LinearIsometryEquiv.apply_symm_apply]`. Establish `ev : ((U v1 : S₂) : H₂) = v` using `by rw [hv1, LinearIsometryEquiv.apply_symm_apply]`.

Establish `hcoef : ∀ g : Formalism.REAL.UJ ε, inner ℂ x (σ₂ (Formalism.MainNotions.S.umat g) v) = Formalism.MainNotions.S.coefOn (tfClRep σ₁ S₁) v1 x1 g`. Introduce `g`. Establish `hg` using `umat_mem_UJset ε g`. Use `set y : S₁ := ⟨σ₁ (Formalism.MainNotions.S.umat g) (v1 : H₁), hS₁ _ hg _ v1.2⟩ with hy`. Establish `h1` using `hU _ hg y v1 rfl`.

Rewrite using `[← ex, ← ev, ← h1, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]`. Use `show inner ℂ x1 y = inner ℂ x1 (tfClRep σ₁ S₁ (Formalism.MainNotions.S.umat g) v1)`. Use `congr 1`. Conclude with `Subtype.ext (tfClRep_coe σ₁ S₁ (hS₁ _ hg) v1).symm`. Take `⟨-, hint, hval⟩` from `hd.1, (hd.2 v1 x1 v1 x1).1, (hd.2 v1 x1 v1 x1).2`.

Establish `hnx : ‖x‖ = ‖x1‖` using `by rw [← ex]; exact U.norm_map x1`. Establish `hnv : ‖v‖ = ‖v1‖` using `by rw [← ev]; exact U.norm_map v1`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[← integral_complex_ofReal]`. Establish `e : ∀ g : Formalism.REAL.UJ ε, ((‖inner ℂ x (σ₂ (Formalism.MainNotions.S.umat g) v)‖ ^ 2 : ℝ) : ℂ) = Formalism.MainNotions.S.coefOn (tfClRep σ₁ S₁) v1 x1 g * star (Formalism.MainNotions.S.coefOn (tfClRep σ₁ S₁) v1 x1 g)`.

Introduce `g`. Rewrite using `[hcoef, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Repeatedly rewrite using `[e]`. Establish `h1 : inner ℂ v1 v1 = ((‖v1‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[inner_self_eq_norm_sq_to_K]`.

Use `norm_cast`. Establish `h2 : inner ℂ x1 x1 = ((‖x1‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[inner_self_eq_norm_sq_to_K]`. Use `norm_cast`. Rewrite using `[hval, h1, h2, hnx, hnv]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tf_schur_transfer {n : ℕ} {ε : Fin n → Bool} {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [CompleteSpace H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
    (S₁ : Submodule ℂ H₁) [S₁.HasOrthogonalProjection] (S₂ : Submodule ℂ H₂) (U : S₁ ≃ₗᵢ[ℂ] S₂)
    (hU : ∀ g ∈ UJset ε, ∀ x y : S₁, (x : H₁) = σ₁ g (y : H₁) → ((U x : S₂) : H₂) = σ₂ g ((U y : S₂) : H₂))
    (hS₁ : ∀ g ∈ UJset ε, ∀ x ∈ S₁, σ₁ g x ∈ S₁) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ₁ S₁) d) :
    ∀ x ∈ S₂, ∀ v ∈ S₂, ∫ g : Formalism.REAL.UJ ε, ‖inner ℂ x (σ₂ (Formalism.MainNotions.S.umat g) v)‖ ^ 2 ∂(Formalism.REAL.muG ε) =
      ‖x‖ ^ 2 * ‖v‖ ^ 2 / d := by
  intro x hx v hv
  set x1 : S₁ := U.symm ⟨x, hx⟩ with hx1
  set v1 : S₁ := U.symm ⟨v, hv⟩ with hv1
  have ex : ((U x1 : S₂) : H₂) = x := by rw [hx1, LinearIsometryEquiv.apply_symm_apply]
  have ev : ((U v1 : S₂) : H₂) = v := by rw [hv1, LinearIsometryEquiv.apply_symm_apply]
  have hcoef : ∀ g : Formalism.REAL.UJ ε, inner ℂ x (σ₂ (Formalism.MainNotions.S.umat g) v) =
      Formalism.MainNotions.S.coefOn (tfClRep σ₁ S₁) v1 x1 g := by
    intro g
    have hg := umat_mem_UJset ε g
    set y : S₁ := ⟨σ₁ (Formalism.MainNotions.S.umat g) (v1 : H₁), hS₁ _ hg _ v1.2⟩ with hy
    have h1 := hU _ hg y v1 rfl
    rw [← ex, ← ev, ← h1, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
    show inner ℂ x1 y = inner ℂ x1 (tfClRep σ₁ S₁ (Formalism.MainNotions.S.umat g) v1)
    congr 1
    exact Subtype.ext (tfClRep_coe σ₁ S₁ (hS₁ _ hg) v1).symm
  obtain ⟨-, hint, hval⟩ := hd.1, (hd.2 v1 x1 v1 x1).1, (hd.2 v1 x1 v1 x1).2
  have hnx : ‖x‖ = ‖x1‖ := by rw [← ex]; exact U.norm_map x1
  have hnv : ‖v‖ = ‖v1‖ := by rw [← ev]; exact U.norm_map v1
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have e : ∀ g : Formalism.REAL.UJ ε, ((‖inner ℂ x (σ₂ (Formalism.MainNotions.S.umat g) v)‖ ^ 2 : ℝ) : ℂ) =
      Formalism.MainNotions.S.coefOn (tfClRep σ₁ S₁) v1 x1 g * star (Formalism.MainNotions.S.coefOn (tfClRep σ₁ S₁) v1 x1 g) := by
    intro g
    rw [hcoef, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [e]
  have h1 : inner ℂ v1 v1 = ((‖v1‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have h2 : inner ℂ x1 x1 = ((‖x1‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hval, h1, h2, hnx, hnv]
  push_cast
  ring

end ReciprocityTheory.ChartRestriction.DS
