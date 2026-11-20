import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Descent

noncomputable section

open Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

namespace ApproximationSums

variable {n : ℕ} {ε : Fin n → Bool} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  {E : Fin n → Fin n → Module.End ℂ M}

/- English proof (translation)
Conclude with `(Finset.sum_filter_add_sum_filter_not univ (fun b => ε b = ε a) _).symm`.
-/
theorem split_sum (a : Fin n) (x : M) :
    ∑ b, ‖E a b x‖ ^ 2 = ∑ b ∈ univ.filter (fun b => ε b = ε a), ‖E a b x‖ ^ 2 +
      ∑ b ∈ univ.filter (fun b => ε b ≠ ε a), ‖E a b x‖ ^ 2 := by
  exact (Finset.sum_filter_add_sum_filter_not univ (fun b => ε b = ε a) _).symm

/- English proof (translation)
Take `⟨h1, h2, -⟩` from `hSq n ε M E hE hU x`. Rewrite using `[Finset.sum_congr rfl fun a _ => split_sum (ε := ε) (E := E) a x, Finset.sum_add_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_sq_eq (hSq : SqId) (hE : IsGlRep E) (hU : IsInfUnitary ε E) (x : M) :
    ∑ a, ∑ b, ‖E a b x‖ ^ 2 = 2 * (⟪casimirK ε E x, x⟫_ℂ).re - (⟪casimir E x, x⟫_ℂ).re := by
  obtain ⟨h1, h2, -⟩ := hSq n ε M E hE hU x
  rw [Finset.sum_congr rfl fun a _ => split_sum (ε := ε) (E := E) a x, Finset.sum_add_distrib]
  linarith

end ApproximationSums

open ApproximationSums in
/- English proof (translation)
Introduce `hSq n ε M _ _ E hE hU c hc F hF hK η f hf`. Use `haveI := hF`. Establish `hPF : F.starProjection η ∈ F` using `F.starProjection_apply_mem η`. Establish `hbound : ‖η - F.starProjection η‖ ≤ ‖η - f‖`. Rewrite using `[Submodule.starProjection_minimal (U := F) η]`.

Conclude with `ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ (⟨f, hf⟩ : F)`. Use `⟨F.starProjection η, hPF, hbound, ?_⟩` and prove the remaining obligations. Use `set P := F.starProjection η with hPdef`. Use `set u := η - P with hu`. Establish `hKF : ∀ v ∈ F, casimirK ε E v ∈ F`.

Introduce `v hv`. Simplify using `only [casimirK, LinearMap.sum_apply, Module.End.mul_apply]`. Use `F.sum_mem (fun a _ => F.sum_mem (fun b hb => ?_))` and prove the remaining obligations. Establish `hb' : ε b = ε a` using `(Finset.mem_filter.1 hb).2`. Conclude with `hK a b hb'.symm _ (hK b a hb' v hv)`.

Establish `horth : ∀ w ∈ F, ⟪w, u⟫_ℂ = 0` using `fun w hw => by`. Rewrite using `[inner_eq_zero_symm]`. Conclude with `Submodule.starProjection_inner_eq_zero (K := F) η w hw`. Establish `hw : 2 • casimirK ε E P - (c : ℂ) • P ∈ F` using `F.sub_mem (F.nsmul_mem (hKF P hPF) 2) (F.smul_mem _ hPF)`. Establish `hsplit : 2 • casimirK ε E η - (c : ℂ) • η = (2 • casimirK ε E u - (c : ℂ) • u) + (2 • casimirK ε E P - (c : ℂ) • P)`.

Establish `he : η = u + P` using `by simp [hu]`. Use `conv_lhs => rw [he]`. Rewrite using `[map_add, smul_add, smul_add]`. Normalize the expressions using the abelian group laws. Establish `hkey : (∑ a, ∑ b, ‖E a b u‖ ^ 2) = (⟪2 • casimirK ε E η - (c : ℂ) • η, u⟫_ℂ).re`.

Rewrite using `[sum_sq_eq hSq hE hU u, hsplit, inner_add_left, horth _ hw, add_zero, inner_sub_left, two_nsmul, inner_add_left, hc u, Complex.sub_re, Complex.add_re]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hkey]`. Use `le_trans (Complex.re_le_norm _) (le_trans (norm_inner_le_norm _ _) ?_)` and prove the remaining obligations. Use `gcongr`.

Conclude with `le_of_eq (by simp only [two_smul, two_nsmul])`.
-/
theorem approximation_of_square_identity : SqId → Approx := by
  intro hSq n ε M _ _ E hE hU c hc F hF hK η f hf
  haveI := hF
  have hPF : F.starProjection η ∈ F := F.starProjection_apply_mem η
  have hbound : ‖η - F.starProjection η‖ ≤ ‖η - f‖ := by
    rw [Submodule.starProjection_minimal (U := F) η]
    exact ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ (⟨f, hf⟩ : F)
  refine ⟨F.starProjection η, hPF, hbound, ?_⟩
  set P := F.starProjection η with hPdef
  set u := η - P with hu
  have hKF : ∀ v ∈ F, casimirK ε E v ∈ F := by
    intro v hv
    simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply]
    refine F.sum_mem (fun a _ => F.sum_mem (fun b hb => ?_))
    have hb' : ε b = ε a := (Finset.mem_filter.1 hb).2
    exact hK a b hb'.symm _ (hK b a hb' v hv)
  have horth : ∀ w ∈ F, ⟪w, u⟫_ℂ = 0 := fun w hw => by
    rw [inner_eq_zero_symm]
    exact Submodule.starProjection_inner_eq_zero (K := F) η w hw
  have hw : 2 • casimirK ε E P - (c : ℂ) • P ∈ F :=
    F.sub_mem (F.nsmul_mem (hKF P hPF) 2) (F.smul_mem _ hPF)
  have hsplit : 2 • casimirK ε E η - (c : ℂ) • η =
      (2 • casimirK ε E u - (c : ℂ) • u) + (2 • casimirK ε E P - (c : ℂ) • P) := by
    have he : η = u + P := by simp [hu]
    conv_lhs => rw [he]
    rw [map_add, smul_add, smul_add]
    abel
  have hkey : (∑ a, ∑ b, ‖E a b u‖ ^ 2) = (⟪2 • casimirK ε E η - (c : ℂ) • η, u⟫_ℂ).re := by
    rw [sum_sq_eq hSq hE hU u, hsplit, inner_add_left, horth _ hw, add_zero, inner_sub_left,
      two_nsmul, inner_add_left, hc u, Complex.sub_re, Complex.add_re]
    ring
  rw [hkey]
  refine le_trans (Complex.re_le_norm _) (le_trans (norm_inner_le_norm _ _) ?_)
  gcongr
  exact le_of_eq (by simp only [two_smul, two_nsmul])

end PositivityTheory.RgHe3
