import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

section Liouville

variable {N : ℕ}

/- English proof (translation)
Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn hf.continuous.continuousOn`. Apply `hf.apply_eq_apply_of_bounded` to reduce the goal to its premises. Rewrite using `[isBounded_iff_forall_norm_le]`. Use `⟨C, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨u, rfl⟩`.

Take `⟨v, hv, hvu⟩` from `hcov u`. Establish `h` using `hper v (u - v) hvu`. Establish `e : v + (u - v) = u` using `by abel`. Rewrite `h` using `[e]`. Rewrite using `[h]`.

Conclude with `hC v hv`.
-/
theorem norm_periodic_const (f : (Fin N → ℂ) → ℂ) (hf : Differentiable ℂ f) (L : AddSubgroup (Fin N → ℂ))
    (K : Set (Fin N → ℂ)) (hK : IsCompact K) (hcov : ∀ z, ∃ w ∈ K, z - w ∈ L)
    (hper : ∀ z, ∀ l ∈ L, ‖f (z + l)‖ = ‖f z‖) (z w : Fin N → ℂ) : f z = f w := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuous.continuousOn
  apply hf.apply_eq_apply_of_bounded
  rw [isBounded_iff_forall_norm_le]
  refine ⟨C, ?_⟩
  rintro _ ⟨u, rfl⟩
  obtain ⟨v, hv, hvu⟩ := hcov u
  have h := hper v (u - v) hvu
  have e : v + (u - v) = u := by abel
  rw [e] at h
  rw [h]
  exact hC v hv

/- English proof (translation)
Take `⟨b, hbsub, hbspan, hbli⟩` from `exists_linearIndependent ℝ (Set.range P)`. Rewrite `hbspan` using `[hspan]`. Use `haveI : Finite b := hbli.finite`. Use `haveI : Fintype b := Fintype.ofFinite b`. Establish `hpre : ∀ j : b, ∃ x, P x = (j : Fin N → ℂ)` using `fun j => hbsub j.prop`.

Use `choose a ha using hpre`. Use `⟨(fun c : b → ℝ => ∑ j, c j • (j : Fin N → ℂ)) '' Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(isCompact_univ_pi fun _ => isCompact_Icc).image (continuous_finset_sum _ fun j _ => (continuous_apply j).smul continuous_const)`. Introduce `z`. Set `B` to `Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan]))`.

Establish `hBj : ∀ j, B j = (j : Fin N → ℂ)` using `fun j => by simp [B]`. Establish `hz : ∑ j, B.repr z j • (j : Fin N → ℂ) = z`. Repeatedly rewrite using `[← hBj]`. Conclude with `B.sum_repr z`. Generalize the expression as in `B.repr z = r at hz ⊢`.

Use `⟨∑ j, Int.fract (r j) • (j : Fin N → ℂ), ⟨fun j => Int.fract (r j), fun j _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Use `⟨∑ j, ⌊r j⌋ • a j, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `conv_rhs => rw [← hz]`. Rewrite using `[← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, ha j, ← sub_smul, Int.self_sub_fract, Int.cast_smul_eq_zsmul]`.
-/
theorem exists_compact_reps {La : Type} [AddCommGroup La] (P : La →+ (Fin N → ℂ))
    (hspan : Submodule.span ℝ (Set.range P) = ⊤) :
    ∃ K : Set (Fin N → ℂ), IsCompact K ∧ ∀ z, ∃ w ∈ K, z - w ∈ P.range := by
  classical
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℝ (Set.range P)
  rw [hspan] at hbspan
  haveI : Finite b := hbli.finite
  haveI : Fintype b := Fintype.ofFinite b
  have hpre : ∀ j : b, ∃ x, P x = (j : Fin N → ℂ) := fun j => hbsub j.prop
  choose a ha using hpre
  refine ⟨(fun c : b → ℝ => ∑ j, c j • (j : Fin N → ℂ)) '' Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1),
    ?_, ?_⟩
  · exact (isCompact_univ_pi fun _ => isCompact_Icc).image
      (continuous_finset_sum _ fun j _ => (continuous_apply j).smul continuous_const)
  · intro z
    let B := Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan]))
    have hBj : ∀ j, B j = (j : Fin N → ℂ) := fun j => by simp [B]
    have hz : ∑ j, B.repr z j • (j : Fin N → ℂ) = z := by
      simp_rw [← hBj]
      exact B.sum_repr z
    generalize B.repr z = r at hz ⊢
    refine ⟨∑ j, Int.fract (r j) • (j : Fin N → ℂ),
      ⟨fun j => Int.fract (r j), fun j _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, rfl⟩, ?_⟩
    refine ⟨∑ j, ⌊r j⌋ • a j, ?_⟩
    rw [map_sum]
    conv_rhs => rw [← hz]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, ha j, ← sub_smul, Int.self_sub_fract, Int.cast_smul_eq_zsmul]

/- English proof (translation)
Take `⟨K, hK, hcov⟩` from `exists_compact_reps P hspan`. Use `norm_periodic_const f hf P.range K hK hcov ?_ z w` and prove the remaining obligations. Introduce and unpack `u _ ⟨c, rfl⟩`. Conclude with `hper u c`.
-/
theorem norm_periodic_const_range {La : Type} [AddCommGroup La] (P : La →+ (Fin N → ℂ))
    (hspan : Submodule.span ℝ (Set.range P) = ⊤) (f : (Fin N → ℂ) → ℂ) (hf : Differentiable ℂ f)
    (hper : ∀ z a, ‖f (z + P a)‖ = ‖f z‖) (z w : Fin N → ℂ) : f z = f w := by
  obtain ⟨K, hK, hcov⟩ := exists_compact_reps P hspan
  refine norm_periodic_const f hf P.range K hK hcov ?_ z w
  rintro u _ ⟨c, rfl⟩
  exact hper u c

end Liouville

end ReciprocityTheory.ChartRestriction.G.PullbackSections
