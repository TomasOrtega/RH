import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

/- English proof (translation)
Introduce `l _ k _ _ hl d X p hp hR hLow hKun lam s a hlam Λ hΛ δ`. Establish `hmem : δ ∈ Submodule.span ℚ_[l] {w | ∃ a b, ∃ (h : a + b = 2 * (d : ℤ)), ∃ u v, w = ext2 l p h u v}`. Rewrite using `[hKun.span]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hmem using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨a', b', h', u, v, rfl⟩` from `hx`. Break down `lt_trichotomy b' 0 with hb | hb | hb` into its components or cases. Use `haveI := hLow.neg X b' hb`. Take `rfl : v = 0` from `Subsingleton.elim _ _`.

Use `⟨0, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[ext2]`. Simplify using `[ext2]`. Substitute `hb` using the available equality. Take `rfl : a' = 2 * (d : ℤ)` from `by omega`.

Set `F : V l X (2 * (d : ℤ)) →ₗ[ℚ_[l]] V l (pullback p p) (2 * (d : ℤ))` to `(cupV l (pullback p p) h').flip (pb l (pullback.snd p p) 0 v) ∘ₗ pb l (pullback.fst p p) (2 * (d : ℤ))`. Establish `hsum : ∑ t, ext2 l p (add_zero _ : 2 * (d : ℤ) + 0 = 2 * d) (a t) (a.repr u t • v) = ext2 l p h' u v`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Simplify using `only [ext2, F, map_smul, LinearMap.comp_apply, LinearMap.flip_apply]`.

Use `_ = F (∑ t, a.repr u t • a t) := by`. Rewrite using `[map_sum]`. Simplify using `only [map_smul]`. Use `_ = ext2 l p h' u v := by`. Rewrite using `[a.sum_repr]`.

Both sides reduce to the same expression. Use `⟨fun t => a.repr u t • v, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hΛ.1 u v, ← Finset.sum_smul]`. Use `congr 1`. Use `conv_rhs => rw [← a.sum_repr u]`.

Rewrite using `[map_sum]`. Simplify using `only [map_smul, hlam, smul_eq_mul, mul_one]`. Rewrite using `[hsum, sub_self]`. Conclude with `Submodule.zero_mem _`. Use `⟨0, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [Pi.zero_apply, Finset.sum_const_zero]`. Conclude with `(hΛ.2 a' b' h' (ne_of_gt hb) u v).symm`. Establish `h0 : ∑ t, ext2 l p (add_zero _ : 2 * (d : ℤ) + 0 = 2 * d) (a t) ((0 : Fin s → V l X 0) t) = 0`. Simplify using `[ext2]`. Rewrite using `[h0, sub_zero]`.

Break down `le_or_gt 0 a' with ha | ha` into its components or cases. Conclude with `Submodule.subset_span ⟨a', b', h', u, v, ha, hb, rfl⟩`. Use `haveI := hLow.neg X a' ha`. Take `rfl : u = 0` from `Subsingleton.elim _ _`. Simplify using `[ext2]`.

Consider the case `zero`. Use `⟨0, ?_, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `[ext2]`. Consider the case `add x y _ _ hx hy`.

Take `⟨b1, hb1, hm1⟩` from `hx`. Take `⟨b2, hb2, hm2⟩` from `hy`. Use `⟨b1 + b2, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[Finset.sum_add_distrib, hb1, hb2]`. Use `Submodule.add_mem _ hm1 hm2 using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [ext2, Pi.add_apply, map_add, Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws. Consider the case `smul c x _ hx`. Take `⟨b, hb, hm⟩` from `hx`. Use `⟨c • b, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `[← Finset.smul_sum, hb]`. Use `Submodule.smul_mem _ c hm using 1` and compare the differences between its conclusion and the goal. Simplify using `only [ext2, Pi.smul_apply, map_smul, smul_sub, Finset.smul_sum]`.
-/
theorem topPart_holds : TopPart := by
  intro l _ k _ _ hl d X p hp hR hLow hKun lam s a hlam Λ hΛ δ
  classical
  have hmem : δ ∈ Submodule.span ℚ_[l]
      {w | ∃ a b, ∃ (h : a + b = 2 * (d : ℤ)), ∃ u v, w = ext2 l p h u v} := by
    rw [hKun.span]
    trivial
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a', b', h', u, v, rfl⟩ := hx
    rcases lt_trichotomy b' 0 with hb | hb | hb
    · haveI := hLow.neg X b' hb
      obtain rfl : v = 0 := Subsingleton.elim _ _
      refine ⟨0, ?_, ?_⟩
      · simp [ext2]
      · simp [ext2]
    · subst hb
      obtain rfl : a' = 2 * (d : ℤ) := by omega
      let F : V l X (2 * (d : ℤ)) →ₗ[ℚ_[l]] V l (pullback p p) (2 * (d : ℤ)) :=
        (cupV l (pullback p p) h').flip (pb l (pullback.snd p p) 0 v) ∘ₗ
          pb l (pullback.fst p p) (2 * (d : ℤ))
      have hsum : ∑ t, ext2 l p (add_zero _ : 2 * (d : ℤ) + 0 = 2 * d) (a t) (a.repr u t • v) =
          ext2 l p h' u v := by
        calc ∑ t, ext2 l p (add_zero _ : 2 * (d : ℤ) + 0 = 2 * d) (a t) (a.repr u t • v)
            = ∑ t, a.repr u t • F (a t) := by
              refine Finset.sum_congr rfl fun t _ => ?_
              simp only [ext2, F, map_smul, LinearMap.comp_apply, LinearMap.flip_apply]
          _ = F (∑ t, a.repr u t • a t) := by
              rw [map_sum]
              simp only [map_smul]
          _ = ext2 l p h' u v := by
              rw [a.sum_repr]
              rfl
      refine ⟨fun t => a.repr u t • v, ?_, ?_⟩
      · rw [hΛ.1 u v, ← Finset.sum_smul]
        congr 1
        conv_rhs => rw [← a.sum_repr u]
        rw [map_sum]
        simp only [map_smul, hlam, smul_eq_mul, mul_one]
      · rw [hsum, sub_self]
        exact Submodule.zero_mem _
    · refine ⟨0, ?_, ?_⟩
      · simp only [Pi.zero_apply, Finset.sum_const_zero]
        exact (hΛ.2 a' b' h' (ne_of_gt hb) u v).symm
      · have h0 : ∑ t, ext2 l p (add_zero _ : 2 * (d : ℤ) + 0 = 2 * d) (a t) ((0 : Fin s → V l X 0) t) = 0 := by
          simp [ext2]
        rw [h0, sub_zero]
        rcases le_or_gt 0 a' with ha | ha
        · exact Submodule.subset_span ⟨a', b', h', u, v, ha, hb, rfl⟩
        · haveI := hLow.neg X a' ha
          obtain rfl : u = 0 := Subsingleton.elim _ _
          simp [ext2]
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp [ext2]
  | add x y _ _ hx hy =>
    obtain ⟨b1, hb1, hm1⟩ := hx
    obtain ⟨b2, hb2, hm2⟩ := hy
    refine ⟨b1 + b2, ?_, ?_⟩
    · simp [Finset.sum_add_distrib, hb1, hb2]
    · convert Submodule.add_mem _ hm1 hm2 using 1
      simp only [ext2, Pi.add_apply, map_add, Finset.sum_add_distrib]
      abel
  | smul c x _ hx =>
    obtain ⟨b, hb, hm⟩ := hx
    refine ⟨c • b, ?_, ?_⟩
    · simp [← Finset.smul_sum, hb]
    · convert Submodule.smul_mem _ c hm using 1
      simp only [ext2, Pi.smul_apply, map_smul, smul_sub, Finset.smul_sum]

end UpperTheory.Gal.KunnethLefschetz
