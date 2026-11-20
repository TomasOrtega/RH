import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

/- English proof (translation)
Introduce `V W F _ _ _ _ _ _ k x`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f g a b hf hg ha hb i hi`. Establish `hi' : (i : WithTop ℕ∞) ≤ ∞` using `by exact_mod_cast le_top`. Take `⟨u, hu, hfu⟩` from `(hf.of_le hi').contDiffOn (m := i) le_rfl (by simp)`.

Take `⟨v, hv, hgv⟩` from `(hg.of_le hi').contDiffOn (m := i) le_rfl (by simp)`. Take `⟨s, hs, hso, hxs⟩` from `mem_nhds_iff.1 (Filter.inter_mem hu hv)`. Establish `key` using `norm_iteratedFDerivWithin_clm_apply (n := i) (hfu.mono fun y hy => (hs hy).1) (hgv.mono fun y hy => (hs hy).2) hso.uniqueDiffOn hxs le_rfl`. Simplify using `only [iteratedFDerivWithin_of_isOpen _ hso hxs] at key`. Use `key.trans ?_` and prove the remaining obligations.

Establish `h0` using `ha.nonneg`. Establish `h1` using `hb.nonneg`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun j hj => ?_` and prove the remaining obligations. Establish `hj' : j ≤ i` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)`.

Establish `e1` using `ha j (hj'.trans hi)`. Establish `e2` using `hb (i - j) ((Nat.sub_le _ _).trans hi)`. Use `gcongr`. Use `_ = 2 ^ i * a * b := by`. Rewrite using `[← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]`.

Simplify using the standard rewrite rules. Use `_ ≤ 2 ^ k * a * b := by gcongr`. Evaluate the numerical expressions. Introduce `L g b hg hb i hi`. Establish `hi' : (i : WithTop ℕ∞) ≤ ∞` using `by exact_mod_cast le_top`.

Establish `key` using `L.iteratedFDeriv_comp_left hg (i := i) hi'`. Establish `e : (fun y => L (g y)) = L ∘ g` using `rfl`. Rewrite using `[e, key]`. Conclude with `(L.norm_compContinuousMultilinearMap_le _).trans (mul_le_mul_of_nonneg_left (hb i hi) (norm_nonneg _))`. Introduce `ι s g b hg hb i hi`.

Establish `hi' : (i : WithTop ℕ∞) ≤ ∞` using `by exact_mod_cast le_top`. Establish `key` using `iteratedFDeriv_fun_sum_apply (n := i) (u := s) (f := g) (x := x) (fun j hj => (hg j hj).of_le hi')`. Rewrite using `[key]`. Conclude with `(norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => hb j hj i hi)`.
-/
theorem UpperTheory.V.Lit.Geo.Cs.appSz :
    AppSz := by
  intro V W F _ _ _ _ _ _ k x
  refine ⟨?_, ?_, ?_⟩
  · intro f g a b hf hg ha hb i hi
    have hi' : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    obtain ⟨u, hu, hfu⟩ := (hf.of_le hi').contDiffOn (m := i) le_rfl (by simp)
    obtain ⟨v, hv, hgv⟩ := (hg.of_le hi').contDiffOn (m := i) le_rfl (by simp)
    obtain ⟨s, hs, hso, hxs⟩ := mem_nhds_iff.1 (Filter.inter_mem hu hv)
    have key := norm_iteratedFDerivWithin_clm_apply (n := i)
      (hfu.mono fun y hy => (hs hy).1) (hgv.mono fun y hy => (hs hy).2) hso.uniqueDiffOn hxs le_rfl
    simp only [iteratedFDerivWithin_of_isOpen _ hso hxs] at key
    refine key.trans ?_
    have h0 := ha.nonneg
    have h1 := hb.nonneg
    calc _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * a * b := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
          have e1 := ha j (hj'.trans hi)
          have e2 := hb (i - j) ((Nat.sub_le _ _).trans hi)
          gcongr
      _ = 2 ^ i * a * b := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          simp
      _ ≤ 2 ^ k * a * b := by
          gcongr
          norm_num
  · intro L g b hg hb i hi
    have hi' : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have key := L.iteratedFDeriv_comp_left hg (i := i) hi'
    have e : (fun y => L (g y)) = L ∘ g := rfl
    rw [e, key]
    exact (L.norm_compContinuousMultilinearMap_le _).trans
      (mul_le_mul_of_nonneg_left (hb i hi) (norm_nonneg _))
  · intro ι s g b hg hb i hi
    have hi' : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have key := iteratedFDeriv_fun_sum_apply (n := i) (u := s) (f := g) (x := x)
      (fun j hj => (hg j hj).of_le hi')
    rw [key]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => hb j hj i hi)
