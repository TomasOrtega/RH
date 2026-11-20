import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Evaluate the numerical expressions.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
