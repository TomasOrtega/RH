import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RankCount

open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up CategoryTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations.

Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.V.ZK.Up.rqFacts : UpperTheory.V.ZK.Up.RqFacts := by
  intro q
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro G _ m z
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single g a =>
      ext i
      simp only [bd, rq, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single,
        Finsupp.linearCombination_single, Finsupp.smul_apply, Finsupp.add_apply,
        Finsupp.finset_sum_apply, Finsupp.mapRange_apply, smul_eq_mul]
      push_cast
      unfold Finsupp.single
      split_ifs <;> simp [Pi.single_apply, apply_ite]
  · intro G H _ _ f m z
    simp only [cm, rq, Finsupp.lmapDomain_apply, Finsupp.mapRange.addMonoidHom_apply]
    exact Finsupp.mapDomain_mapRange _ _ _ _ (fun _ _ => by simp)
  · intro G m y
    refine ⟨Finsupp.mapRange (fun x : ZMod q => (x.cast : ℤ)) (by simp) y, ?_⟩
    ext i
    simp [rq]
  · intro G m z
    constructor
    · intro h
      have hd : ∀ i, (q : ℤ) ∣ z i := by
        intro i
        have := DFunLike.congr_fun h i
        simpa [rq, ZMod.intCast_zmod_eq_zero_iff_dvd] using this
      refine ⟨Finsupp.mapRange (fun x : ℤ => x / q) (by simp) z, ?_⟩
      ext i
      simp [Int.mul_ediv_cancel' (hd i)]
    · rintro ⟨w, rfl⟩
      ext i
      simp [rq]
