import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private lemma kun_lof {k : Type} [Field k] (l : ℕ) [Fact l.Prime] {X : Scheme.{0}} (p : X ⟶ S k)
    (n a : ℤ) (h : a + (n - a) = n) (u : V l X a) (v : V l X (n - a)) :
    kun l p p n (DirectSum.lof ℚ_[l] ℤ (fun i => V l X i ⊗[ℚ_[l]] V l X (n - i)) a (u ⊗ₜ v)) =
      ext2 l p h u v := by
  simp [kun, DirectSum.toModule_lof, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Proceed by induction. Treat this case separately. Treat this case separately. Proceed by induction. Treat this case separately.

Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.KunnethLefschetz.kunL_holds :
    UpperTheory.Gal.KunnethLefschetz.KunL := by
  intro l _ k _ d X p hb
  refine ⟨fun n => ?_, fun lam m n h => ?_⟩
  · rw [eq_top_iff]
    rintro w -
    obtain ⟨x, rfl⟩ := (hb n).2 w
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i t =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul u v =>
        rw [← DirectSum.lof_eq_of ℚ_[l], kun_lof l p n i (by omega) u v]
        exact Submodule.subset_span ⟨i, n - i, by omega, u, v, rfl⟩
      | add s t hs ht =>
        rw [map_add, map_add]
        exact Submodule.add_mem _ hs ht
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  · let e := LinearEquiv.ofBijective (kun l p p n) (hb n)
    have he : ∀ a (ha : a + (n - a) = n) (u : V l X a) (v : V l X (n - a)),
        e.symm (ext2 l p ha u v) = DirectSum.lof ℚ_[l] ℤ (fun i => V l X i ⊗[ℚ_[l]] V l X (n - i)) a (u ⊗ₜ v) := by
      intro a ha u v
      rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply, kun_lof]
    refine ⟨(DirectSum.toModule ℚ_[l] ℤ (V l X m) (fun i =>
        if hi : i = 2 * (d : ℤ) then
          TensorProduct.lift ((LinearMap.lsmul ℚ_[l] (V l X m)).compl₁₂
            (Eq.rec (motive := fun j _ => V l X j →ₗ[ℚ_[l]] ℚ_[l]) lam hi.symm)
            (Eq.rec (motive := fun j _ => V l X j →ₗ[ℚ_[l]] V l X m) LinearMap.id
              (show m = n - i by omega)))
        else 0)) ∘ₗ e.symm.toLinearMap, ?_, ?_⟩
    · intro u v
      obtain rfl : m = n - 2 * (d : ℤ) := by omega
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, he,
        DirectSum.toModule_lof, dif_pos rfl]
      simp [TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.lsmul_apply]
    · intro a b h' hbm u v
      obtain rfl : b = n - a := by omega
      have ha : a ≠ 2 * (d : ℤ) := by omega
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, he,
        DirectSum.toModule_lof, dif_neg ha, LinearMap.zero_apply]
