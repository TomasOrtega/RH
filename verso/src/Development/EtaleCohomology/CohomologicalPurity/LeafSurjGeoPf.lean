import Development.EtaleCohomology.CohomologicalPurity.LeafExcSheafCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Apply the first step, then apply the next step to every resulting obligation. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Split into cases according to the possible forms of the given data. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem LeafSurjGeo_of : LeafSurjGeo := by
  intro X' X Z f _ ι' ι _ hp U hU T t
  let F : Bool → Scheme.{0} := fun b => Bool.rec (pullback t f) (t ⁻¹ᵁ U).toScheme b
  let m : ∀ b, F b ⟶ T := fun b => Bool.rec (pullback.fst t f) (t ⁻¹ᵁ U).ι b
  have hR : Presieve.ofArrows F m ∈ Scheme.precoverage @Etale T := by
    refine (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr ⟨fun x => ?_, fun b => ?_⟩
    · by_cases hx : t.base x ∈ (U : Set X)
      · refine ⟨true, ?_⟩
        show x ∈ Set.range (t ⁻¹ᵁ U).ι.base
        rw [Scheme.Opens.range_ι]; exact hx
      · rw [hU, Set.notMem_compl_iff] at hx
        obtain ⟨z, hz⟩ := hx
        have hw : f.base (ι'.base z) = ι.base z := by
          rw [← Scheme.Hom.comp_apply, hp.w]; simp
        obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := t) (g := f) x (ι'.base z)
          (by rw [hw, hz])
        exact ⟨false, p, hp1⟩
    · cases b <;> dsimp [m] <;> infer_instance
  refine ⟨Sieve.generate (Presieve.ofArrows F m),
    Precoverage.generate_mem_toGrothendieck hR, ?_⟩
  intro V g hg
  obtain ⟨W, h, k, hk, rfl⟩ := hg
  obtain ⟨b⟩ := hk
  cases b
  · right
    refine ⟨h ≫ pullback.snd t f, ?_⟩
    simp only [m, Category.assoc, ← pullback.condition]
  · left
    refine ⟨h ≫ (t ∣_ U), ?_⟩
    simp only [m, Category.assoc, morphismRestrict_ι]

end LateralTheory.CohomologicalPurity
