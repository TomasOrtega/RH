import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FLimit

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Separate the alternatives or extract the components of the hypothesis.

Prove the first alternative. Prove the first alternative. Prove the second alternative. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.CA.finE :
    ∀ {n h : ℕ} {B G : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Finite (ResidueField B)] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (D : GDet n B G) (χ : Fin n → G →* (ResidueField B)ˣ), D.IsCont (maximalIdeal B) → D.map (residue B) = GDet.ofChars χ → MultFree χ h → ∀ Z : Set (MonoidAlgebra B G), (∃ s : Finset G, s.card ≤ finBound n h ∧ Submodule.span B ((fun g => D.toQuot Z (MonoidAlgebra.single g 1)) '' (s : Set G)) = ⊤) ∧ Module.Finite B (D.CHQuot Z) ∧ ∀ N : ℕ, ∃ U : OpenNormalSubgroup G, ∀ u ∈ U, D.toQuot Z (MonoidAlgebra.single u 1) - 1 ∈ (maximalIdeal B ^ N) • (⊤ : Submodule B (D.CHQuot Z)) := by
  classical
  intro n h B G _ _ _ _ _ _ _ _ _ _ D χ hc hm hmf Z
  obtain ⟨s, hs, hy, hU⟩ := f_limit (D.CH ∪ Z) (finBound n h) (fun U => by
    obtain ⟨s, hs, hy⟩ := f_level D χ hc hm hmf 1 U
    refine ⟨s, hs, fun y => ?_⟩
    obtain ⟨z, hz, hyz⟩ := hy y
    refine ⟨z, hz, ?_⟩
    refine (TwoSidedIdeal.span_le.2 ?_) hyz
    intro x hx
    apply TwoSidedIdeal.subset_span
    rcases hx with (hx | hx) | hx
    · exact Or.inl (Or.inl (Or.inl hx))
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx)
  have key : ∀ a b : MonoidAlgebra B G, a - b ∈ closureIdeal (maximalIdeal B) (D.CH ∪ Z) →
      D.toQuot Z a = D.toQuot Z b := by
    intro a b hab
    show RingCon.mkₐ B (D.chBar Z).ringCon a = RingCon.mkₐ B (D.chBar Z).ringCon b
    exact Quot.sound ((TwoSidedIdeal.rel_iff _ _ _).2 hab)
  have hspan : Submodule.span B ((fun g => D.toQuot Z (MonoidAlgebra.single g 1)) '' (s : Set G)) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨y, rfl⟩ : ∃ y, D.toQuot Z y = q := ⟨Quot.out q, Quot.out_eq q⟩
    obtain ⟨z, hz, hyz⟩ := hy y
    have himg : (fun g => D.toQuot Z (MonoidAlgebra.single g 1)) '' (s : Set G) =
        (D.toQuot Z).toLinearMap '' ((fun g => MonoidAlgebra.single g 1) '' (s : Set G)) := by
      rw [Set.image_image]
      rfl
    rw [himg, Submodule.span_image]
    exact ⟨z, hz, (key y z hyz).symm⟩
  refine ⟨⟨s, hs, hspan⟩, ⟨⟨s.image (fun g => D.toQuot Z (MonoidAlgebra.single g 1)), by
    rw [Finset.coe_image]
    exact hspan⟩⟩, ?_⟩
  intro N
  obtain ⟨U, hU'⟩ := hU N
  refine ⟨U, fun u hu => ?_⟩
  obtain ⟨z, hz, hz'⟩ := hU' u hu
  have heq : D.toQuot Z (MonoidAlgebra.single u 1) - 1 = D.toQuot Z z := by
    rw [← map_one (D.toQuot Z), ← map_sub]
    exact key _ _ hz'
  rw [heq]
  have hle : (maximalIdeal B ^ N) • (⊤ : Submodule B (MonoidAlgebra B G)) ≤
      ((maximalIdeal B ^ N) • (⊤ : Submodule B (D.CHQuot Z))).comap (D.toQuot Z).toLinearMap := by
    rw [Submodule.smul_le]
    intro r hr m _
    rw [Submodule.mem_comap]
    show D.toQuot Z (r • m) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem_smul hr trivial
  exact hle hz
