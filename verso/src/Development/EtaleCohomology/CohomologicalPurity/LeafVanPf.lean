import Development.EtaleCohomology.CohomologicalPurity.LeafClCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.Cl

/- English proof (translation)
Use `P.cl` as an intermediate fact. Establish `hsupp : (P.ι.ker.support : Set P.X) = Set.range P.ι`. Rewrite using `[Scheme.Hom.support_ker, P.ι.isClosedEmbedding.isClosed_range.closure_eq]`. Use extensionality with `y`. Establish `hmem : V.2.fromSpec y ∈ V.1`.

Rewrite using `[← SetLike.mem_coe, ← V.2.range_fromSpec]`. Conclude with `Set.mem_range_self y`. Establish `h1` using `Set.ext_iff.mp (V.2.fromSpec_preimage_zeroLocus ((P.ι.ker.ideal V : Ideal Γ(P.X, V.1)) : Set Γ(P.X, V.1))) y`. Establish `h2` using `Scheme.IdealSheafData.mem_support_iff_of_mem (I := P.ι.ker) hmem`. Establish `h3 : V.2.fromSpec y ∈ (P.U : Set P.X) ↔ V.2.fromSpec y ∉ Set.range P.ι` using `by rw [P.hU]; rfl`.

Establish `h4 : V.2.fromSpec y ∈ P.ι.ker.support ↔ V.2.fromSpec y ∈ Set.range P.ι`. Rewrite using `[← SetLike.mem_coe, hsupp]`. Conclude with `(not_congr (h1.symm.trans (h2.symm.trans h4))).trans h3.symm`.
-/
theorem van_preimage {d : ℕ} (P : SP d) (V : P.X.affineOpens) :
    off Γ(P.X, V.1) (P.ι.ker.ideal V) = V.2.fromSpec ⁻¹ᵁ P.U := by
  have := P.cl
  have hsupp : (P.ι.ker.support : Set P.X) = Set.range P.ι := by
    rw [Scheme.Hom.support_ker, P.ι.isClosedEmbedding.isClosed_range.closure_eq]
  ext y
  have hmem : V.2.fromSpec y ∈ V.1 := by
    rw [← SetLike.mem_coe, ← V.2.range_fromSpec]; exact Set.mem_range_self y
  have h1 := Set.ext_iff.mp (V.2.fromSpec_preimage_zeroLocus ((P.ι.ker.ideal V : Ideal Γ(P.X, V.1)) : Set Γ(P.X, V.1))) y
  have h2 := Scheme.IdealSheafData.mem_support_iff_of_mem (I := P.ι.ker) hmem
  have h3 : V.2.fromSpec y ∈ (P.U : Set P.X) ↔ V.2.fromSpec y ∉ Set.range P.ι := by rw [P.hU]; rfl
  have h4 : V.2.fromSpec y ∈ P.ι.ker.support ↔ V.2.fromSpec y ∈ Set.range P.ι := by
    rw [← SetLike.mem_coe, hsupp]
  exact (not_congr (h1.symm.trans (h2.symm.trans h4))).trans h3.symm

/- English proof (translation)
Introduce `hH d q _ P hq i x W hxW`. Take `⟨V, hxV, hVW, -, hch⟩` from `hC d P x W hxW`. Establish `hqV : IsUnit (q : Γ(P.X, V.1))`. Use `hq.map (P.X.presheaf.map (homOfLE le_top : V.1 ⟶ ⊤).op).hom` as an intermediate fact. Simplify using `using this`.

Use `⟨⟨Spec (CommRingCat.of Γ(P.X, V.1)), V.2.fromSpec, V.2.isOpenImmersion_fromSpec, off Γ(P.X, V.1) (P.ι.ker.ideal V), van_preimage P V⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[V.2.range_fromSpec]`. Conclude with `hxV`. Rewrite using `[V.2.range_fromSpec]`. Conclude with `hVW`.

Introduce `n hn`. Conclude with `hR hH d q Γ(P.X, V.1) _ hch hqV n i hn`.
-/
theorem LeafVan_of (hC : LeafChart) (hR : LeafVanRing) : LeafVan := by
  intro hH d q _ P hq i x W hxW
  obtain ⟨V, hxV, hVW, -, hch⟩ := hC d P x W hxW
  have hqV : IsUnit (q : Γ(P.X, V.1)) := by
    have := hq.map (P.X.presheaf.map (homOfLE le_top : V.1 ⟶ ⊤).op).hom
    simpa using this
  refine ⟨⟨Spec (CommRingCat.of Γ(P.X, V.1)), V.2.fromSpec, V.2.isOpenImmersion_fromSpec, off Γ(P.X, V.1) (P.ι.ker.ideal V),
    van_preimage P V⟩, ?_, ?_, ?_⟩
  · rw [V.2.range_fromSpec]; exact hxV
  · rw [V.2.range_fromSpec]; exact hVW
  · intro n hn
    exact hR hH d q Γ(P.X, V.1) _ hch hqV n i hn

end LateralTheory.CohomologicalPurity.Cl
