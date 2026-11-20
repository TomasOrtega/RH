import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteDimensionalOfOrtho

open NumberField

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.SplitA

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem conjO_mem_hcompl (p : Ideal (𝓞 K)) {s : 𝓞 K} (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    conjO K s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
  have hle : Formalism.HermitianLatticesTheory.hcompl (K := K) p ≤
      (Formalism.HermitianLatticesTheory.hcompl (K := K) p).comap (conjO K).toMonoidHom := by
    unfold Formalism.HermitianLatticesTheory.hcompl
    rw [Submonoid.closure_le]
    rintro s ⟨hs1, hs2⟩
    rw [SetLike.mem_coe, Submonoid.mem_comap]
    apply Submonoid.subset_closure
    refine ⟨hs2 _ rfl, fun t ht => ?_⟩
    have hts : t = s := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [ht]
      exact star_star _
    rw [hts]; exact hs1
  exact hle hs

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem one_mem_locR (p : Ideal (𝓞 K)) : (1 : K) ∈ Formalism.HermitianLatticesTheory.locR (K := K) p :=
  ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem star_mem_locR (p : Ideal (𝓞 K)) {c : K} (hc : c ∈ Formalism.HermitianLatticesTheory.locR (K := K) p) :
    starRingEnd K c ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
  obtain ⟨s, hs, hc⟩ := hc
  refine ⟨conjO K s, conjO_mem_hcompl p hs, ?_⟩
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp hc
  refine Submodule.mem_one.mpr ⟨conjO K r, ?_⟩
  rw [Algebra.smul_def] at hr ⊢
  show starRingEnd K (algebraMap (𝓞 K) K r) = _
  rw [hr, map_mul]
  rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_mem_locR (p : Ideal (𝓞 K)) {c d : K} (hc : c ∈ Formalism.HermitianLatticesTheory.locR (K := K) p)
    (hd : d ∈ Formalism.HermitianLatticesTheory.locR (K := K) p) : c * d ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
  obtain ⟨s, hs, hc⟩ := hc
  obtain ⟨t, ht, hd⟩ := hd
  refine ⟨s * t, Submonoid.mul_mem _ hs ht, ?_⟩
  obtain ⟨r₁, hr₁⟩ := Submodule.mem_one.mp hc
  obtain ⟨r₂, hr₂⟩ := Submodule.mem_one.mp hd
  refine Submodule.mem_one.mpr ⟨r₁ * r₂, ?_⟩
  rw [Algebra.smul_def] at hr₁ hr₂ ⊢
  rw [map_mul, hr₁, hr₂, map_mul]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem mem_dualAt_iff' {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (g : W →ₗ⋆[K] W →ₗ[K] K) (p : Ideal (𝓞 K))
    (M : Submodule (𝓞 K) W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.dualAt g p M ↔ ∀ y ∈ M, g y x ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
  unfold Formalism.HermitianLatticesTheory.dualAt
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]

end Formalism.HermitianLattices.Ext.L3.SplitA
