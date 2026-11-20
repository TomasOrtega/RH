import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteDimensionalOfOrtho

open NumberField

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.SplitA

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Establish `hle : Formalism.HermitianLatticesTheory.hcompl (K` using `K) p ≤ (Formalism.HermitianLatticesTheory.hcompl (K := K) p).comap (conjO K).toMonoidHom := by`. Unfold `Formalism.HermitianLatticesTheory.hcompl`. Rewrite using `[Submonoid.closure_le]`. Introduce and unpack `s ⟨hs1, hs2⟩`. Rewrite using `[SetLike.mem_coe, Submonoid.mem_comap]`.

Apply `Submonoid.subset_closure` to reduce the goal to its premises. Use `⟨hs2 _ rfl, fun t ht => ?_⟩` and prove the remaining obligations. Establish `hts : t = s`. Apply `FaithfulSMul.algebraMap_injective (𝓞 K) K` to reduce the goal to its premises. Rewrite using `[ht]`.

Conclude with `star_star _`. Rewrite using `[hts]`. Conclude with `hs1`. Conclude with `hle hs`.
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
Assemble the required witnesses or components as `⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩⟩`.
-/
theorem one_mem_locR (p : Ideal (𝓞 K)) : (1 : K) ∈ Formalism.HermitianLatticesTheory.locR (K := K) p :=
  ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩⟩

/- English proof (translation)
Take `⟨s, hs, hc⟩` from `hc`. Use `⟨conjO K s, conjO_mem_hcompl p hs, ?_⟩` and prove the remaining obligations. Take `⟨r, hr⟩` from `Submodule.mem_one.mp hc`. Use `Submodule.mem_one.mpr ⟨conjO K r, ?_⟩` and prove the remaining obligations. Rewrite `hr`, the goal using `[Algebra.smul_def]`.

Use `show starRingEnd K (algebraMap (𝓞 K) K r) = _`. Rewrite using `[hr, map_mul]`. Both sides reduce to the same expression.
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
Take `⟨s, hs, hc⟩` from `hc`. Take `⟨t, ht, hd⟩` from `hd`. Use `⟨s * t, Submonoid.mul_mem _ hs ht, ?_⟩` and prove the remaining obligations. Take `⟨r₁, hr₁⟩` from `Submodule.mem_one.mp hc`. Take `⟨r₂, hr₂⟩` from `Submodule.mem_one.mp hd`.

Use `Submodule.mem_one.mpr ⟨r₁ * r₂, ?_⟩` and prove the remaining obligations. Rewrite `hr₁`, `hr₂`, the goal using `[Algebra.smul_def]`. Rewrite using `[map_mul, hr₁, hr₂, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
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
Unfold `Formalism.HermitianLatticesTheory.dualAt`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]`.
-/
theorem mem_dualAt_iff' {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (g : W →ₗ⋆[K] W →ₗ[K] K) (p : Ideal (𝓞 K))
    (M : Submodule (𝓞 K) W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.dualAt g p M ↔ ∀ y ∈ M, g y x ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
  unfold Formalism.HermitianLatticesTheory.dualAt
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]

end Formalism.HermitianLattices.Ext.L3.SplitA
