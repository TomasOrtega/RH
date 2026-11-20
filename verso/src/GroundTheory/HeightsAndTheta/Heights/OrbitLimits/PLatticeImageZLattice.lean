import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLatticeImageZLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.mixedEmbedding

/- English proof (translation)
Take `⟨S, hS⟩` from `hfg`. Establish `halg : ∀ s : F, ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ (y • s)` using `fun s => ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic s)).exists_integral_multiple`. Use `choose y hy0 hyint using halg`. Use `⟨∏ s ∈ S, y s, Finset.prod_ne_zero_iff.mpr fun s _ => hy0 s, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Rewrite `hx` using `[← hS]`. Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem s hs`. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem y hs`. Rewrite using `[hc, mul_comm, mul_smul]`.

Conclude with `(hyint s).zsmul c`. Consider the case `zero => simpa using isIntegral_zero`. Consider the case `add a b _ _ ha hb => simpa [smul_add] using ha.add hb`. Consider the case `neg a _ ha => simpa [smul_neg] using ha.neg`.
-/
theorem LatticeImageZLattice.exists_int_mul_integral {F : Type} [Field F] [NumberField F]
    (L : AddSubgroup F) (hfg : L.FG) : ∃ N : ℤ, N ≠ 0 ∧ ∀ x ∈ L, IsIntegral ℤ (N • x) := by
  obtain ⟨S, hS⟩ := hfg
  have halg : ∀ s : F, ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ (y • s) := fun s =>
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic s)).exists_integral_multiple
  choose y hy0 hyint using halg
  refine ⟨∏ s ∈ S, y s, Finset.prod_ne_zero_iff.mpr fun s _ => hy0 s, ?_⟩
  intro x hx
  rw [← hS] at hx
  induction hx using AddSubgroup.closure_induction with
  | mem s hs =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem y hs
    rw [hc, mul_comm, mul_smul]
    exact (hyint s).zsmul c
  | zero => simpa using isIntegral_zero
  | add a b _ _ ha hb => simpa [smul_add] using ha.add hb
  | neg a _ ha => simpa [smul_neg] using ha.neg

open scoped Classical in

/- English proof (translation)
Introduce `F _ _ L hfg hfull`. Take `⟨N, hN0, hLint⟩` from `LatticeImageZLattice.exists_int_mul_integral L hfg`. Set `e : mixedSpace F →ₗ[ℝ] mixedSpace F` to `(N : ℝ) • LinearMap.id`. Establish `he₁ : Continuous e` using `continuous_const_smul (N : ℝ)`. Establish `he₂ : Function.Injective e` using `fun a b h => smul_right_injective (mixedSpace F) (Int.cast_ne_zero.mpr hN0 : (N : ℝ) ≠ 0) h`.

Establish `hdisc : DiscreteTopology (ZLattice.comap ℝ (mixedEmbedding.integerLattice F) e)` using `ZLattice.comap_discreteTopology ℝ _ he₁ he₂`. Establish `hle : (latticeImage F L : Set (mixedSpace F)) ⊆ ZLattice.comap ℝ (mixedEmbedding.integerLattice F) e`. Introduce `z hz`. Take `⟨x, hx, rfl⟩` from `(mem_latticeImage L z).mp hz`. Use `show e (mixedEmbedding F x) ∈ mixedEmbedding.integerLattice F`.

Use `⟨⟨N • x, hLint x hx⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mixedEmbedding F (N • x) = (N : ℝ) • mixedEmbedding F x`. Rewrite using `[map_zsmul, Int.cast_smul_eq_zsmul]`. Establish `: DiscreteTopology (latticeImage F L)` using `DiscreteTopology.of_subset hdisc hle`. Use `⟨this, ⟨?_⟩⟩` and prove the remaining obligations.

Rewrite using `[eq_top_iff, ← (latticeBasis F).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨n, hn, hnL⟩` from `hfull (integralBasis F i)`. Establish `hmem : mixedEmbedding F ((n : F) * integralBasis F i) ∈ latticeImage F L` using `(mem_latticeImage L _).mpr ⟨_, hnL, rfl⟩`. Establish `hb : latticeBasis F i = (n : ℝ)⁻¹ • mixedEmbedding F ((n : F) * integralBasis F i)`.

Rewrite using `[map_mul, map_natCast, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), one_smul, latticeBasis_apply]`. Rewrite using `[hb]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`.
-/
theorem LatticeImageZLattice.proof : LatticeImageZLattice.Statement := by
  intro F _ _ L hfg hfull
  obtain ⟨N, hN0, hLint⟩ := LatticeImageZLattice.exists_int_mul_integral L hfg

  let e : mixedSpace F →ₗ[ℝ] mixedSpace F := (N : ℝ) • LinearMap.id
  have he₁ : Continuous e := continuous_const_smul (N : ℝ)
  have he₂ : Function.Injective e := fun a b h =>
    smul_right_injective (mixedSpace F) (Int.cast_ne_zero.mpr hN0 : (N : ℝ) ≠ 0) h
  have hdisc : DiscreteTopology (ZLattice.comap ℝ (mixedEmbedding.integerLattice F) e) :=
    ZLattice.comap_discreteTopology ℝ _ he₁ he₂
  have hle : (latticeImage F L : Set (mixedSpace F)) ⊆
      ZLattice.comap ℝ (mixedEmbedding.integerLattice F) e := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (mem_latticeImage L z).mp hz
    show e (mixedEmbedding F x) ∈ mixedEmbedding.integerLattice F
    refine ⟨⟨N • x, hLint x hx⟩, ?_⟩
    change mixedEmbedding F (N • x) = (N : ℝ) • mixedEmbedding F x
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  have : DiscreteTopology (latticeImage F L) := DiscreteTopology.of_subset hdisc hle
  refine ⟨this, ⟨?_⟩⟩

  rw [eq_top_iff, ← (latticeBasis F).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨n, hn, hnL⟩ := hfull (integralBasis F i)
  have hmem : mixedEmbedding F ((n : F) * integralBasis F i) ∈ latticeImage F L :=
    (mem_latticeImage L _).mpr ⟨_, hnL, rfl⟩
  have hb : latticeBasis F i = (n : ℝ)⁻¹ • mixedEmbedding F ((n : F) * integralBasis F i) := by
    rw [map_mul, map_natCast, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), one_smul, latticeBasis_apply]
  rw [hb]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GroundTheory.Heights₂.Heights.Targets
