import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosurePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraStandardOpenIffPowSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStandardOpenCoordinateRingIffLocalizationCharStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

/- English proof (translation)
Introduce `k _ _ F K _ _ _ _ _ _ d x hx p W _ _ _ _ _ _ _ e I i hi`. Establish `hloc` using `GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul k F K d x hx I i hi p`. Use extensionality with `w`. Rewrite using `[Submodule.restrictScalars_mem, Submodule.mem_comap, LinearMap.restrictScalars_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `hw`. Take `⟨N, hN⟩` from `(hloc _).1 hw`. Establish `hg : (∏ j ∈ I, x i / x j) ^ N ∈ rA k x I` using `Subalgebra.pow_mem _ (Subalgebra.prod_mem _ fun j hj => Algebra.subset_adjoin (s := {y | ∃ i ∈ I, ∃ j, y = x j / x i}) ⟨j, hj, i, rfl⟩) N`. Establish `hfg : (∏ j ∈ I, x i / x j) ^ N * (∏ j ∈ I, x j / x i) ^ N = 1`. Rewrite using `[← mul_pow, ← Finset.prod_mul_distrib, Finset.prod_eq_one, one_pow]`.

Introduce `j _`. Establish `h1` using `hx.pd.ne i`. Establish `h2` using `hx.pd.ne j`. Clear the denominators using the available nonvanishing facts. Establish `hm : (∏ j ∈ I, x j / x i) ^ N • w ∈ ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)`.

Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply, ← algebraMap_smul K, map_smul, map_pow]`. Conclude with `hN`. Use `(Submodule.span (rA k x I) _).smul_mem ⟨_, hg⟩ (Submodule.subset_span hm)` as an intermediate fact. Rewrite `this` using `[Subalgebra.smul_def, smul_smul, hfg, one_smul]`. Then use the resulting hypothesis. Introduce `hw`.

Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem z hz`. Use `(hloc _).2 ⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, one_smul]`. Conclude with `hz`.

Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul r a _ ha`.

Rewrite using `[Subalgebra.smul_def, ← algebraMap_smul K, map_smul]`. Use `((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p p).2.1 _ ha).2.2.2 _ ?_` and prove the remaining obligations. Conclude with `(integralClosure (rA k x I) K).algebraMap_mem r`.
-/
theorem omB_comap_loc : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module F W] [Module k W] [IsScalarTower F K W] [IsScalarTower k F W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K) (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → (omB k K (rB k K x I) p).comap (e.restrictScalars k) = (Submodule.span (rA k x I) ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)).restrictScalars k := by
  intro k _ _ F K _ _ _ _ _ _ d x hx p W _ _ _ _ _ _ _ e I i hi
  have hloc := GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul k F K d x hx I i hi p
  ext w
  rw [Submodule.restrictScalars_mem, Submodule.mem_comap, LinearMap.restrictScalars_apply]
  constructor
  · intro hw
    obtain ⟨N, hN⟩ := (hloc _).1 hw
    have hg : (∏ j ∈ I, x i / x j) ^ N ∈ rA k x I :=
      Subalgebra.pow_mem _ (Subalgebra.prod_mem _ fun j hj =>
        Algebra.subset_adjoin (s := {y | ∃ i ∈ I, ∃ j, y = x j / x i}) ⟨j, hj, i, rfl⟩) N
    have hfg : (∏ j ∈ I, x i / x j) ^ N * (∏ j ∈ I, x j / x i) ^ N = 1 := by
      rw [← mul_pow, ← Finset.prod_mul_distrib, Finset.prod_eq_one, one_pow]
      intro j _
      have h1 := hx.pd.ne i
      have h2 := hx.pd.ne j
      field_simp
    have hm : (∏ j ∈ I, x j / x i) ^ N • w ∈
        ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W) := by
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
        ← algebraMap_smul K, map_smul, map_pow]
      exact hN
    have := (Submodule.span (rA k x I) _).smul_mem ⟨_, hg⟩ (Submodule.subset_span hm)
    rwa [Subalgebra.smul_def, smul_smul, hfg, one_smul] at this
  · intro hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
      refine (hloc _).2 ⟨0, ?_⟩
      rw [pow_zero, one_smul]
      exact hz
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
      rw [Subalgebra.smul_def, ← algebraMap_smul K, map_smul]
      refine ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p p).2.1 _ ha).2.2.2 _ ?_
      exact (integralClosure (rA k x I) K).algebraMap_mem r

end GlobalTheory.PD
