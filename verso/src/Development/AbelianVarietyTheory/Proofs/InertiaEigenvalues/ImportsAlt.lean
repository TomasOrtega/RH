import Mathlib

namespace GlobalTheory.TargetStatementAlt

open Polynomial

/- English proof (translation)
Set `f : F →ₐ[R] AlgebraicClosure F` to `IsScalarTower.toAlgHom R F (AlgebraicClosure F)`. Set `φ : Matrix n n F →ₐ[R] Matrix n n (AlgebraicClosure F)` to `f.mapMatrix`. Take `⟨p, hpm, hp⟩` from `hM.map φ`. Establish `key : ∀ μ ∈ (φ M).charpoly.roots, IsIntegral R μ`. Introduce `μ hμ`.

Establish `hroot : IsRoot (φ M).charpoly μ` using `(mem_roots'.mp hμ).2`. Establish `hs : μ ∈ spectrum (AlgebraicClosure F) (φ M)` using `Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot`. Establish `h1` using `spectrum.subset_polynomial_aeval (φ M) (p.map (algebraMap R (AlgebraicClosure F))) ⟨μ, hs, rfl⟩`. Establish `h2 : aeval (φ M) (p.map (algebraMap R (AlgebraicClosure F))) = 0`. Rewrite using `[aeval_map_algebraMap, aeval_def]`.

Conclude with `hp`. Rewrite `h1` using `[h2, spectrum.mem_iff, sub_zero]`. Use `⟨p, hpm, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Apply `h1` to reduce the goal to its premises.

Establish `: eval μ (p.map (algebraMap R (AlgebraicClosure F))) ≠ 0`. Rewrite using `[eval_map_algebraMap, aeval_def]` and apply the resulting hypothesis. Conclude with `(Ne.isUnit this).map _`. Establish `ht : IsIntegral R (Matrix.trace (φ M))`. Rewrite using `[Matrix.trace_eq_sum_roots_charpoly]`.

Conclude with `IsIntegral.multiset_sum key`. Establish `he : Matrix.trace (φ M) = f (Matrix.trace M)`. Simplify using `[φ, Matrix.trace, map_sum, AlgHom.mapMatrix_apply]`. Rewrite `ht` using `[he]`. Conclude with `(isIntegral_algHom_iff f f.toRingHom.injective).mp ht`.
-/
theorem main {R F : Type} [CommRing R] [Field F] [Algebra R F] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n F) (hM : IsIntegral R M) :
    IsIntegral R (Matrix.trace M) := by
  let f : F →ₐ[R] AlgebraicClosure F := IsScalarTower.toAlgHom R F (AlgebraicClosure F)
  let φ : Matrix n n F →ₐ[R] Matrix n n (AlgebraicClosure F) := f.mapMatrix
  obtain ⟨p, hpm, hp⟩ := hM.map φ
  have key : ∀ μ ∈ (φ M).charpoly.roots, IsIntegral R μ := by
    intro μ hμ
    have hroot : IsRoot (φ M).charpoly μ := (mem_roots'.mp hμ).2
    have hs : μ ∈ spectrum (AlgebraicClosure F) (φ M) :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot
    have h1 := spectrum.subset_polynomial_aeval (φ M) (p.map (algebraMap R (AlgebraicClosure F)))
      ⟨μ, hs, rfl⟩
    have h2 : aeval (φ M) (p.map (algebraMap R (AlgebraicClosure F))) = 0 := by
      rw [aeval_map_algebraMap, aeval_def]; exact hp
    rw [h2, spectrum.mem_iff, sub_zero] at h1
    refine ⟨p, hpm, ?_⟩
    by_contra hne
    apply h1
    have : eval μ (p.map (algebraMap R (AlgebraicClosure F))) ≠ 0 := by
      rwa [eval_map_algebraMap, aeval_def]
    exact (Ne.isUnit this).map _
  have ht : IsIntegral R (Matrix.trace (φ M)) := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    exact IsIntegral.multiset_sum key
  have he : Matrix.trace (φ M) = f (Matrix.trace M) := by
    simp [φ, Matrix.trace, map_sum, AlgHom.mapMatrix_apply]
  rw [he] at ht
  exact (isIntegral_algHom_iff f f.toRingHom.injective).mp ht

/- English proof (translation)
Introduce `M h` and use `main M h`.
-/
theorem target : ∀ {R F : Type} [inst : CommRing R] [inst_1 : Field F] [inst_2 : Algebra R F] {n : Type} [inst_3 : Fintype n] [inst_4 : DecidableEq n] (M : Matrix n n F), IsIntegral R M → IsIntegral R (Matrix.trace M) :=
  fun M h => main M h

end GlobalTheory.TargetStatementAlt
