import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.DualLattices.MemOfSumSingleEqZero

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rh

/- English proof (translation)
Rewrite using `[← Matrix.cramer_transpose_apply, Matrix.diagonal_transpose, Matrix.cramer_eq_adjugate_mulVec, Matrix.adjugate_diagonal, Matrix.mulVec_diagonal]`.
-/
theorem det_updateRow_diagonal {R : Type} [CommRing R] {m : ℕ} (c r : Fin m → R) (i : Fin m) :
    ((Matrix.diagonal c).updateRow i r).det = (∏ j ∈ Finset.univ.erase i, c j) * r i := by
  rw [← Matrix.cramer_transpose_apply, Matrix.diagonal_transpose, Matrix.cramer_eq_adjugate_mulVec,
    Matrix.adjugate_diagonal, Matrix.mulVec_diagonal]

/- English proof (translation)
Introduce `C _ v R _ _ hv ι _ L L' hL x y hx0 hx hy`. Take `⟨m, c, ⟨e⟩, rfl⟩` from `hx`. Take `⟨n, d, ⟨e'⟩, rfl⟩` from `hy`. Use `haveI := isLocal_of_integers hv`. Set `π : ((i : Fin m) → R ⧸ Ideal.span {c i}) →ₗ[R] ((i : Fin n) → R ⧸ Ideal.span {d i})` to `e'.toLinearMap ∘ₗ (Submodule.factor hL) ∘ₗ e.symm.toLinearMap`.

Establish `hπ : Function.Surjective π` using `e'.surjective.comp ((Submodule.factor_surjective hL).comp e.symm.surjective)`. Set `s : Fin m → ((i : Fin m) → R ⧸ Ideal.span {c i})` to `fun i => Pi.single i (1 : R ⧸ Ideal.span {c i})`. Establish `hsp : Submodule.span R (Set.range fun i => π (s i)) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `z _`.

Take `⟨w, rfl⟩` from `hπ z`. Rewrite using `[eq_sum_single c w, map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Establish `hdiag : ∀ k, ∑ i, Matrix.diagonal c k i • π (s i) = 0`. Introduce `k`. Rewrite using `[Finset.sum_eq_single k]`. Rewrite using `[Matrix.diagonal_apply_eq, ← map_smul, single_smul_self c k, map_zero]`. Introduce `i _ hi`.

Rewrite using `[Matrix.diagonal_apply_ne' _ hi, zero_smul]`. Simplify using the standard rewrite rules. Establish `key : ∀ T : Matrix (Fin m) (Fin m) R, (∀ k, ∑ i, T k i • π (s i) = 0) → v (algebraMap R C T.det) ≤ ∏ i, v (algebraMap R C (d i))`. Introduce `T hT`. Establish `h` using `det_mem_span_prod n d m _ hsp T hT`.

Rewrite `h` using `[Ideal.mem_span_singleton]`. Establish `h2` using `hv.le_of_dvd h`. Rewrite `h2` using `[map_prod, map_prod]`. Then use the resulting hypothesis. Use `⟨?_, fun hxy => le_antisymm hL fun l hl => ?_⟩` and prove the remaining obligations. Use `key _ hdiag` as an intermediate fact.

Rewrite `this` using `[Matrix.det_diagonal, map_prod, map_prod]`. Then use the resulting hypothesis. Use `set w := e (Submodule.Quotient.mk l) with hw`. Establish `hπw : π w = 0`. Establish `: (Submodule.Quotient.mk l : (ι → R) ⧸ L') = 0` using `(Submodule.Quotient.mk_eq_zero _).2 hl`. Simplify using `[π, hw, this]`.

Establish `hw0 : w = 0`. Use function extensionality and compare the values at `i`. Establish `hrel : ∑ k, (Quotient.out (w k) : R) • π (s k) = 0`. Rewrite using `[← hπw]`. Use `conv_rhs => rw [eq_sum_single c w, map_sum]`.

Simplify using `only [map_smul, s]`. Establish `h` using `key ((Matrix.diagonal c).updateRow i fun k => (Quotient.out (w k) : R)) (by`. Introduce `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality.

Simplify `hrel` using `only [Matrix.updateRow_self]`. Simplify `hdiag k)` using `only [Matrix.updateRow_ne hk]`. Rewrite `h` using `[det_updateRow_diagonal, ← hxy, map_mul, map_mul, map_prod, map_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]`. Establish `hne : ∏ j ∈ Finset.univ.erase i, v (algebraMap R C (c j)) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => Finset.prod_ne_zero_iff.1 hx0 j (Finset.mem_univ j)`. Establish `h2` using `le_of_mul_le_mul_left h (pos_iff_ne_zero.2 hne)`.

Establish `h3` using `hv.dvd_of_le h2`. Rewrite `h3` using `[← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_out]`. Conclude with `h3`. Establish `: (Submodule.Quotient.mk l : (ι → R) ⧸ L) = 0` using `e.injective (by rw [← hw, hw0, map_zero])`. Conclude with `(Submodule.Quotient.mk_eq_zero _).1 this`.
-/
theorem len_eq : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → ∀ (ι : Type) [Fintype ι] (L L' : Submodule R (ι → R)), L ≤ L' → ∀ x y : NNReal, x ≠ 0 → HasLen v R ((ι → R) ⧸ L) x → HasLen v R ((ι → R) ⧸ L') y → x ≤ y ∧ (x = y → L = L') := by
  intro C _ v R _ _ hv ι _ L L' hL x y hx0 hx hy
  obtain ⟨m, c, ⟨e⟩, rfl⟩ := hx
  obtain ⟨n, d, ⟨e'⟩, rfl⟩ := hy
  haveI := isLocal_of_integers hv
  let π : ((i : Fin m) → R ⧸ Ideal.span {c i}) →ₗ[R] ((i : Fin n) → R ⧸ Ideal.span {d i}) :=
    e'.toLinearMap ∘ₗ (Submodule.factor hL) ∘ₗ e.symm.toLinearMap
  have hπ : Function.Surjective π :=
    e'.surjective.comp ((Submodule.factor_surjective hL).comp e.symm.surjective)
  let s : Fin m → ((i : Fin m) → R ⧸ Ideal.span {c i}) :=
    fun i => Pi.single i (1 : R ⧸ Ideal.span {c i})
  have hsp : Submodule.span R (Set.range fun i => π (s i)) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨w, rfl⟩ := hπ z
    rw [eq_sum_single c w, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hdiag : ∀ k, ∑ i, Matrix.diagonal c k i • π (s i) = 0 := by
    intro k
    rw [Finset.sum_eq_single k]
    · rw [Matrix.diagonal_apply_eq, ← map_smul, single_smul_self c k, map_zero]
    · intro i _ hi
      rw [Matrix.diagonal_apply_ne' _ hi, zero_smul]
    · simp
  have key : ∀ T : Matrix (Fin m) (Fin m) R, (∀ k, ∑ i, T k i • π (s i) = 0) →
      v (algebraMap R C T.det) ≤ ∏ i, v (algebraMap R C (d i)) := by
    intro T hT
    have h := det_mem_span_prod n d m _ hsp T hT
    rw [Ideal.mem_span_singleton] at h
    have h2 := hv.le_of_dvd h
    rwa [map_prod, map_prod] at h2
  refine ⟨?_, fun hxy => le_antisymm hL fun l hl => ?_⟩
  · have := key _ hdiag
    rwa [Matrix.det_diagonal, map_prod, map_prod] at this
  · set w := e (Submodule.Quotient.mk l) with hw
    have hπw : π w = 0 := by
      have : (Submodule.Quotient.mk l : (ι → R) ⧸ L') = 0 := (Submodule.Quotient.mk_eq_zero _).2 hl
      simp [π, hw, this]
    have hw0 : w = 0 := by
      funext i
      have hrel : ∑ k, (Quotient.out (w k) : R) • π (s k) = 0 := by
        rw [← hπw]
        conv_rhs => rw [eq_sum_single c w, map_sum]
        simp only [map_smul, s]
      have h := key ((Matrix.diagonal c).updateRow i fun k => (Quotient.out (w k) : R)) (by
        intro k
        by_cases hk : k = i
        · subst hk
          simpa only [Matrix.updateRow_self] using hrel
        · simpa only [Matrix.updateRow_ne hk] using hdiag k)
      rw [det_updateRow_diagonal, ← hxy, map_mul, map_mul, map_prod, map_prod,
        ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)] at h
      have hne : ∏ j ∈ Finset.univ.erase i, v (algebraMap R C (c j)) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun j _ =>
          Finset.prod_ne_zero_iff.1 hx0 j (Finset.mem_univ j)
      have h2 := le_of_mul_le_mul_left h (pos_iff_ne_zero.2 hne)
      have h3 := hv.dvd_of_le h2
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_out] at h3
      exact h3
    have : (Submodule.Quotient.mk l : (ι → R) ⧸ L) = 0 := e.injective (by rw [← hw, hw0, map_zero])
    exact (Submodule.Quotient.mk_eq_zero _).1 this

end PositivityTheory.HtPt.Rh
