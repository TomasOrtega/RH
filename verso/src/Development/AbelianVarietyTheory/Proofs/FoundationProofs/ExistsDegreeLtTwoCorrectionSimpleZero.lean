import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DedekindFiniteTypeIdealCodimensionStatement

open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `k A _ _ _ _ _ _ _ _ _ _ n b P₀ w hP`. Use `haveI : Algebra.FiniteType k A := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance`. Take `⟨φ, hφ⟩` from `((GlobalTheory.T.dedekind_finiteType_ideal_codimension k A).2.1 P₀ hP).2`. Use `set α : k := φ (algebraMap k[X] A X) with hα`. Establish `hC : algebraMap k[X] A (C α) = algebraMap k A α`.

Rewrite using `[IsScalarTower.algebraMap_apply k k[X] A]`. Both sides reduce to the same expression. Establish `hlin : algebraMap k[X] A (X - C α) ∈ P₀`. Rewrite using `[hφ, map_sub, map_sub, hC, φ.commutes, ← hα]`. Simplify using the standard rewrite rules.

Establish `hne : algebraMap k[X] A (X - C α) ≠ 0`. Introduce `h0`. Establish `h1 : (X - C α) • (1 : A) = 0` using `by rw [Algebra.smul_def, h0, zero_mul]`. Establish `h3 : b.repr (1 : A) ≠ 0`. Rewrite using `[Ne, LinearEquiv.map_eq_zero_iff]`.

Conclude with `one_ne_zero`. Take `⟨i, hi⟩` from `DFunLike.ne_iff.mp h3`. Establish `h4` using `congrArg (fun a => b.repr a i) h1`. Simplify using `only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h4`. Conclude with `mul_ne_zero (X_sub_C_ne_zero α) hi h4`.

Establish `hbot : P₀ ≠ ⊥` using `fun h => hne (by rw [h] at hlin; simpa using hlin)`. Establish `hlt` using `Ideal.pow_lt_self P₀ hbot hP.ne_top 2 le_rfl`. Take `⟨π, hπP, hπ2⟩` from `SetLike.exists_of_lt hlt`. Use `set q : k[X] := (X - C α) ^ 2 with hq`. Establish `hmon : q.Monic` using `(monic_X_sub_C α).pow 2`.

Establish `hqdeg : q.degree = (2 : ℕ)`. Rewrite using `[hq, degree_pow, degree_X_sub_C]`. Both sides reduce to the same expression. Establish `hqmem : algebraMap k[X] A q ∈ P₀ ^ 2`. Rewrite using `[hq, map_pow]`.

Conclude with `Ideal.pow_mem_pow hlin 2`. Set `c : Fin n → k[X]` to `fun i => b.repr (π - w) i`. Set `p : Fin n → k[X]` to `fun i => c i %ₘ q`. Set `d : Fin n → k[X]` to `fun i => c i /ₘ q`. Establish `hs : ∑ i, c i • b i = π - w` using `b.sum_repr (π - w)`.

Establish `h2 : ∑ i, c i • b i = ∑ i, p i • b i + algebraMap k[X] A q * ∑ i, d i • b i`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Algebra.smul_def, smul_smul, ← add_smul]`. Conclude with `congrArg (· • b i) (modByMonic_add_div (c i) q).symm`.

Establish `key : w + ∑ i, p i • b i = π - algebraMap k[X] A q * ∑ i, d i • b i`. Take the linear combination `hs - h2`. Establish `hM : algebraMap k[X] A q * ∑ i, d i • b i ∈ P₀ ^ 2` using `Ideal.mul_mem_right _ _ hqmem`. Use `⟨p, fun i => ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hqdeg]`.

Conclude with `degree_modByMonic_lt _ hmon`. Rewrite using `[key]`. Conclude with `P₀.sub_mem hπP (Ideal.pow_le_self two_ne_zero hM)`. Introduce `h`. Apply `hπ2` to reduce the goal to its premises.

Establish `: π = (w + ∑ i, p i • b i) + algebraMap k[X] A q * ∑ i, d i • b i`. Rewrite using `[key]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `(P₀ ^ 2).add_mem h hM`.
-/
theorem exists_deg_lt_two_correction_simple :
    ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A]
      [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A]
      [Module.Free k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) (P₀ : Ideal A) (w : A),
      P₀.IsMaximal → ∃ p : Fin n → k[X], (∀ i, (p i).degree < (2 : ℕ)) ∧
        w + ∑ i, p i • b i ∈ P₀ ∧ w + ∑ i, p i • b i ∉ P₀ ^ 2 := by
  intro k A _ _ _ _ _ _ _ _ _ _ n b P₀ w hP
  haveI : Algebra.FiniteType k A := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  obtain ⟨φ, hφ⟩ := ((GlobalTheory.T.dedekind_finiteType_ideal_codimension k A).2.1 P₀ hP).2
  set α : k := φ (algebraMap k[X] A X) with hα
  have hC : algebraMap k[X] A (C α) = algebraMap k A α := by
    rw [IsScalarTower.algebraMap_apply k k[X] A]; rfl
  have hlin : algebraMap k[X] A (X - C α) ∈ P₀ := by
    rw [hφ, map_sub, map_sub, hC, φ.commutes, ← hα]
    simp
  have hne : algebraMap k[X] A (X - C α) ≠ 0 := by
    intro h0
    have h1 : (X - C α) • (1 : A) = 0 := by rw [Algebra.smul_def, h0, zero_mul]
    have h3 : b.repr (1 : A) ≠ 0 := by
      rw [Ne, LinearEquiv.map_eq_zero_iff]; exact one_ne_zero
    obtain ⟨i, hi⟩ := DFunLike.ne_iff.mp h3
    have h4 := congrArg (fun a => b.repr a i) h1
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at h4
    exact mul_ne_zero (X_sub_C_ne_zero α) hi h4
  have hbot : P₀ ≠ ⊥ := fun h => hne (by rw [h] at hlin; simpa using hlin)
  have hlt := Ideal.pow_lt_self P₀ hbot hP.ne_top 2 le_rfl
  obtain ⟨π, hπP, hπ2⟩ := SetLike.exists_of_lt hlt
  set q : k[X] := (X - C α) ^ 2 with hq
  have hmon : q.Monic := (monic_X_sub_C α).pow 2
  have hqdeg : q.degree = (2 : ℕ) := by
    rw [hq, degree_pow, degree_X_sub_C]; rfl
  have hqmem : algebraMap k[X] A q ∈ P₀ ^ 2 := by
    rw [hq, map_pow]; exact Ideal.pow_mem_pow hlin 2
  let c : Fin n → k[X] := fun i => b.repr (π - w) i
  let p : Fin n → k[X] := fun i => c i %ₘ q
  let d : Fin n → k[X] := fun i => c i /ₘ q
  have hs : ∑ i, c i • b i = π - w := b.sum_repr (π - w)
  have h2 : ∑ i, c i • b i = ∑ i, p i • b i + algebraMap k[X] A q * ∑ i, d i • b i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Algebra.smul_def, smul_smul, ← add_smul]
    exact congrArg (· • b i) (modByMonic_add_div (c i) q).symm
  have key : w + ∑ i, p i • b i = π - algebraMap k[X] A q * ∑ i, d i • b i := by
    linear_combination hs - h2
  have hM : algebraMap k[X] A q * ∑ i, d i • b i ∈ P₀ ^ 2 := Ideal.mul_mem_right _ _ hqmem
  refine ⟨p, fun i => ?_, ?_, ?_⟩
  · rw [← hqdeg]; exact degree_modByMonic_lt _ hmon
  · rw [key]; exact P₀.sub_mem hπP (Ideal.pow_le_self two_ne_zero hM)
  · intro h
    apply hπ2
    have : π = (w + ∑ i, p i • b i) + algebraMap k[X] A q * ∑ i, d i • b i := by
      rw [key]; ring
    rw [this]; exact (P₀ ^ 2).add_mem h hM

end GlobalTheory
