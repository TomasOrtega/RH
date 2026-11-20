import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by omega)`. Establish `hr : 1 < Module.rank F E`. Rewrite using `[← Module.finrank_eq_rank, h]`. Evaluate the numerical expressions. Take `⟨s, hs⟩` from `exists_linearIndependent_pair_of_one_lt_rank hr (one_ne_zero (α := E))`.

Set `b` to `basisOfLinearIndependentOfCardEqFinrank hs (by simp [h])`. Establish `hb0 : b 0 = 1` using `by simp [b]`. Establish `hb1 : b 1 = s` using `by simp [b]`. Choose the witnesses or unpack the hypotheses as in `⟨p, q, hpq⟩ : ∃ p q : F, s * s = algebraMap F E p + algebraMap F E q * s := by`. Use `⟨b.repr (s * s) 0, b.repr (s * s) 1, ?_⟩` and prove the remaining obligations.

Use `conv_lhs => rw [← b.sum_repr (s * s), Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one]`. Establish `ht : LinearIndependent F ![(1 : E), s - algebraMap F E (q / 2)]`. Rewrite `hs`, the goal using `[LinearIndependent.pair_iff]`. Introduce `x y hxy`. Use `hs (x - y * (q / 2)) y (by` as an intermediate fact.

Rewrite using `[← hxy]`. Simplify using `only [Algebra.smul_def, map_sub, map_mul]`. Use the proof step `ring)`. Take `⟨h1, rfl⟩` from `this`. Conclude with `⟨by simpa using h1, rfl⟩`.

Establish `hsq : (s - algebraMap F E (q / 2)) * (s - algebraMap F E (q / 2)) = algebraMap F E (p + (q / 2) ^ 2)`. Establish `hq : algebraMap F E q = 2 * algebraMap F E (q / 2)`. Rewrite using `[← map_ofNat (algebraMap F E) 2, ← map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[map_add, map_pow]`. Rewrite `hpq` using `[hq]`. Take the linear combination `hpq`. Use `⟨basisOfLinearIndependentOfCardEqFinrank ht (by simp [h]), p + (q / 2) ^ 2, ?_, by simp, by simpa using hsq⟩` and prove the remaining obligations. Introduce `h0`.

Rewrite `hsq` using `[h0, map_zero, mul_self_eq_zero]`. Conclude with `ht.ne_zero 1 (by simpa using hsq)`.
-/
theorem exists_basis_one_sqrt_of_finrank_two {F E : Type} [Field F] [CharZero F] [Field E]
    [Algebra F E] (h : Module.finrank F E = 2) :
    ∃ (e : Module.Basis (Fin 2) F E) (δ : F), δ ≠ 0 ∧ e 0 = 1 ∧ e 1 * e 1 = algebraMap F E δ := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hr : 1 < Module.rank F E := by
    rw [← Module.finrank_eq_rank, h]; norm_num
  obtain ⟨s, hs⟩ := exists_linearIndependent_pair_of_one_lt_rank hr (one_ne_zero (α := E))
  let b := basisOfLinearIndependentOfCardEqFinrank hs (by simp [h])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = s := by simp [b]
  obtain ⟨p, q, hpq⟩ : ∃ p q : F, s * s = algebraMap F E p + algebraMap F E q * s := by
    refine ⟨b.repr (s * s) 0, b.repr (s * s) 1, ?_⟩
    conv_lhs => rw [← b.sum_repr (s * s), Fin.sum_univ_two, hb0, hb1, Algebra.smul_def,
      Algebra.smul_def, mul_one]
  have ht : LinearIndependent F ![(1 : E), s - algebraMap F E (q / 2)] := by
    rw [LinearIndependent.pair_iff] at hs ⊢
    intro x y hxy
    have := hs (x - y * (q / 2)) y (by
      rw [← hxy]; simp only [Algebra.smul_def, map_sub, map_mul]; ring)
    obtain ⟨h1, rfl⟩ := this
    exact ⟨by simpa using h1, rfl⟩
  have hsq : (s - algebraMap F E (q / 2)) * (s - algebraMap F E (q / 2))
      = algebraMap F E (p + (q / 2) ^ 2) := by
    have hq : algebraMap F E q = 2 * algebraMap F E (q / 2) := by
      rw [← map_ofNat (algebraMap F E) 2, ← map_mul]; congr 1; ring
    rw [map_add, map_pow]
    rw [hq] at hpq
    linear_combination hpq
  refine ⟨basisOfLinearIndependentOfCardEqFinrank ht (by simp [h]), p + (q / 2) ^ 2, ?_,
    by simp, by simpa using hsq⟩
  intro h0
  rw [h0, map_zero, mul_self_eq_zero] at hsq
  exact ht.ne_zero 1 (by simpa using hsq)

/- English proof (translation)
Take `⟨z, hz⟩` from `h`. Set `e'` to `Algebra.TensorProduct.basis L e`. Use `⟨e'.repr z 0, e'.repr z 1, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz, ← GlobalTheory.Published.norm_of_basis_one_sqrt e' (by rw [Algebra.TensorProduct.basis_apply, h0]; rfl) (algebraMap F L δ) (by`. Rewrite using `[Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, h1, ← IsScalarTower.algebraMap_apply]`.

Conclude with `(Algebra.TensorProduct.algebraMap_apply' δ).symm)]`. Use `congr 1`. Use `conv_lhs => rw [← e'.sum_repr z, Fin.sum_univ_two]`.
-/
theorem TNorm.exists_sq_sub {F E : Type} [Field F] [Field E] [Algebra F E]
    (e : Module.Basis (Fin 2) F E) (h0 : e 0 = 1) {δ : F} (h1 : e 1 * e 1 = algebraMap F E δ)
    (L : Type) [Field L] [Algebra F L] {x : F} (h : TNorm F E L x) :
    ∃ a b : L, algebraMap F L x = a ^ 2 - algebraMap F L δ * b ^ 2 := by
  obtain ⟨z, hz⟩ := h
  let e' := Algebra.TensorProduct.basis L e
  refine ⟨e'.repr z 0, e'.repr z 1, ?_⟩
  rw [← hz, ← GlobalTheory.Published.norm_of_basis_one_sqrt e'
    (by rw [Algebra.TensorProduct.basis_apply, h0]; rfl) (algebraMap F L δ)
    (by
      rw [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, h1,
        ← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.algebraMap_apply' δ).symm)]
  congr 1
  conv_lhs => rw [← e'.sum_repr z, Fin.sum_univ_two]

/- English proof (translation)
Introduce `F E _ _ _ _ _ h x hx hloc`. Take `⟨e, δ, hδ, h0, h1⟩` from `exists_basis_one_sqrt_of_finrank_two h`. Take `⟨a, b, hab⟩` from `GlobalTheory.QNorm.hasseNormSt F δ x hδ hx (fun σ => @TNorm.exists_sq_sub F E _ _ _ e h0 δ h1 ℝ _ σ.toAlgebra x (hloc.2 σ.toAlgebra)) (fun v => TNorm.exists_sq_sub e h0 h1 _ (hloc.1 v))`. Conclude with `⟨_, (GlobalTheory.Published.norm_of_basis_one_sqrt e h0 δ h1 a b).trans hab.symm⟩`.
-/
theorem np_of_finrank_two : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → NP F E := by
  intro F E _ _ _ _ _ h x hx hloc
  obtain ⟨e, δ, hδ, h0, h1⟩ := exists_basis_one_sqrt_of_finrank_two h
  obtain ⟨a, b, hab⟩ := GlobalTheory.QNorm.hasseNormSt F δ x hδ hx
    (fun σ => @TNorm.exists_sq_sub F E _ _ _ e h0 δ h1 ℝ _ σ.toAlgebra x (hloc.2 σ.toAlgebra))
    (fun v => TNorm.exists_sq_sub e h0 h1 _ (hloc.1 v))
  exact ⟨_, (GlobalTheory.Published.norm_of_basis_one_sqrt e h0 δ h1 a b).trans hab.symm⟩

end GlobalTheory.CNorm
