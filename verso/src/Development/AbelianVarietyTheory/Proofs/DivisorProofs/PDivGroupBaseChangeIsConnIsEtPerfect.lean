import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqZeroOfForallLTensorEqZero

set_option autoImplicit false

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b a`. Establish `hc : Coalgebra.counit (R` using `k') (b ⊗ₜ[k] a : (G.baseChange k').A n) = b * algebraMap k k' (Coalgebra.counit (R := k) a) := by`. Simplify using `[Algebra.smul_def, mul_comm]`.

Establish `ha : a - algebraMap k (G.A n) (Coalgebra.counit (R` using `k) a) ∈ augIdeal k (G.A n) := by`. Simplify using `[RingHom.mem_ker]`. Establish `he : (b ⊗ₜ[k] a : k' ⊗[k] G.A n) - algebraMap k' (k' ⊗[k] G.A n) (b * algebraMap k k' (Coalgebra.counit (R` using `k) a)) = (b ⊗ₜ[k] (1 : G.A n)) * Algebra.TensorProduct.includeRight (a - algebraMap k (G.A n) (Coalgebra.counit (R := k) a)) := by`. Rewrite using `[map_sub, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply, mul_sub, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`. Use `congr 1`.

Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one (A := G.A n), one_mul, tmul_smul, smul_tmul', Algebra.algebraMap_self, RingHom.id_apply, Algebra.smul_def, mul_comm]`. Rewrite using `[hc]`. Conclude with `he ▸ Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ha)`. Consider the case `add x y hx hy`. Establish `: x + y - algebraMap k' ((G.baseChange k').A n) (Coalgebra.counit (R` using `k') (x + y)) = (x - algebraMap k' _ (Coalgebra.counit (R := k') x)) + (y - algebraMap k' _ (Coalgebra.counit (R := k') y)) := by`.

Rewrite using `[map_add, map_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `add_mem hx hy`.
-/
theorem baseChange_sub_counit_mem (p : ℕ) (k k' : Type) [Field k] [Field k'] [Algebra k k']
    (G : PDivGroup p k) (n : ℕ) (x : (G.baseChange k').A n) :
    x - algebraMap k' _ (Coalgebra.counit (R := k') x) ∈
      Ideal.map (Algebra.TensorProduct.includeRight : G.A n →ₐ[k] k' ⊗[k] G.A n)
        (augIdeal k (G.A n)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b a =>
    have hc : Coalgebra.counit (R := k') (b ⊗ₜ[k] a : (G.baseChange k').A n) =
        b * algebraMap k k' (Coalgebra.counit (R := k) a) := by
      simp [Algebra.smul_def, mul_comm]
    have ha : a - algebraMap k (G.A n) (Coalgebra.counit (R := k) a) ∈ augIdeal k (G.A n) := by
      simp [RingHom.mem_ker]
    have he : (b ⊗ₜ[k] a : k' ⊗[k] G.A n) - algebraMap k' (k' ⊗[k] G.A n)
        (b * algebraMap k k' (Coalgebra.counit (R := k) a)) =
        (b ⊗ₜ[k] (1 : G.A n)) * Algebra.TensorProduct.includeRight
          (a - algebraMap k (G.A n) (Coalgebra.counit (R := k) a)) := by
      rw [map_sub, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply,
        mul_sub, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        mul_one]
      congr 1
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one (A := G.A n),
        one_mul, tmul_smul, smul_tmul', Algebra.algebraMap_self, RingHom.id_apply, Algebra.smul_def,
        mul_comm]
    rw [hc]
    exact he ▸ Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ha)
  | add x y hx hy =>
    have : x + y - algebraMap k' ((G.baseChange k').A n) (Coalgebra.counit (R := k') (x + y)) =
        (x - algebraMap k' _ (Coalgebra.counit (R := k') x)) +
          (y - algebraMap k' _ (Coalgebra.counit (R := k') y)) := by
      rw [map_add, map_add]; abel
    rw [this]
    exact add_mem hx hy

/- English proof (translation)
Introduce `p _ k k' _ _ _ _ _ _ _ G`. Use `⟨fun hG n x hx => ?_, fun hG n => ?_⟩` and prove the remaining obligations. Establish `h0 : Coalgebra.counit (R` using `k') x = 0 := hx`. Establish `hmem` using `baseChange_sub_counit_mem p k k' G n x`. Rewrite `hmem` using `[h0, map_zero, sub_zero]`.

Establish `hle : Ideal.map (Algebra.TensorProduct.includeRight : G.A n →ₐ[k] k' ⊗[k] G.A n) (augIdeal k (G.A n)) ≤ nilradical (k' ⊗[k] G.A n)`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Conclude with `(hG n a ha).map _`. Conclude with `hle hmem`.

Use `haveI : PerfectField k := PerfectRing.toPerfectField k p haveI : IsReduced (G.A n) := hG n`. Conclude with `GlobalTheory.ReducedAlg.isReduced_field_tensor k' (G.A n)`.
-/
theorem baseChange_isConn_isEt : ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p] [Algebra k k'] (G : PDivGroup p k), (G.IsConn → (G.baseChange k').IsConn) ∧ (G.IsEt → (G.baseChange k').IsEt) := by
  intro p _ k k' _ _ _ _ _ _ _ G
  refine ⟨fun hG n x hx => ?_, fun hG n => ?_⟩
  · have h0 : Coalgebra.counit (R := k') x = 0 := hx
    have hmem := baseChange_sub_counit_mem p k k' G n x
    rw [h0, map_zero, sub_zero] at hmem
    have hle : Ideal.map (Algebra.TensorProduct.includeRight : G.A n →ₐ[k] k' ⊗[k] G.A n)
        (augIdeal k (G.A n)) ≤ nilradical (k' ⊗[k] G.A n) := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact (hG n a ha).map _
    exact hle hmem
  · haveI : PerfectField k := PerfectRing.toPerfectField k p
    haveI : IsReduced (G.A n) := hG n
    exact GlobalTheory.ReducedAlg.isReduced_field_tensor k' (G.A n)

end GlobalTheory.Dieu
