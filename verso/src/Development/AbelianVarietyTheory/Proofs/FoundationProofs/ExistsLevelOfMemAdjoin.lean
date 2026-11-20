import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

noncomputable section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
open Polynomial

namespace GlobalTheory.K5.Level

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

abbrev Bn (T : Tower p Ω) (n : ℕ) : Subalgebra (O0 p) Ω :=
  Algebra.adjoin (O0 p) {T.ζ n, T.qq n}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem bn_le_succ (T : Tower p Ω) (n : ℕ) : Bn T n ≤ Bn T (n + 1) := by
  rw [Algebra.adjoin_le_iff]
  rintro x (rfl | rfl)
  · rw [← T.ζpow n]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) _
  · rw [← T.qpow n]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bn_mono (T : Tower p Ω) : Monotone (Bn T) :=
  monotone_nat_of_le_succ (bn_le_succ T)

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Prove the first alternative. Prove the second alternative.
-/
theorem bn_le_B (T : Tower p Ω) (n : ℕ) :
    Bn T n ≤ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
  apply Algebra.adjoin_mono
  rintro x (rfl | rfl)
  · exact Or.inl ⟨n, rfl⟩
  · exact Or.inr ⟨n, rfl⟩

/- English proof (translation)
Proceed by induction. Treat this case separately. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Supply the required witnesses or components.

Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_mem_bn (T : Tower p Ω) {b : Ω}
    (hb : b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq)) : ∃ n, b ∈ Bn T n := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · exact ⟨n, Algebra.subset_adjoin (by simp)⟩
    · exact ⟨n, Algebra.subset_adjoin (by simp)⟩
  | algebraMap r => exact ⟨0, Subalgebra.algebraMap_mem _ r⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨k, hk⟩ := hy
    exact ⟨max m k, Subalgebra.add_mem _ (bn_mono T (le_max_left m k) hm)
      (bn_mono T (le_max_right m k) hk)⟩
  | mul x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨k, hk⟩ := hy
    exact ⟨max m k, Subalgebra.mul_mem _ (bn_mono T (le_max_left m k) hm)
      (bn_mono T (le_max_right m k) hk)⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Supply the required witnesses or components.
-/
theorem bn_le_range (T : Tower p Ω) (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (h : IsEmb T n ι) :
    Bn T n ≤ ι.range := by
  rw [Algebra.adjoin_le_iff]
  rintro x (rfl | rfl)
  · exact ⟨xn p n, h.1⟩
  · exact ⟨yn p n, h.2⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Proceed by induction. Treat this case separately. Treat this case separately.

Treat this case separately. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem range_le_bn (T : Tower p Ω) (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (h : IsEmb T n ι)
    (w : On p n) : ι w ∈ Bn T n := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hX : ι (Ideal.Quotient.mk (towerIdeal p n) (C X)) ∈ Bn T n := by
    have : ι (xn p n) = T.ζ n := h.1
    simp only [xn] at this
    rw [this]; exact Algebra.subset_adjoin (by simp)
  have hY : ι (Ideal.Quotient.mk (towerIdeal p n) X) ∈ Bn T n := by
    have : ι (yn p n) = T.qq n := h.2
    simp only [yn] at this
    rw [this]; exact Algebra.subset_adjoin (by simp)
  have hC : ∀ a : Polynomial (O0 p), ι (Ideal.Quotient.mk (towerIdeal p n) (C a)) ∈ Bn T n := by
    intro a
    induction a using Polynomial.induction_on with
    | C c =>
      have : (Ideal.Quotient.mk (towerIdeal p n) (C (C c))) = algebraMap (O0 p) (On p n) c := rfl
      rw [this, AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ c
    | add f g hf hg =>
      rw [map_add, map_add, map_add]; exact Subalgebra.add_mem _ hf hg
    | monomial k c _ =>
      simp only [map_mul, map_pow]
      refine Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ hX _)
      have : (Ideal.Quotient.mk (towerIdeal p n) (C (C c))) = algebraMap (O0 p) (On p n) c := rfl
      rw [this, AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ c
  induction P using Polynomial.induction_on with
  | C a => exact hC a
  | add f g hf hg => rw [map_add, map_add]; exact Subalgebra.add_mem _ hf hg
  | monomial k a _ =>
    simp only [map_mul, map_pow]
    exact Subalgebra.mul_mem _ (hC a) (Subalgebra.pow_mem _ hY _)

end GlobalTheory.K5.Level

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components.
-/
theorem GlobalTheory.K5.exists_level_of_mem_adjoin :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
      ∀ (T : Tower p Ω), ∀ b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq),
        ∃ (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (w : On p n), 1 ≤ n ∧ IsEmb T n ι ∧ ι w = b ∧
          ∀ w' : On p n, ι w' ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
  intro p _ Ω _ _ _ T b hb
  obtain ⟨m, hm⟩ := GlobalTheory.K5.Level.exists_mem_bn T hb
  have hm1 : b ∈ GlobalTheory.K5.Level.Bn T (m + 1) := GlobalTheory.K5.Level.bn_le_succ T m hm
  obtain ⟨ι, hι⟩ := GlobalTheory.K5.Basic.exists_isEmb T (m + 1)
  obtain ⟨w, hw⟩ := GlobalTheory.K5.Level.bn_le_range T (m + 1) ι hι hm1
  exact ⟨m + 1, ι, w, Nat.le_add_left 1 m, hι, hw, fun w' =>
    GlobalTheory.K5.Level.bn_le_B T (m + 1) (GlobalTheory.K5.Level.range_le_bn T (m + 1) ι hι w')⟩
