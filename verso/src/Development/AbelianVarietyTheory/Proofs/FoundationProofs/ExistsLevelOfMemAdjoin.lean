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
Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `x (rfl | rfl)`. Rewrite using `[← T.ζpow n]`. Conclude with `Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) _`. Rewrite using `[← T.qpow n]`.

Conclude with `Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) _`.
-/
theorem bn_le_succ (T : Tower p Ω) (n : ℕ) : Bn T n ≤ Bn T (n + 1) := by
  rw [Algebra.adjoin_le_iff]
  rintro x (rfl | rfl)
  · rw [← T.ζpow n]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) _
  · rw [← T.qpow n]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) _

/- English proof (translation)
The claim follows from `monotone_nat_of_le_succ (bn_le_succ T)`.
-/
theorem bn_mono (T : Tower p Ω) : Monotone (Bn T) :=
  monotone_nat_of_le_succ (bn_le_succ T)

/- English proof (translation)
Apply `Algebra.adjoin_mono` to reduce the goal to its premises. Introduce and unpack `x (rfl | rfl)`. Conclude with `Or.inl ⟨n, rfl⟩`. Conclude with `Or.inr ⟨n, rfl⟩`.
-/
theorem bn_le_B (T : Tower p Ω) (n : ℕ) :
    Bn T n ≤ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
  apply Algebra.adjoin_mono
  rintro x (rfl | rfl)
  · exact Or.inl ⟨n, rfl⟩
  · exact Or.inr ⟨n, rfl⟩

/- English proof (translation)
Proceed by induction on `hb using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨n, rfl⟩ | ⟨n, rfl⟩` into its components or cases. Conclude with `⟨n, Algebra.subset_adjoin (by simp)⟩`. Conclude with `⟨n, Algebra.subset_adjoin (by simp)⟩`.

Consider the case `algebraMap r => exact ⟨0, Subalgebra.algebraMap_mem _ r⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨m, hm⟩` from `hx`. Take `⟨k, hk⟩` from `hy`. Conclude with `⟨max m k, Subalgebra.add_mem _ (bn_mono T (le_max_left m k) hm) (bn_mono T (le_max_right m k) hk)⟩`.

Consider the case `mul x y _ _ hx hy`. Take `⟨m, hm⟩` from `hx`. Take `⟨k, hk⟩` from `hy`. Conclude with `⟨max m k, Subalgebra.mul_mem _ (bn_mono T (le_max_left m k) hm) (bn_mono T (le_max_right m k) hk)⟩`.
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
Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `x (rfl | rfl)`. Conclude with `⟨xn p n, h.1⟩`. Conclude with `⟨yn p n, h.2⟩`.
-/
theorem bn_le_range (T : Tower p Ω) (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (h : IsEmb T n ι) :
    Bn T n ≤ ι.range := by
  rw [Algebra.adjoin_le_iff]
  rintro x (rfl | rfl)
  · exact ⟨xn p n, h.1⟩
  · exact ⟨yn p n, h.2⟩

/- English proof (translation)
Take `⟨P, rfl⟩` from `Ideal.Quotient.mk_surjective w`. Establish `hX : ι (Ideal.Quotient.mk (towerIdeal p n) (C X)) ∈ Bn T n`. Establish `: ι (xn p n) = T.ζ n` using `h.1`. Simplify using `only [xn] at this`. Rewrite using `[this]; exact Algebra.subset_adjoin (by simp)`.

Establish `hY : ι (Ideal.Quotient.mk (towerIdeal p n) X) ∈ Bn T n`. Establish `: ι (yn p n) = T.qq n` using `h.2`. Simplify using `only [yn] at this`. Rewrite using `[this]; exact Algebra.subset_adjoin (by simp)`. Establish `hC : ∀ a : Polynomial (O0 p), ι (Ideal.Quotient.mk (towerIdeal p n) (C a)) ∈ Bn T n`.

Introduce `a`. Proceed by induction on `a using Polynomial.induction_on with`. Consider the case `C c`. Establish `: (Ideal.Quotient.mk (towerIdeal p n) (C (C c))) = algebraMap (O0 p) (On p n) c` using `rfl`. Rewrite using `[this, AlgHom.commutes]`.

Conclude with `Subalgebra.algebraMap_mem _ c`. Consider the case `add f g hf hg`. Rewrite using `[map_add, map_add, map_add]`. Conclude with `Subalgebra.add_mem _ hf hg`. Consider the case `monomial k c _`.

Simplify using `only [map_mul, map_pow]`. Use `Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ hX _)` and prove the remaining obligations. Establish `: (Ideal.Quotient.mk (towerIdeal p n) (C (C c))) = algebraMap (O0 p) (On p n) c` using `rfl`. Rewrite using `[this, AlgHom.commutes]`. Conclude with `Subalgebra.algebraMap_mem _ c`.

Proceed by induction on `P using Polynomial.induction_on with`. Consider the case `C a => exact hC a`. Consider the case `add f g hf hg => rw [map_add, map_add]`. Conclude with `Subalgebra.add_mem _ hf hg`. Consider the case `monomial k a _`.

Simplify using `only [map_mul, map_pow]`. Conclude with `Subalgebra.mul_mem _ (hC a) (Subalgebra.pow_mem _ hY _)`.
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
Introduce `p _ Ω _ _ _ T b hb`. Take `⟨m, hm⟩` from `GlobalTheory.K5.Level.exists_mem_bn T hb`. Establish `hm1 : b ∈ GlobalTheory.K5.Level.Bn T (m + 1)` using `GlobalTheory.K5.Level.bn_le_succ T m hm`. Take `⟨ι, hι⟩` from `GlobalTheory.K5.Basic.exists_isEmb T (m + 1)`. Take `⟨w, hw⟩` from `GlobalTheory.K5.Level.bn_le_range T (m + 1) ι hι hm1`.

Conclude with `⟨m + 1, ι, w, Nat.le_add_left 1 m, hι, hw, fun w' => GlobalTheory.K5.Level.bn_le_B T (m + 1) (GlobalTheory.K5.Level.range_le_bn T (m + 1) ι hι w')⟩`.
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
