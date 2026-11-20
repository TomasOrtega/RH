import Mathlib
import Formalism.LocalToGlobal.Columns.GoodXgFin
open Formalism.L2.DIV

namespace GlobalTheory

/- English proof (translation)
Take `⟨n, ρ, -, hch⟩` from `hχ`. Use `set N := Fintype.card G with hN`. Use `haveI : NeZero N := ⟨Fintype.card_ne_zero⟩`. Use `set f := ρ g with hf`. Establish `hfN : f ^ N = 1` using `by rw [hf, ← map_pow, pow_card_eq_one, map_one]`.

Establish `htr : LinearMap.trace (AlgebraicClosure K) _ f = (LinearMap.charpoly f).roots.sum`. Rewrite using `[LinearMap.trace_eq_matrix_trace (AlgebraicClosure K) (Pi.basisFun (AlgebraicClosure K) (Fin n)), Matrix.trace_eq_sum_roots_charpoly, LinearMap.charpoly_toMatrix]`. Establish `hz' : IsPrimitiveRoot (algebraMap K (AlgebraicClosure K) z) N` using `hz.map_of_injective (algebraMap K (AlgebraicClosure K)).injective`. Establish `hroot : ∀ μ ∈ (LinearMap.charpoly f).roots, ∃ k : ℕ, μ = algebraMap K (AlgebraicClosure K) (z ^ k)`. Introduce `μ hμ`.

Establish `hev` using `(Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr (Polynomial.isRoot_of_mem_roots hμ)`. Take `⟨v, hv⟩` from `hev.exists_hasEigenvector`. Establish `h1` using `hv.pow_apply N`. Rewrite `h1` using `[hfN]`. Establish `hμN : μ ^ N = 1`.

Establish `h2 : (μ ^ N - 1) • v = 0`. Rewrite using `[sub_smul, ← h1, one_smul]`. Simplify using the standard rewrite rules. Break down `smul_eq_zero.mp h2 with h | h` into its components or cases. Conclude with `sub_eq_zero.mp h`.

Conclude with `absurd h hv.2`. Take `⟨k, -, hk⟩` from `hz'.eq_pow_of_pow_eq_one hμN`. Conclude with `⟨k, by rw [map_pow, hk]⟩`. Establish `hsum : ∀ m : Multiset (AlgebraicClosure K), (∀ μ ∈ m, ∃ k : ℕ, μ = algebraMap K (AlgebraicClosure K) (z ^ k)) → ∃ y ∈ Subring.closure ({z} : Set K), algebraMap K (AlgebraicClosure K) y = m.sum`. Introduce `m`.

Proceed by induction on `m using Multiset.induction_on with`. Consider the case `empty => intro _; exact ⟨0, zero_mem _, by simp⟩`. Consider the case `cons a m ih`. Introduce `h`. Take `⟨y, hy, hy'⟩` from `ih (fun μ hμ => h μ (Multiset.mem_cons_of_mem hμ))`.

Take `⟨k, hk⟩` from `h a (Multiset.mem_cons_self a m)`. Use `⟨z ^ k + y, add_mem (pow_mem (Subring.subset_closure (Set.mem_singleton z)) k) hy, ?_⟩` and prove the remaining obligations. Rewrite using `[Multiset.sum_cons, map_add, hy', hk]`. Take `⟨y, hy, hy'⟩` from `hsum _ hroot`. Establish `hχg : algebraMap K (AlgebraicClosure K) (χ g) = algebraMap K (AlgebraicClosure K) y`.

Rewrite using `[← hch g, hy', ← htr]`. Both sides reduce to the same expression. Rewrite using `[(algebraMap K (AlgebraicClosure K)).injective hχg]`. Conclude with `hy`.
-/
theorem absIrrChar_mem_closure_primitiveRoot {G : Type} [Group G] [Fintype G] {K : Type} [Field K]
    [CharZero K] (z : K) (hz : IsPrimitiveRoot z (Fintype.card G)) (χ : G → K) (hχ : IsAbsIrrChar χ)
    (g : G) : χ g ∈ Subring.closure ({z} : Set K) := by
  obtain ⟨n, ρ, -, hch⟩ := hχ
  set N := Fintype.card G with hN
  haveI : NeZero N := ⟨Fintype.card_ne_zero⟩
  set f := ρ g with hf
  have hfN : f ^ N = 1 := by rw [hf, ← map_pow, pow_card_eq_one, map_one]
  have htr : LinearMap.trace (AlgebraicClosure K) _ f = (LinearMap.charpoly f).roots.sum := by
    rw [LinearMap.trace_eq_matrix_trace (AlgebraicClosure K) (Pi.basisFun (AlgebraicClosure K) (Fin n)),
      Matrix.trace_eq_sum_roots_charpoly, LinearMap.charpoly_toMatrix]
  have hz' : IsPrimitiveRoot (algebraMap K (AlgebraicClosure K) z) N :=
    hz.map_of_injective (algebraMap K (AlgebraicClosure K)).injective
  have hroot : ∀ μ ∈ (LinearMap.charpoly f).roots,
      ∃ k : ℕ, μ = algebraMap K (AlgebraicClosure K) (z ^ k) := by
    intro μ hμ
    have hev := (Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr (Polynomial.isRoot_of_mem_roots hμ)
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have h1 := hv.pow_apply N
    rw [hfN] at h1
    have hμN : μ ^ N = 1 := by
      have h2 : (μ ^ N - 1) • v = 0 := by
        rw [sub_smul, ← h1, one_smul]; simp
      rcases smul_eq_zero.mp h2 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hv.2
    obtain ⟨k, -, hk⟩ := hz'.eq_pow_of_pow_eq_one hμN
    exact ⟨k, by rw [map_pow, hk]⟩
  have hsum : ∀ m : Multiset (AlgebraicClosure K),
      (∀ μ ∈ m, ∃ k : ℕ, μ = algebraMap K (AlgebraicClosure K) (z ^ k)) →
      ∃ y ∈ Subring.closure ({z} : Set K), algebraMap K (AlgebraicClosure K) y = m.sum := by
    intro m
    induction m using Multiset.induction_on with
    | empty => intro _; exact ⟨0, zero_mem _, by simp⟩
    | cons a m ih =>
      intro h
      obtain ⟨y, hy, hy'⟩ := ih (fun μ hμ => h μ (Multiset.mem_cons_of_mem hμ))
      obtain ⟨k, hk⟩ := h a (Multiset.mem_cons_self a m)
      refine ⟨z ^ k + y, add_mem (pow_mem (Subring.subset_closure (Set.mem_singleton z)) k) hy, ?_⟩
      rw [Multiset.sum_cons, map_add, hy', hk]
  obtain ⟨y, hy, hy'⟩ := hsum _ hroot
  have hχg : algebraMap K (AlgebraicClosure K) (χ g) = algebraMap K (AlgebraicClosure K) y := by
    rw [← hch g, hy', ← htr]; rfl
  rw [(algebraMap K (AlgebraicClosure K)).injective hχg]
  exact hy

end GlobalTheory
