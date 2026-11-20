import Mathlib

open Topology Filter

namespace GlobalTheory

/- English proof (translation)
Take `⟨t, hts, hspan, hli⟩` from `exists_linearIndependent ℂ s`. Establish `ht : t.Finite`. Assume the negation of the conclusion as `hinf`. Establish `hinf' : t.Infinite` using `hinf`. Set `e : ℕ ↪ t` to `hinf'.natEmbedding`.

Establish `hli' : LinearIndepOn ℂ id t` using `hli`. Set `b` to `Module.Basis.extend hli'`. Set `v : (hli'.extend (Set.subset_univ t)) → ℂ` to `fun i => if h : ∃ k : ℕ, ((e k : t) : V) = (i : V) then (h.choose : ℂ) else 0`. Take `⟨C, hC⟩` from `hs (b.constr ℂ v)`. Establish `key : ∀ k : ℕ, b.constr ℂ v ((e k : t) : V) = (k : ℂ)`.

Introduce `k`. Establish `hmem : ((e k : t) : V) ∈ hli'.extend (Set.subset_univ t)` using `hli'.subset_extend _ (e k).2`. Establish `hb : b ⟨_, hmem⟩ = ((e k : t) : V)` using `by simp [b, Module.Basis.coe_extend]`. Rewrite using `[← hb, Module.Basis.constr_basis]`. Establish `h : ∃ j : ℕ, ((e j : t) : V) = ((⟨_, hmem⟩ : hli'.extend (Set.subset_univ t)) : V)` using `⟨k, rfl⟩`.

Simplify using `only [v, dif_pos h]`. Establish `hj : h.choose = k` using `e.injective (Subtype.ext h.choose_spec)`. Rewrite using `[hj]`. Take `⟨k, hk⟩` from `exists_nat_gt C`. Establish `hle` using `hC _ (hts (e k).2)`.

Rewrite `hle` using `[key, Complex.norm_natCast]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfd : FiniteDimensional ℂ (Submodule.span ℂ t)` using `FiniteDimensional.span_of_finite ℂ ht`. Rewrite `hfd` using `[hspan]`. Conclude with `hfd`.
-/
theorem span_finiteDimensional_of_bounded_forms {V : Type} [AddCommGroup V] [Module ℂ V]
    (s : Set V) (hs : ∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) :
    FiniteDimensional ℂ (Submodule.span ℂ s) := by
  classical
  obtain ⟨t, hts, hspan, hli⟩ := exists_linearIndependent ℂ s
  have ht : t.Finite := by
    by_contra hinf
    have hinf' : t.Infinite := hinf
    let e : ℕ ↪ t := hinf'.natEmbedding
    have hli' : LinearIndepOn ℂ id t := hli
    let b := Module.Basis.extend hli'
    let v : (hli'.extend (Set.subset_univ t)) → ℂ := fun i =>
      if h : ∃ k : ℕ, ((e k : t) : V) = (i : V) then (h.choose : ℂ) else 0
    obtain ⟨C, hC⟩ := hs (b.constr ℂ v)
    have key : ∀ k : ℕ, b.constr ℂ v ((e k : t) : V) = (k : ℂ) := by
      intro k
      have hmem : ((e k : t) : V) ∈ hli'.extend (Set.subset_univ t) :=
        hli'.subset_extend _ (e k).2
      have hb : b ⟨_, hmem⟩ = ((e k : t) : V) := by simp [b, Module.Basis.coe_extend]
      rw [← hb, Module.Basis.constr_basis]
      have h : ∃ j : ℕ, ((e j : t) : V) = ((⟨_, hmem⟩ : hli'.extend (Set.subset_univ t)) : V) :=
        ⟨k, rfl⟩
      simp only [v, dif_pos h]
      have hj : h.choose = k := e.injective (Subtype.ext h.choose_spec)
      rw [hj]
    obtain ⟨k, hk⟩ := exists_nat_gt C
    have hle := hC _ (hts (e k).2)
    rw [key, Complex.norm_natCast] at hle
    linarith
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ t) := FiniteDimensional.span_of_finite ℂ ht
  rw [hspan] at hfd
  exact hfd

end GlobalTheory
