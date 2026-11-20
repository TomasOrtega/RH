import Formalism.WachLatticeTwists.WachProductBases.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N1

open Finset

/- English proof (translation)
Introduce `A _ Δ _ _ _ N _ _ κ _ b ρ π hmul hone hsl hπ hcard htriv`. Take `⟨r, hr⟩` from `hcard.exists_left_inv`. Establish `hnat : ∀ (d : Δ) (m : ℕ), d • (m : A) = (m : A)` using `fun d m => map_natCast (MulSemiringAction.toRingHom Δ A d) m`. Establish `hrinv : ∀ d : Δ, d • r = r`. Introduce `d`.

Establish `h1 : (d • r) * ((Fintype.card Δ : ℕ) : A) = 1`. Use `congrArg (fun a => d • a) hr` as an intermediate fact. Simplify `this` using `[smul_mul', hnat]`. Combine the equalities or inequalities in the displayed calculation. Set `b' : κ → N` to `fun k => r • ∑ d, ρ d (b k)`.

Establish `hinv : ∀ d k, ρ d (b' k) = b' k`. Introduce `d k`. Simplify using `only [b']`. Rewrite using `[hsl, hrinv, map_sum]`. Use `congr 1`.

Simplify using `only [← hmul]`. Conclude with `Fintype.sum_equiv (Equiv.mulLeft d) _ _ (fun _ => rfl)`. Establish `hcong : ∀ k, ∃ y, b k = b' k - π • y`. Introduce `k`. Use `choose x' hx' using fun d => htriv d (b k)`.

Use `⟨r • ∑ d, x' d, ?_⟩` and prove the remaining obligations. Establish `h1 : ∑ d, ρ d (b k) = ((Fintype.card Δ : ℕ) : A) • b k + π • ∑ d, x' d`. Rewrite using `[smul_sum, Nat.cast_smul_eq_nsmul, ← card_univ, ← sum_const, ← sum_add_distrib]`. Use `sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[← hx' d]`.

Normalize the expressions using the abelian group laws. Simplify using `only [b']`. Rewrite using `[h1, smul_add, smul_smul, hr, one_smul, smul_comm r π]`. Normalize the expressions using the abelian group laws. Establish `hspan : (⊤ : Submodule A N) ≤ Submodule.span A (Set.range b')`.

Apply `Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {π}) (Module.Finite.of_basis b).fg_top` to reduce the goal to its premises. Rewrite using `[Ideal.span_le]`. Introduce `x hx`. Rewrite using `[Set.mem_singleton_iff.1 hx]`. Conclude with `hπ`.

Rewrite using `[← b.span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Take `⟨y, hy⟩` from `hcong k`. Rewrite using `[hy]`. Use `Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨k, rfl⟩)) (Submodule.mem_sup_right ?_)` and prove the remaining obligations.

Rewrite using `[b.span_eq]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self π) Submodule.mem_top`. Set `f : N →ₗ[A] N` to `b.constr A b'`. Establish `hf : ∀ k, f (b k) = b' k` using `fun k => b.constr_basis A b' k`. Establish `hsurj : Function.Surjective f`.

Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, b.constr_range]`. Conclude with `hspan`. Use `haveI : Module.Finite A N := Module.Finite.of_basis b`. Establish `hinj : Function.Injective f` using `OrzechProperty.injective_of_surjective_endomorphism f hsurj`. Set `e : N ≃ₗ[A] N` to `LinearEquiv.ofBijective f ⟨hinj, hsurj⟩`.

Use `⟨b.map e, fun d k => ?_⟩` and prove the remaining obligations. Establish `: (b.map e) k = b' k`. Rewrite using `[Module.Basis.map_apply]`. Conclude with `hf k`. Rewrite using `[this]`.

Conclude with `hinv d k`.
-/
theorem invariant_basis_average : InvariantBasisAverage := by
  intro A _ Δ _ _ _ N _ _ κ _ b ρ π hmul hone hsl hπ hcard htriv
  classical
  obtain ⟨r, hr⟩ := hcard.exists_left_inv
  have hnat : ∀ (d : Δ) (m : ℕ), d • (m : A) = (m : A) :=
    fun d m => map_natCast (MulSemiringAction.toRingHom Δ A d) m
  have hrinv : ∀ d : Δ, d • r = r := by
    intro d
    have h1 : (d • r) * ((Fintype.card Δ : ℕ) : A) = 1 := by
      have := congrArg (fun a => d • a) hr
      simpa [smul_mul', hnat] using this
    calc d • r = (d • r) * (r * ((Fintype.card Δ : ℕ) : A)) := by rw [hr, mul_one]
      _ = ((d • r) * ((Fintype.card Δ : ℕ) : A)) * r := by ring
      _ = r := by rw [h1, one_mul]
  let b' : κ → N := fun k => r • ∑ d, ρ d (b k)
  have hinv : ∀ d k, ρ d (b' k) = b' k := by
    intro d k
    simp only [b']
    rw [hsl, hrinv, map_sum]
    congr 1
    simp only [← hmul]
    exact Fintype.sum_equiv (Equiv.mulLeft d) _ _ (fun _ => rfl)
  have hcong : ∀ k, ∃ y, b k = b' k - π • y := by
    intro k
    choose x' hx' using fun d => htriv d (b k)
    refine ⟨r • ∑ d, x' d, ?_⟩
    have h1 : ∑ d, ρ d (b k) = ((Fintype.card Δ : ℕ) : A) • b k + π • ∑ d, x' d := by
      rw [smul_sum, Nat.cast_smul_eq_nsmul, ← card_univ, ← sum_const, ← sum_add_distrib]
      refine sum_congr rfl fun d _ => ?_
      rw [← hx' d]; abel
    simp only [b']
    rw [h1, smul_add, smul_smul, hr, one_smul, smul_comm r π]
    abel
  have hspan : (⊤ : Submodule A N) ≤ Submodule.span A (Set.range b') := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {π})
      (Module.Finite.of_basis b).fg_top
    · rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff.1 hx]
      exact hπ
    · rw [← b.span_eq, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨y, hy⟩ := hcong k
      rw [hy]
      refine Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨k, rfl⟩))
        (Submodule.mem_sup_right ?_)
      rw [b.span_eq]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self π) Submodule.mem_top
  let f : N →ₗ[A] N := b.constr A b'
  have hf : ∀ k, f (b k) = b' k := fun k => b.constr_basis A b' k
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, eq_top_iff, b.constr_range]
    exact hspan
  haveI : Module.Finite A N := Module.Finite.of_basis b
  have hinj : Function.Injective f := OrzechProperty.injective_of_surjective_endomorphism f hsurj
  let e : N ≃ₗ[A] N := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨b.map e, fun d k => ?_⟩
  have : (b.map e) k = b' k := by
    rw [Module.Basis.map_apply]
    exact hf k
  rw [this]
  exact hinv d k

end Formalism.RepresentationBoundsCohomology.N1
