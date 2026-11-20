import Mathlib

/- English proof (translation)
Introduce `O LL V _ _ _ _ _ _ _ _ _ _ Λ A hΛ c hc`. Use `haveI : IsNoetherian O Λ := isNoetherian_of_fg_of_noetherian Λ hΛ`. Set `f : ℕ →o Submodule O Λ` to `⟨fun n => (A.comap ((c ^ n) • LinearMap.id : V →ₗ[O] V)).comap Λ.subtype, by`. Introduce `m n hmn x hx`. Simplify using `only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢`.

Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Rewrite using `[pow_add, mul_comm, mul_smul]`. Conclude with `A.smul_mem _ hx⟩`. Take `⟨N, hN⟩` from `(monotone_stabilizes_iff_noetherian.mpr inferInstance) f`. Use `⟨c ^ (N + 1), pow_ne_zero _ hc, ?_⟩` and prove the remaining obligations.

Introduce `u hu hμ`. Establish `h1 : (⟨u, hu⟩ : Λ) ∈ f (N + 1)` using `hμ`. Rewrite `h1` using `[← hN (N + 1) (Nat.le_succ N)]`. Establish `h2 : c ^ N • u ∈ A` using `h1`. Conclude with `⟨c ^ N • u, h2, by rw [pow_succ, mul_comm, mul_smul]⟩`.
-/
theorem _root_.UpperTheory.KN.admissible_lattices_commensurable :
    ∀ {O LL V : Type} [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field LL] [Algebra O LL] [IsFractionRing O LL]
      [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] (Λ A : Submodule O V), Λ.FG → ∀ c : O, c ≠ 0 →
      ∃ μ : O, μ ≠ 0 ∧ ∀ u ∈ Λ, μ • u ∈ A → ∃ a ∈ A, μ • u = c • a := by
  intro O LL V _ _ _ _ _ _ _ _ _ _ Λ A hΛ c hc
  haveI : IsNoetherian O Λ := isNoetherian_of_fg_of_noetherian Λ hΛ
  let f : ℕ →o Submodule O Λ :=
    ⟨fun n => (A.comap ((c ^ n) • LinearMap.id : V →ₗ[O] V)).comap Λ.subtype, by
      intro m n hmn x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.smul_apply,
        LinearMap.id_apply] at hx ⊢
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [pow_add, mul_comm, mul_smul]
      exact A.smul_mem _ hx⟩
  obtain ⟨N, hN⟩ := (monotone_stabilizes_iff_noetherian.mpr inferInstance) f
  refine ⟨c ^ (N + 1), pow_ne_zero _ hc, ?_⟩
  intro u hu hμ
  have h1 : (⟨u, hu⟩ : Λ) ∈ f (N + 1) := hμ
  rw [← hN (N + 1) (Nat.le_succ N)] at h1
  have h2 : c ^ N • u ∈ A := h1
  exact ⟨c ^ N • u, h2, by rw [pow_succ, mul_comm, mul_smul]⟩
