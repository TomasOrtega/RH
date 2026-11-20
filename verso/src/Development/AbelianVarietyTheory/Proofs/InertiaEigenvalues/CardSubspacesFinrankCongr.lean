import Mathlib

open scoped BigOperators

namespace GlobalTheory

open Module

/- English proof (translation)
Use `symm`. Use `Nat.card_congr (Equiv.ofBijective (fun U => ⟨U.1.map p.subtype, Submodule.map_subtype_le p U.1, ?_⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Rewrite using `[Submodule.finrank_map_subtype_eq]`. Conclude with `U.2`. Introduce `U U' h`.

Conclude with `Subtype.ext (Submodule.map_injective_of_injective p.injective_subtype (congrArg Subtype.val h))`. Introduce and unpack `⟨U, hU, hj⟩`. Establish `h : (U.comap p.subtype).map p.subtype = U`. Rewrite using `[Submodule.map_comap_subtype, inf_eq_right.2 hU]`. Use `⟨⟨U.comap p.subtype, ?_⟩, Subtype.ext h⟩` and prove the remaining obligations.

Rewrite using `[← Submodule.finrank_map_subtype_eq, h, hj]`.
-/
theorem card_subspaces_le_eq {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (p : Submodule k V) (j : ℕ) :
    Nat.card {U : Submodule k V // U ≤ p ∧ finrank k U = j} =
      Nat.card {U : Submodule k p // finrank k U = j} := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun U => ⟨U.1.map p.subtype, Submodule.map_subtype_le p U.1, ?_⟩) ⟨?_, ?_⟩)
  · rw [Submodule.finrank_map_subtype_eq]; exact U.2
  · intro U U' h
    exact Subtype.ext (Submodule.map_injective_of_injective p.injective_subtype
      (congrArg Subtype.val h))
  · rintro ⟨U, hU, hj⟩
    have h : (U.comap p.subtype).map p.subtype = U := by
      rw [Submodule.map_comap_subtype, inf_eq_right.2 hU]
    refine ⟨⟨U.comap p.subtype, ?_⟩, Subtype.ext h⟩
    rw [← Submodule.finrank_map_subtype_eq, h, hj]

/- English proof (translation)
Use `Nat.card_congr (Equiv.subtypeEquiv (Submodule.orderIsoMapComap e).toEquiv ?_)` and prove the remaining obligations. Introduce `U`. Establish `: finrank k (U.map (e : V →ₗ[k] V')) = finrank k U` using `LinearEquiv.finrank_map_eq e U`. Express the relevant statement in the definitionally equal form `_ ↔ finrank k (U.map (e : V →ₗ[k] V')) = j`. Rewrite using `[this]`.
-/
theorem card_subspaces_finrank_congr {k V V' : Type} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] (e : V ≃ₗ[k] V') (j : ℕ) :
    Nat.card {U : Submodule k V // finrank k U = j} =
      Nat.card {U : Submodule k V' // finrank k U = j} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Submodule.orderIsoMapComap e).toEquiv ?_)
  intro U
  have : finrank k (U.map (e : V →ₗ[k] V')) = finrank k U := LinearEquiv.finrank_map_eq e U
  change _ ↔ finrank k (U.map (e : V →ₗ[k] V')) = j
  rw [this]

end GlobalTheory
