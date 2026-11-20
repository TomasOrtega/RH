import Mathlib

namespace GlobalTheory.IndexComapCosets

/- English proof (translation)
Rewrite using `[Subgroup.index_eq_card, Subgroup.index_eq_card]`. Set `φ : A ⧸ H.comap f → B ⧸ H` to `Quotient.map' f (fun a a' hr => by`. Rewrite `hr`, the goal using `[QuotientGroup.leftRel_apply]`. Simplify using `using hr)`. Establish `hφ : ∀ a : A, φ (a : A ⧸ H.comap f) = (f a : B ⧸ H)` using `fun a => rfl`.

Establish `hinj : Function.Injective φ`. Introduce `x y hxy`. Take `⟨a, rfl⟩` from `QuotientGroup.mk_surjective x`. Take `⟨a', rfl⟩` from `QuotientGroup.mk_surjective y`. Rewrite `hxy` using `[hφ, hφ, QuotientGroup.eq]`.

Rewrite using `[QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv]`. Conclude with `hxy`. Establish `hsurj : Function.Surjective φ`. Introduce `y`. Take `⟨b, rfl⟩` from `QuotientGroup.mk_surjective y`.

Take `⟨a, ha⟩` from `h b`. Conclude with `⟨a, by rw [hφ, QuotientGroup.eq]; exact ha⟩`. Conclude with `Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)`.
-/
theorem index_comap_eq_of_cosets_hit {A B : Type} [Group A] [Group B] (f : A →* B)
    (H : Subgroup B) (h : ∀ b : B, ∃ a : A, (f a)⁻¹ * b ∈ H) :
    (H.comap f).index = H.index := by
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  let φ : A ⧸ H.comap f → B ⧸ H :=
    Quotient.map' f (fun a a' hr => by
      rw [QuotientGroup.leftRel_apply] at hr ⊢
      simpa using hr)
  have hφ : ∀ a : A, φ (a : A ⧸ H.comap f) = (f a : B ⧸ H) := fun a => rfl
  have hinj : Function.Injective φ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective y
    rw [hφ, hφ, QuotientGroup.eq] at hxy
    rw [QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv]
    exact hxy
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, ha⟩ := h b
    exact ⟨a, by rw [hφ, QuotientGroup.eq]; exact ha⟩
  exact Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)

end GlobalTheory.IndexComapCosets
