import Mathlib
open Module

namespace GlobalTheory

/- English proof (translation)
Use `set H := (Ideal.span {t ^ (r + 1)}).toAddSubgroup with hH`. Use `set K := (Ideal.span {t ^ r}).toAddSubgroup with hK`. Establish `hHK : H ≤ K`. Introduce `x hx`. Simplify using `only [hH, hK, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton] at hx ⊢`.

Conclude with `(pow_dvd_pow t (Nat.le_succ r)).trans hx`. Establish `e1 : Nat.card (O ⧸ Ideal.span {t ^ (r + 1)}) = H.index` using `rfl`. Establish `e2 : Nat.card (O ⧸ Ideal.span {t ^ r}) = K.index` using `rfl`. Establish `e3 : Nat.card (O ⧸ Ideal.span {t}) = (Ideal.span {t}).toAddSubgroup.index` using `rfl`. Rewrite using `[e1, e2, e3, ← AddSubgroup.relIndex_mul_index hHK]`.

Use `congr 1`. Set `φ : O →+ K` to `{ toFun := fun x => ⟨t ^ r * x, by`. Simplify using `only [hK, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]`. Conclude with `dvd_mul_right _ _⟩`. Use the proof step `map_zero' := by ext; simp`.

Use the proof step `map_add' := by intro x y; ext; simp [mul_add] }`. Establish `hφ : Function.Surjective φ`. Introduce and unpack `⟨y, hy⟩`. Establish `hy' : y ∈ Ideal.span {t ^ r}` using `hy`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton.mp hy'`.

Conclude with `⟨a, rfl⟩`. Establish `hc : (H.addSubgroupOf K).comap φ = (Ideal.span {t}).toAddSubgroup`. Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, hH, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]`. Express the relevant statement in the definitionally equal form `t ^ (r + 1) ∣ t ^ r * x ↔ t ∣ x`.

Rewrite using `[pow_succ]`. Conclude with `mul_dvd_mul_iff_left (pow_ne_zero r ht)`. Rewrite using `[AddSubgroup.relIndex, ← hc, AddSubgroup.index_comap_of_surjective _ hφ]`.
-/
theorem card_quot_span_pow_succ_eq_mul_domain (O : Type) [CommRing O] [IsDomain O] (t : O) (ht : t ≠ 0)
    (r : ℕ) :
    Nat.card (O ⧸ Ideal.span {t ^ (r + 1)}) =
      Nat.card (O ⧸ Ideal.span {t}) * Nat.card (O ⧸ Ideal.span {t ^ r}) := by
  set H := (Ideal.span {t ^ (r + 1)}).toAddSubgroup with hH
  set K := (Ideal.span {t ^ r}).toAddSubgroup with hK
  have hHK : H ≤ K := by
    intro x hx
    simp only [hH, hK, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton] at hx ⊢
    exact (pow_dvd_pow t (Nat.le_succ r)).trans hx
  have e1 : Nat.card (O ⧸ Ideal.span {t ^ (r + 1)}) = H.index := rfl
  have e2 : Nat.card (O ⧸ Ideal.span {t ^ r}) = K.index := rfl
  have e3 : Nat.card (O ⧸ Ideal.span {t}) = (Ideal.span {t}).toAddSubgroup.index := rfl
  rw [e1, e2, e3, ← AddSubgroup.relIndex_mul_index hHK]
  congr 1
  let φ : O →+ K :=
    { toFun := fun x => ⟨t ^ r * x, by
        simp only [hK, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
        exact dvd_mul_right _ _⟩
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp [mul_add] }
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ Ideal.span {t ^ r} := hy
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hy'
    exact ⟨a, rfl⟩
  have hc : (H.addSubgroupOf K).comap φ = (Ideal.span {t}).toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, hH,
      Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
    change t ^ (r + 1) ∣ t ^ r * x ↔ t ∣ x
    rw [pow_succ]
    exact mul_dvd_mul_iff_left (pow_ne_zero r ht)
  rw [AddSubgroup.relIndex, ← hc, AddSubgroup.index_comap_of_surjective _ hφ]

/- English proof (translation)
Introduce `O _ _ t ht _ r`. Proceed by induction on `r with`. Consider the case `zero`. Rewrite using `[pow_zero, pow_zero, Ideal.span_singleton_one]`. Conclude with `Nat.card_unique`.

Consider the case `succ r ih`. Rewrite using `[card_quot_span_pow_succ_eq_mul_domain O t ht r, ih, pow_succ, mul_comm]`.
-/
theorem card_quot_span_pow :
    ∀ (O : Type) [CommRing O] [IsDomain O] (t : O), t ≠ 0 → Finite (O ⧸ Ideal.span {t}) →
      ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {t ^ r}) = Nat.card (O ⧸ Ideal.span {t}) ^ r := by
  intro O _ _ t ht _ r
  induction r with
  | zero =>
    rw [pow_zero, pow_zero, Ideal.span_singleton_one]
    exact Nat.card_unique
  | succ r ih =>
    rw [card_quot_span_pow_succ_eq_mul_domain O t ht r, ih, pow_succ, mul_comm]

end GlobalTheory
