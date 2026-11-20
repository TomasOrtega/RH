import Mathlib

open scoped Classical

namespace GlobalTheory

/- English proof (translation)
Establish `key : ∀ b ∈ T₁ ×ˢ T₂, ∑ p ∈ S.filter (fun p => (cls p.1, cls p.2) = b), w p.1 * (om (cls p.1) * om (cls p.2)) ≤ om b.1 * om b.2`. Introduce `b _`. Use `set F := S.filter (fun p => (cls p.1, cls p.2) = b) with hF`. Establish `h1 : ∑ p ∈ F, w p.1 * (om (cls p.1) * om (cls p.2)) = (∑ p ∈ F, w p.1) * (om b.1 * om b.2)`. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl ?_` and prove the remaining obligations. Introduce `p hp`. Establish `e` using `(Finset.mem_filter.1 hp).2`. Rewrite using `[← e]`. Establish `h2 : ∑ p ∈ F, w p.1 = ∑ a ∈ F.image Prod.fst, w a`.

Rewrite using `[Finset.sum_image]`. Introduce `p hp q hq hpq`. Establish `ep` using `(Finset.mem_filter.1 hp).2`. Establish `eq` using `(Finset.mem_filter.1 hq).2`. Establish `hc : cls p.2 = cls q.2`.

Use `congrArg Prod.snd (ep.trans eq.symm)` as an intermediate fact. Simplify using `using this`. Conclude with `hinj p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1 hpq hc`. Establish `h3 : F.image Prod.fst ⊆ (S.image Prod.fst).filter (fun a => cls a = b.1)`. Introduce `a ha`.

Take `⟨p, hp, rfl⟩` from `Finset.mem_image.1 ha`. Establish `hp'` using `Finset.mem_filter.1 hp`. Use `Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hp'.1, ?_⟩` and prove the remaining obligations. Use `congrArg Prod.fst hp'.2` as an intermediate fact. Simplify using `using this`.

Establish `h4 : ∑ p ∈ F, w p.1 ≤ 1`. Rewrite using `[h2]`. Conclude with `(Finset.sum_le_sum_of_subset_of_nonneg h3 (fun a _ _ => hw a)).trans (hsum b.1)`. Rewrite using `[h1]`. Establish `hnn : 0 ≤ om b.1 * om b.2` using `mul_nonneg (hom _) (hom _)`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Use `symm`. Conclude with `Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_product.2 (hT p hp)) _`. Use `_ ≤ ∑ b ∈ T₁ ×ˢ T₂, om b.1 * om b.2 := Finset.sum_le_sum key`.

Use `_ = (∑ b ∈ T₁, om b) * ∑ b ∈ T₂, om b := by`. Rewrite using `[Finset.sum_product, Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun x _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.
-/
theorem sum_pairs_weight_mul_class_le_mul_sum (α β : Type) (S : Finset (α × α)) (cls : α → β)
    (w : α → ℝ) (om : β → ℝ) (T₁ T₂ : Finset β) (hw : ∀ a, 0 ≤ w a) (hom : ∀ b, 0 ≤ om b)
    (hT : ∀ p ∈ S, cls p.1 ∈ T₁ ∧ cls p.2 ∈ T₂)
    (hinj : ∀ p ∈ S, ∀ q ∈ S, p.1 = q.1 → cls p.2 = cls q.2 → p = q)
    (hsum : ∀ b, ∑ a ∈ (S.image Prod.fst).filter (fun a => cls a = b), w a ≤ 1) :
    ∑ p ∈ S, w p.1 * (om (cls p.1) * om (cls p.2)) ≤ (∑ b ∈ T₁, om b) * ∑ b ∈ T₂, om b := by

  have key : ∀ b ∈ T₁ ×ˢ T₂,
      ∑ p ∈ S.filter (fun p => (cls p.1, cls p.2) = b), w p.1 * (om (cls p.1) * om (cls p.2))
        ≤ om b.1 * om b.2 := by
    intro b _
    set F := S.filter (fun p => (cls p.1, cls p.2) = b) with hF
    have h1 : ∑ p ∈ F, w p.1 * (om (cls p.1) * om (cls p.2))
        = (∑ p ∈ F, w p.1) * (om b.1 * om b.2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro p hp
      have e := (Finset.mem_filter.1 hp).2
      rw [← e]
    have h2 : ∑ p ∈ F, w p.1 = ∑ a ∈ F.image Prod.fst, w a := by
      rw [Finset.sum_image]
      intro p hp q hq hpq
      have ep := (Finset.mem_filter.1 hp).2
      have eq := (Finset.mem_filter.1 hq).2
      have hc : cls p.2 = cls q.2 := by
        have := congrArg Prod.snd (ep.trans eq.symm)
        simpa using this
      exact hinj p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1 hpq hc
    have h3 : F.image Prod.fst ⊆ (S.image Prod.fst).filter (fun a => cls a = b.1) := by
      intro a ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
      have hp' := Finset.mem_filter.1 hp
      refine Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hp'.1, ?_⟩
      have := congrArg Prod.fst hp'.2
      simpa using this
    have h4 : ∑ p ∈ F, w p.1 ≤ 1 := by
      rw [h2]
      exact (Finset.sum_le_sum_of_subset_of_nonneg h3 (fun a _ _ => hw a)).trans (hsum b.1)
    rw [h1]
    have hnn : 0 ≤ om b.1 * om b.2 := mul_nonneg (hom _) (hom _)
    calc (∑ p ∈ F, w p.1) * (om b.1 * om b.2) ≤ 1 * (om b.1 * om b.2) :=
          mul_le_mul_of_nonneg_right h4 hnn
      _ = om b.1 * om b.2 := one_mul _
  calc ∑ p ∈ S, w p.1 * (om (cls p.1) * om (cls p.2))
      = ∑ b ∈ T₁ ×ˢ T₂, ∑ p ∈ S.filter (fun p => (cls p.1, cls p.2) = b),
          w p.1 * (om (cls p.1) * om (cls p.2)) := by
        symm
        exact Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_product.2 (hT p hp)) _
    _ ≤ ∑ b ∈ T₁ ×ˢ T₂, om b.1 * om b.2 := Finset.sum_le_sum key
    _ = (∑ b ∈ T₁, om b) * ∑ b ∈ T₂, om b := by
      rw [Finset.sum_product, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]

end GlobalTheory
