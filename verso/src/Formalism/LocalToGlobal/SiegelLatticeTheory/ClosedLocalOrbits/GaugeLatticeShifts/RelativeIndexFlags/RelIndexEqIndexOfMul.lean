import Mathlib

namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt

variable {G : Type*} [Group G]

/- English proof (translation)
Establish `hs : MulAction.stabilizer R (((1 : G) : G ⧸ A)) = A.subgroupOf R`. Use extensionality with `r`. Rewrite using `[MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]`. Express the relevant statement in the definitionally equal form `((((r : G) * 1 : G)) : G ⧸ A) = ((1 : G) : G ⧸ A) ↔ _`. Rewrite using `[mul_one, QuotientGroup.eq]`.

Simplify using the standard rewrite rules. Establish `ho : MulAction.orbit R (((1 : G) : G ⧸ A)) = Set.univ`. Use extensionality with `q`. Simplify using `only [Set.mem_univ, iff_true]`. Proceed by induction on `q using QuotientGroup.induction_on with`.

Consider the case `H y`. Take `⟨r, hr, a, ha, rfl⟩` from `h y`. Use `⟨⟨r, hr⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((((r : G) * 1 : G)) : G ⧸ A) = ((r * a : G) : G ⧸ A)`. Rewrite using `[mul_one, QuotientGroup.eq]`.

Simplify using `using ha`. Rewrite using `[Subgroup.relIndex, ← hs, MulAction.index_stabilizer, ho, Set.ncard_univ, Subgroup.index_eq_card]`.
-/
theorem relIndex_eq_index_of_mul (A R : Subgroup G)
    (h : ∀ y : G, ∃ r ∈ R, ∃ a ∈ A, y = r * a) : A.relIndex R = A.index := by
  have hs : MulAction.stabilizer R (((1 : G) : G ⧸ A)) = A.subgroupOf R := by
    ext r
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change ((((r : G) * 1 : G)) : G ⧸ A) = ((1 : G) : G ⧸ A) ↔ _
    rw [mul_one, QuotientGroup.eq]
    simp
  have ho : MulAction.orbit R (((1 : G) : G ⧸ A)) = Set.univ := by
    ext q
    simp only [Set.mem_univ, iff_true]
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨r, hr, a, ha, rfl⟩ := h y
      refine ⟨⟨r, hr⟩, ?_⟩
      change ((((r : G) * 1 : G)) : G ⧸ A) = ((r * a : G) : G ⧸ A)
      rw [mul_one, QuotientGroup.eq]
      simpa using ha
  rw [Subgroup.relIndex, ← hs, MulAction.index_stabilizer, ho, Set.ncard_univ,
    Subgroup.index_eq_card]

/- English proof (translation)
Rewrite using `[← Subgroup.relIndex_subgroupOf hBB]`. Use `relIndex_eq_index_of_mul (A.subgroupOf B') (B.subgroupOf B') ?_` and prove the remaining obligations. Introduce `y`. Take `⟨b, hb, a, ha, hy⟩` from `h y.1 y.2`. Establish `haB : a ∈ B'`.

Establish `: a = b⁻¹ * y.1` using `by rw [hy]; group`. Rewrite using `[this]`. Conclude with `B'.mul_mem (B'.inv_mem (hBB hb)) y.2`. Use `⟨⟨b, hBB hb⟩, ?_, ⟨a, haB⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.mem_subgroupOf]`.

Conclude with `hb`. Rewrite using `[Subgroup.mem_subgroupOf]`. Conclude with `ha`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hy]`.
-/
theorem relIndex_eq_of_mul (A B B' : Subgroup G) (hBB : B ≤ B')
    (h : ∀ y ∈ B', ∃ b ∈ B, ∃ a ∈ A, y = b * a) : A.relIndex B = A.relIndex B' := by
  rw [← Subgroup.relIndex_subgroupOf hBB]
  refine relIndex_eq_index_of_mul (A.subgroupOf B') (B.subgroupOf B') ?_
  intro y
  obtain ⟨b, hb, a, ha, hy⟩ := h y.1 y.2
  have haB : a ∈ B' := by
    have : a = b⁻¹ * y.1 := by rw [hy]; group
    rw [this]; exact B'.mul_mem (B'.inv_mem (hBB hb)) y.2
  refine ⟨⟨b, hBB hb⟩, ?_, ⟨a, haB⟩, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]; exact hb
  · rw [Subgroup.mem_subgroupOf]; exact ha
  · apply Subtype.ext; simp [hy]

/- English proof (translation)
Unfold `Subgroup.relIndex`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]`. Conclude with `⟨fun h => h.1, fun h => ⟨h, hL x.2⟩⟩`.
-/
theorem inf_relIndex_of_le (H N L : Subgroup G) (hL : L ≤ N) :
    (H ⊓ N).relIndex L = H.relIndex L := by
  unfold Subgroup.relIndex
  congr 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, hL x.2⟩⟩

/- English proof (translation)
Establish `e1` using `Subgroup.relIndex_inf_mul_relIndex H (H ⊔ N) X`. Rewrite `e1` using `[show H ⊓ (H ⊔ N) = H from inf_of_le_left le_sup_left]`. Establish `e2 : (H ⊔ N).relIndex X = (H ⊔ N).relIndex (X ⊔ N)`. Use `relIndex_eq_of_mul _ _ _ le_sup_left ?_` and prove the remaining obligations. Introduce `y hy`.

Take `⟨x, hx, z, hz, rfl⟩` from `(Subgroup.mem_sup_of_normal_right).1 hy`. Conclude with `⟨x, hx, z, Subgroup.mem_sup_right hz, rfl⟩`. Establish `e3 : H.relIndex (X ⊓ N) = H.relIndex ((H ⊔ N) ⊓ X)`. Use `relIndex_eq_of_mul _ _ _ ?_ ?_` and prove the remaining obligations. Introduce `y hy`.

Conclude with `⟨Subgroup.mem_sup_right hy.2, hy.1⟩`. Introduce `y hy`. Take `⟨h, hh, z, hz, hyz⟩` from `(Subgroup.mem_sup_of_normal_right).1 hy.1`. Use `⟨y * h⁻¹, ⟨X.mul_mem hy.2 (X.inv_mem (hHX hh)), ?_⟩, h, hh, by group⟩` and prove the remaining obligations. Rewrite using `[← hyz]`.

Establish `: h * z * h⁻¹ ∈ N` using `hN.conj_mem z hz h`. Simplify `this` using `[mul_assoc]`. Rewrite using `[← e1, ← e3, e2, inf_relIndex_of_le H N (X ⊓ N) inf_le_right]`.
-/
theorem relIndex_split (N : Subgroup G) [hN : N.Normal] (H X : Subgroup G) (hHX : H ≤ X) :
    H.relIndex X = (H ⊓ N).relIndex (X ⊓ N) * (H ⊔ N).relIndex (X ⊔ N) := by
  have e1 := Subgroup.relIndex_inf_mul_relIndex H (H ⊔ N) X
  rw [show H ⊓ (H ⊔ N) = H from inf_of_le_left le_sup_left] at e1
  have e2 : (H ⊔ N).relIndex X = (H ⊔ N).relIndex (X ⊔ N) := by
    refine relIndex_eq_of_mul _ _ _ le_sup_left ?_
    intro y hy
    obtain ⟨x, hx, z, hz, rfl⟩ := (Subgroup.mem_sup_of_normal_right).1 hy
    exact ⟨x, hx, z, Subgroup.mem_sup_right hz, rfl⟩
  have e3 : H.relIndex (X ⊓ N) = H.relIndex ((H ⊔ N) ⊓ X) := by
    refine relIndex_eq_of_mul _ _ _ ?_ ?_
    · intro y hy
      exact ⟨Subgroup.mem_sup_right hy.2, hy.1⟩
    · intro y hy
      obtain ⟨h, hh, z, hz, hyz⟩ := (Subgroup.mem_sup_of_normal_right).1 hy.1
      refine ⟨y * h⁻¹, ⟨X.mul_mem hy.2 (X.inv_mem (hHX hh)), ?_⟩, h, hh, by group⟩
      rw [← hyz]
      have : h * z * h⁻¹ ∈ N := hN.conj_mem z hz h
      simpa [mul_assoc] using this
  rw [← e1, ← e3, e2, inf_relIndex_of_le H N (X ⊓ N) inf_le_right]

abbrev cj (g : G) (A : Subgroup G) : Subgroup G := A.map (MulAut.conj g).toMonoidHom

/- English proof (translation)
Simplify using `[cj, Subgroup.mem_map, MulAut.conj_apply]`.
-/
theorem mem_cj (g : G) (A : Subgroup G) (y : G) : y ∈ cj g A ↔ ∃ x ∈ A, g * x * g⁻¹ = y := by
  simp [cj, Subgroup.mem_map, MulAut.conj_apply]

end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
