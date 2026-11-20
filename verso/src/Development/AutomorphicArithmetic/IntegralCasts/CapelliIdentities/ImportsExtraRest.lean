import Mathlib

/- English proof (translation)
Introduce `O Ω V _ _ _ _ _ R A B c hB v`. Set `f : V →+ V` to `DistribSMul.toAddMonoidHom V c`. Establish `hS : {v : V | ∃ a ∈ R, ∃ e ∈ B, v = a • e} = f '' {v : V | ∃ a ∈ R, ∃ e ∈ A, v = a • e}`. Use extensionality with `w`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_image]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, e, he, rfl⟩`. Take `⟨e', he', rfl⟩` from `(hB e).1 he`. Use `⟨a • e', ⟨a, ha, e', he', rfl⟩, ?_⟩` and prove the remaining obligations. Use `show c • a • e' = a • c • e'`.

Rewrite using `[smul_smul, smul_smul, mul_comm]`. Introduce and unpack `⟨x, ⟨a, ha, e, he, rfl⟩, rfl⟩`. Use `⟨a, ha, c • e, (hB _).2 ⟨e, he, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show c • a • e = a • c • e`. Rewrite using `[smul_smul, smul_smul, mul_comm]`.

Rewrite using `[hS, ← AddMonoidHom.map_closure, AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨x, hx, rfl⟩`. Introduce and unpack `⟨x, hx, rfl⟩`.

Conclude with `⟨x, hx, rfl⟩`.
-/
theorem UpperTheory.Reformulated.B.Ydb6.main :
    ∀ {O Ω V : Type} [inst : CommRing O] [inst_1 : Field Ω] [inst_2 : Algebra O Ω] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module Ω V] (R : Subalgebra O Ω) (A B : AddSubgroup V) (c : Ω),
      (∀ (v : V), v ∈ B ↔ ∃ e ∈ A, v = c • e) →
        ∀ (v : V),
          v ∈ AddSubgroup.closure {v : V | ∃ a ∈ R, ∃ e ∈ B, v = a • e} ↔
            ∃ e ∈ AddSubgroup.closure {v : V | ∃ a ∈ R, ∃ e ∈ A, v = a • e}, v = c • e := by
  intro O Ω V _ _ _ _ _ R A B c hB v
  let f : V →+ V := DistribSMul.toAddMonoidHom V c
  have hS : {v : V | ∃ a ∈ R, ∃ e ∈ B, v = a • e} =
      f '' {v : V | ∃ a ∈ R, ∃ e ∈ A, v = a • e} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨a, ha, e, he, rfl⟩
      obtain ⟨e', he', rfl⟩ := (hB e).1 he
      refine ⟨a • e', ⟨a, ha, e', he', rfl⟩, ?_⟩
      show c • a • e' = a • c • e'
      rw [smul_smul, smul_smul, mul_comm]
    · rintro ⟨x, ⟨a, ha, e, he, rfl⟩, rfl⟩
      refine ⟨a, ha, c • e, (hB _).2 ⟨e, he, rfl⟩, ?_⟩
      show c • a • e = a • c • e
      rw [smul_smul, smul_smul, mul_comm]
  rw [hS, ← AddMonoidHom.map_closure, AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
