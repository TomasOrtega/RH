import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Simplify using `[sqs, Subgroup.mem_map]`.
-/
private theorem mem_sqs_iff_exists_sq {G : Type} [CommGroup G] (U : Subgroup G) (x : G) :
    x ∈ sqs U ↔ ∃ y ∈ U, y ^ 2 = x := by
  simp [sqs, Subgroup.mem_map]

/- English proof (translation)
Introduce `A _ σ ε hσ h90 hε1 hε2 hσε h2`. Use `set B : Subgroup A := σ.eqLocus (MonoidHom.id A) with hB`. Use `set N : Subgroup A := (MonoidHom.id A * σ).ker with hN`. Use `set S : Subgroup A := sqs (⊤ : Subgroup A) with hS`. Establish `memB : ∀ a, a ∈ B ↔ σ a = a` using `fun a => Iff.rfl`.

Establish `memN : ∀ a, a ∈ N ↔ a * σ a = 1` using `fun a => Iff.rfl`. Establish `memS : ∀ a, a ∈ S ↔ ∃ y, y ^ 2 = a` using `fun a => by`. Rewrite using `[hS, mem_sqs_iff_exists_sq]`. Simplify using the standard rewrite rules. Set `f : A →* A` to `MonoidHom.id A / σ`.

Establish `hf : ∀ a, f a = a / σ a` using `fun a => rfl`. Establish `hker : ∀ a, f a = 1 ↔ a ∈ B` using `fun a => by`. Rewrite using `[hf, memB, div_eq_one, eq_comm]`. Establish `hrange : f.range = N`. Use extensionality with `x`.

Rewrite using `[memN, MonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Rewrite using `[hf, map_div, hσ]`. Simplify using the standard rewrite rules.

Introduce `hx`. Take `⟨b, hb⟩` from `h90 x hx`. Conclude with `⟨b, hb.symm⟩`. Establish `hcomap : B ⊔ S = (sqs N).comap f`. Apply `le_antisymm` to reduce the goal to its premises.

Apply `sup_le` to reduce the goal to its premises. Introduce `a ha`. Rewrite using `[Subgroup.mem_comap, (hker a).2 ha]`. Conclude with `one_mem _`. Introduce `a ha`.

Take `⟨y, rfl⟩` from `(memS a).1 ha`. Rewrite using `[Subgroup.mem_comap, mem_sqs_iff_exists_sq]`. Conclude with `⟨f y, hrange ▸ ⟨y, rfl⟩, (map_pow f y 2).symm⟩`. Introduce `a ha`. Rewrite `ha` using `[Subgroup.mem_comap, mem_sqs_iff_exists_sq]`.

Take `⟨c, hc, hca⟩` from `ha`. Rewrite `hc` using `[← hrange]`. Take `⟨b, rfl⟩` from `hc`. Establish `h1 : a / b ^ 2 ∈ B`. Rewrite using `[← hker, map_div, map_pow, hca, div_self']`.

Establish `: a = a / b ^ 2 * b ^ 2` using `by simp`. Rewrite using `[this]`. Conclude with `Subgroup.mul_mem_sup h1 ((memS _).2 ⟨b, rfl⟩)`. Establish `e1 : (B ⊔ S).index = (sqs N).relIndex N`. Rewrite using `[hcomap, Subgroup.index_comap, hrange]`.

Establish `e2 : S.relIndex (B ⊔ S) * (B ⊔ S).index = S.index` using `Subgroup.relIndex_mul_index le_sup_right`. Establish `e3 : S.relIndex (B ⊔ S) = S.relIndex B` using `Subgroup.relIndex_sup_right B S`. Establish `hle : sqs B ≤ S ⊓ B`. Introduce `a ha`. Take `⟨y, hy, rfl⟩` from `(mem_sqs_iff_exists_sq _ _).1 ha`.

Conclude with `⟨(memS _).2 ⟨y, rfl⟩, pow_mem hy 2⟩`. Establish `e4 : (sqs B).relIndex (S ⊓ B) * (S ⊓ B).relIndex B = (sqs B).relIndex B` using `Subgroup.relIndex_mul_relIndex _ _ _ hle inf_le_right`. Establish `e5 : (S ⊓ B).relIndex B = S.relIndex B` using `Subgroup.inf_relIndex_right S B`. Establish `hεB : ε ∈ B` using `hσε`. Establish `key : ∀ y, y ^ 2 ∈ sqs B ↔ f y = 1`.

Introduce `y`. Rewrite using `[mem_sqs_iff_exists_sq, hker]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, hby⟩`. Establish `: (y / b) ^ 2 = 1` using `by rw [div_pow, hby, div_self']`.

Establish `hyb : y / b ∈ B`. Break down `h2 _ this with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `one_mem _`. Rewrite using `[h]`.

Conclude with `hεB`. Simplify using `using mul_mem hyb hb`. Introduce `hy`. Conclude with `⟨y, hy, rfl⟩`. Take `⟨a0, ha0⟩` from `h90 ε (by rw [hσε, ← sq, hε2])`.

Rewrite `ha0` using `[← hf]`. Establish `e6 : (sqs B).relIndex (S ⊓ B) = 2`. Rewrite using `[Subgroup.relIndex, Subgroup.index_eq_two_iff]`. Establish `h0 : a0 ^ 2 ∈ S ⊓ B` using `⟨(memS _).2 ⟨a0, rfl⟩, (hker _).1 (by rw [map_pow, ← ha0, hε2])⟩`. Use `⟨⟨a0 ^ 2, h0⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨x, hxS, hxB⟩`. Take `⟨y, rfl⟩` from `(memS x).1 hxS`. Establish `hy : f y ^ 2 = 1` using `by rw [← map_pow]; exact (hker _).2 hxB`. Simplify using `only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]`. Rewrite using `[← mul_pow, key, key, map_mul, ← ha0]`.

Break down `h2 _ hy with h | h` into its components or cases. Rewrite using `[h, one_mul]`. Conclude with `Or.inr ⟨rfl, hε1⟩`. Rewrite using `[h, ← sq]`. Conclude with `Or.inl ⟨hε2, hε1⟩`.

Rewrite using `[← e2, e1, e3, ← e4, e5, e6, mul_assoc]`.
-/
theorem two_mul_index_sqs_involution :
    ∀ (A : Type) [CommGroup A] (σ : A →* A) (ε : A), (∀ a, σ (σ a) = a) →
      (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → ε ≠ 1 → ε ^ 2 = 1 → σ ε = ε →
      (∀ a : A, a ^ 2 = 1 → a = 1 ∨ a = ε) →
      2 * (sqs (⊤ : Subgroup A)).index =
        (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) *
          (sqs (MonoidHom.id A * σ).ker).relIndex (MonoidHom.id A * σ).ker := by
  intro A _ σ ε hσ h90 hε1 hε2 hσε h2
  set B : Subgroup A := σ.eqLocus (MonoidHom.id A) with hB
  set N : Subgroup A := (MonoidHom.id A * σ).ker with hN
  set S : Subgroup A := sqs (⊤ : Subgroup A) with hS
  have memB : ∀ a, a ∈ B ↔ σ a = a := fun a => Iff.rfl
  have memN : ∀ a, a ∈ N ↔ a * σ a = 1 := fun a => Iff.rfl
  have memS : ∀ a, a ∈ S ↔ ∃ y, y ^ 2 = a := fun a => by
    rw [hS, mem_sqs_iff_exists_sq]; simp
  let f : A →* A := MonoidHom.id A / σ
  have hf : ∀ a, f a = a / σ a := fun a => rfl
  have hker : ∀ a, f a = 1 ↔ a ∈ B := fun a => by
    rw [hf, memB, div_eq_one, eq_comm]
  have hrange : f.range = N := by
    ext x
    rw [memN, MonoidHom.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      rw [hf, map_div, hσ]; simp
    · intro hx
      obtain ⟨b, hb⟩ := h90 x hx
      exact ⟨b, hb.symm⟩
  have hcomap : B ⊔ S = (sqs N).comap f := by
    apply le_antisymm
    · apply sup_le
      · intro a ha
        rw [Subgroup.mem_comap, (hker a).2 ha]
        exact one_mem _
      · intro a ha
        obtain ⟨y, rfl⟩ := (memS a).1 ha
        rw [Subgroup.mem_comap, mem_sqs_iff_exists_sq]
        exact ⟨f y, hrange ▸ ⟨y, rfl⟩, (map_pow f y 2).symm⟩
    · intro a ha
      rw [Subgroup.mem_comap, mem_sqs_iff_exists_sq] at ha
      obtain ⟨c, hc, hca⟩ := ha
      rw [← hrange] at hc
      obtain ⟨b, rfl⟩ := hc
      have h1 : a / b ^ 2 ∈ B := by
        rw [← hker, map_div, map_pow, hca, div_self']
      have : a = a / b ^ 2 * b ^ 2 := by simp
      rw [this]
      exact Subgroup.mul_mem_sup h1 ((memS _).2 ⟨b, rfl⟩)
  have e1 : (B ⊔ S).index = (sqs N).relIndex N := by
    rw [hcomap, Subgroup.index_comap, hrange]
  have e2 : S.relIndex (B ⊔ S) * (B ⊔ S).index = S.index :=
    Subgroup.relIndex_mul_index le_sup_right
  have e3 : S.relIndex (B ⊔ S) = S.relIndex B := Subgroup.relIndex_sup_right B S
  have hle : sqs B ≤ S ⊓ B := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := (mem_sqs_iff_exists_sq _ _).1 ha
    exact ⟨(memS _).2 ⟨y, rfl⟩, pow_mem hy 2⟩
  have e4 : (sqs B).relIndex (S ⊓ B) * (S ⊓ B).relIndex B = (sqs B).relIndex B :=
    Subgroup.relIndex_mul_relIndex _ _ _ hle inf_le_right
  have e5 : (S ⊓ B).relIndex B = S.relIndex B := Subgroup.inf_relIndex_right S B
  have hεB : ε ∈ B := hσε
  have key : ∀ y, y ^ 2 ∈ sqs B ↔ f y = 1 := by
    intro y
    rw [mem_sqs_iff_exists_sq, hker]
    constructor
    · rintro ⟨b, hb, hby⟩
      have : (y / b) ^ 2 = 1 := by rw [div_pow, hby, div_self']
      have hyb : y / b ∈ B := by
        rcases h2 _ this with h | h
        · rw [h]; exact one_mem _
        · rw [h]; exact hεB
      simpa using mul_mem hyb hb
    · intro hy
      exact ⟨y, hy, rfl⟩
  obtain ⟨a0, ha0⟩ := h90 ε (by rw [hσε, ← sq, hε2])
  rw [← hf] at ha0
  have e6 : (sqs B).relIndex (S ⊓ B) = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    have h0 : a0 ^ 2 ∈ S ⊓ B :=
      ⟨(memS _).2 ⟨a0, rfl⟩, (hker _).1 (by rw [map_pow, ← ha0, hε2])⟩
    refine ⟨⟨a0 ^ 2, h0⟩, ?_⟩
    rintro ⟨x, hxS, hxB⟩
    obtain ⟨y, rfl⟩ := (memS x).1 hxS
    have hy : f y ^ 2 = 1 := by rw [← map_pow]; exact (hker _).2 hxB
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rw [← mul_pow, key, key, map_mul, ← ha0]
    rcases h2 _ hy with h | h
    · rw [h, one_mul]
      exact Or.inr ⟨rfl, hε1⟩
    · rw [h, ← sq]
      exact Or.inl ⟨hε2, hε1⟩
  rw [← e2, e1, e3, ← e4, e5, e6, mul_assoc]

end GlobalTheory.QNorm
