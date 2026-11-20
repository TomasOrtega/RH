import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Establish `h1 : (nsmulAddMonoidHom (α` using `L × T) 2).range = ((nsmulAddMonoidHom (α := L) 2).range).prod (nsmulAddMonoidHom (α := T) 2).range := by`. Use extensionality with `⟨x, y⟩`. Simplify using `only [AddMonoidHom.mem_range, AddSubgroup.mem_prod, nsmulAddMonoidHom_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨a, b⟩, h⟩`.

Conclude with `⟨⟨a, congrArg Prod.fst h⟩, ⟨b, congrArg Prod.snd h⟩⟩`. Introduce and unpack `⟨⟨a, ha⟩, ⟨b, hb⟩⟩`. Conclude with `⟨(a, b), Prod.ext ha hb⟩`. Establish `h2 : (nsmulAddMonoidHom (α` using `L × T) 2).ker = (⊥ : AddSubgroup L).prod (nsmulAddMonoidHom (α := T) 2).ker := by`. Use extensionality with `⟨x, y⟩`.

Establish `hx : 2 • x = 0 ↔ x = 0`. Rewrite using `[← natCast_zsmul, smul_eq_zero]`. Simplify using the standard rewrite rules. Simplify using `[AddMonoidHom.mem_ker, AddSubgroup.mem_prod, hx]`. Establish `h3 : Module.finrank ℤ (L × T) = Module.finrank ℤ L`.

Establish `hT : Module.rank ℤ T = 0`. Rewrite using `[rank_eq_zero_iff]`. Introduce `x`. Use `⟨(Nat.card T : ℤ), by exact_mod_cast Nat.card_pos.ne', ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Establish `hq` using `Submodule.rank_quotient_add_rank (LinearMap.ker (LinearMap.fst ℤ L T))`. Establish `e1` using `(LinearMap.quotKerEquivOfSurjective (LinearMap.fst ℤ L T) LinearMap.fst_surjective).rank_eq`. Establish `e2 : Module.rank ℤ (LinearMap.ker (LinearMap.fst ℤ L T)) = 0`. Rewrite using `[LinearMap.ker_fst, rank_range_of_injective _ LinearMap.inr_injective, hT]`. Unfold `Module.finrank`.

Rewrite using `[← hq, e1, e2, add_zero]`. Establish `h4 : (nsmulAddMonoidHom (α` using `T) 2).range.index = Nat.card (nsmulAddMonoidHom (α := T) 2).ker := by`. Establish `a` using `AddSubgroup.card_mul_index (nsmulAddMonoidHom (α := T) 2).range`. Establish `b` using `AddSubgroup.card_mul_index (nsmulAddMonoidHom (α := T) 2).ker`. Rewrite `b` using `[AddSubgroup.index_ker]`.

Establish `hpos : 0 < Nat.card (nsmulAddMonoidHom (α` using `T) 2).range := Nat.card_pos`. Apply `Nat.eq_of_mul_eq_mul_left hpos` to reduce the goal to its premises. Rewrite using `[a, mul_comm, b]`. Rewrite using `[h1, h2, h3, AddSubgroup.index_prod, AddSubgroup.index_range_nsmul, h4, Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv, Nat.card_prod]`. Simplify using the standard rewrite rules.
-/
theorem index_double_prod (L T : Type) [AddCommGroup L] [AddCommGroup T] [Module.Free ℤ L]
    [Module.Finite ℤ L] [Finite T] :
    (nsmulAddMonoidHom (α := L × T) 2).range.index =
      2 ^ Module.finrank ℤ (L × T) * Nat.card (nsmulAddMonoidHom (α := L × T) 2).ker := by
  have h1 : (nsmulAddMonoidHom (α := L × T) 2).range =
      ((nsmulAddMonoidHom (α := L) 2).range).prod (nsmulAddMonoidHom (α := T) 2).range := by
    ext ⟨x, y⟩
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_prod, nsmulAddMonoidHom_apply]
    constructor
    · rintro ⟨⟨a, b⟩, h⟩
      exact ⟨⟨a, congrArg Prod.fst h⟩, ⟨b, congrArg Prod.snd h⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨(a, b), Prod.ext ha hb⟩
  have h2 : (nsmulAddMonoidHom (α := L × T) 2).ker =
      (⊥ : AddSubgroup L).prod (nsmulAddMonoidHom (α := T) 2).ker := by
    ext ⟨x, y⟩
    have hx : 2 • x = 0 ↔ x = 0 := by
      rw [← natCast_zsmul, smul_eq_zero]; simp
    simp [AddMonoidHom.mem_ker, AddSubgroup.mem_prod, hx]
  have h3 : Module.finrank ℤ (L × T) = Module.finrank ℤ L := by
    have hT : Module.rank ℤ T = 0 := by
      rw [rank_eq_zero_iff]
      intro x
      refine ⟨(Nat.card T : ℤ), by exact_mod_cast Nat.card_pos.ne', ?_⟩
      simp
    have hq := Submodule.rank_quotient_add_rank (LinearMap.ker (LinearMap.fst ℤ L T))
    have e1 := (LinearMap.quotKerEquivOfSurjective (LinearMap.fst ℤ L T)
      LinearMap.fst_surjective).rank_eq
    have e2 : Module.rank ℤ (LinearMap.ker (LinearMap.fst ℤ L T)) = 0 := by
      rw [LinearMap.ker_fst, rank_range_of_injective _ LinearMap.inr_injective, hT]
    unfold Module.finrank
    rw [← hq, e1, e2, add_zero]
  have h4 : (nsmulAddMonoidHom (α := T) 2).range.index =
      Nat.card (nsmulAddMonoidHom (α := T) 2).ker := by
    have a := AddSubgroup.card_mul_index (nsmulAddMonoidHom (α := T) 2).range
    have b := AddSubgroup.card_mul_index (nsmulAddMonoidHom (α := T) 2).ker
    rw [AddSubgroup.index_ker] at b
    have hpos : 0 < Nat.card (nsmulAddMonoidHom (α := T) 2).range := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [a, mul_comm, b]
  rw [h1, h2, h3, AddSubgroup.index_prod, AddSubgroup.index_range_nsmul, h4,
    Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
  simp

/- English proof (translation)
Take `⟨n, ι, _, p, hp, e, ⟨f⟩⟩` from `AddCommGroup.equiv_free_prod_directSum_zmod M`. Use `haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩`. Use `haveI : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) := Finite.of_equiv _ (DFinsupp.equivFunOnFintype).symm`. Establish `h` using `index_double_prod (Fin n →₀ ℤ) (DirectSum ι fun i => ZMod (p i ^ e i))`. Rewrite using `[← AddSubgroup.index_map_equiv _ f, AddEquiv.map_range_nsmulAddMonoidHom, h, f.toIntLinearEquiv.finrank_eq]`.

Use `congr 1`. Use `Nat.card_congr (f.toEquiv.subtypeEquiv ?_).symm` and prove the remaining obligations. Introduce `a`. Simplify using `only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]`. Express the relevant statement in the definitionally equal form `_ ↔ 2 • f a = 0`.

Rewrite using `[← map_nsmul, f.map_eq_zero_iff]`.
-/
theorem index_double_of_fg (M : Type) [AddCommGroup M] [AddGroup.FG M] :
    (nsmulAddMonoidHom (α := M) 2).range.index =
      2 ^ Module.finrank ℤ M * Nat.card (nsmulAddMonoidHom (α := M) 2).ker := by
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod M
  haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  haveI : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) :=
    Finite.of_equiv _ (DFinsupp.equivFunOnFintype).symm
  have h := index_double_prod (Fin n →₀ ℤ) (DirectSum ι fun i => ZMod (p i ^ e i))
  rw [← AddSubgroup.index_map_equiv _ f, AddEquiv.map_range_nsmulAddMonoidHom, h,
    f.toIntLinearEquiv.finrank_eq]
  congr 1
  refine Nat.card_congr (f.toEquiv.subtypeEquiv ?_).symm
  intro a
  simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
  change _ ↔ 2 • f a = 0
  rw [← map_nsmul, f.map_eq_zero_iff]

/- English proof (translation)
Introduce `G _ _`. Establish `h` using `index_double_of_fg (Additive G)`. Establish `h1 : (sqs (⊤ : Subgroup G)).toAddSubgroup = (nsmulAddMonoidHom (α` using `Additive G) 2).range := by`. Use extensionality with `x`. Simplify using `only [sqs, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, -, hy⟩`. Conclude with `⟨Additive.ofMul y, hy⟩`. Introduce and unpack `⟨y, hy⟩`. Conclude with `⟨Additive.toMul y, trivial, hy⟩`.

Rewrite using `[← Subgroup.index_toAddSubgroup, h1, h]`. Use `congr 1`.
-/
theorem index_sqs_top_of_fg : ∀ (G : Type) [CommGroup G] [Group.FG G],
    (sqs (⊤ : Subgroup G)).index =
      2 ^ Module.finrank ℤ (Additive G) * Nat.card {a : G // a ^ 2 = 1} := by
  intro G _ _
  have h := index_double_of_fg (Additive G)
  have h1 : (sqs (⊤ : Subgroup G)).toAddSubgroup =
      (nsmulAddMonoidHom (α := Additive G) 2).range := by
    ext x
    simp only [sqs, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
    constructor
    · rintro ⟨y, -, hy⟩
      exact ⟨Additive.ofMul y, hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨Additive.toMul y, trivial, hy⟩
  rw [← Subgroup.index_toAddSubgroup, h1, h]
  congr 1

end GlobalTheory.QNorm
