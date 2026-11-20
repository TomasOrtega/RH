import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsInvertibleIndexMulSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights

/- English proof (translation)
Apply `Module.finite_of_fg_torsion` to reduce the goal to its premises. Introduce `x`. Use `⟨⟨(ringChar Ω : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hp)⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Submonoid.smul_def]`. Use `ext`.

Simplify using `[zsmul_eq_mul]`.
-/
theorem InvertibleIndexCharP.finite_subring {Ω : Type} [Field Ω] (B : Subring Ω) (hp : ringChar Ω ≠ 0)
    (hB : Module.Finite ℤ B) : Finite B := by
  apply Module.finite_of_fg_torsion
  intro x
  refine ⟨⟨(ringChar Ω : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hp)⟩, ?_⟩
  rw [Submonoid.smul_def]
  ext
  simp [zsmul_eq_mul]

/- English proof (translation)
Introduce `Ω _ B X η _ f hp hB hX hf hloc`. Establish `hfin : Finite B` using `InvertibleIndexCharP.finite_subring B hp hB`. Establish `hfield : IsField B` using `Finite.isField_of_domain B`. Take `⟨m, hm⟩` from `Ideal.exists_maximal B`. Take `⟨i, ⟨b₀, hb₀m, hb₀X⟩, hgen⟩` from `hloc m hm`.

Establish `hunit : ∀ b : B, b ∉ m → ∃ b' : B, (b' : Ω) * b = 1`. Introduce `b hb`. Establish `hb0 : b ≠ 0` using `fun h => hb (h ▸ m.zero_mem)`. Take `⟨b', hb'⟩` from `hfield.mul_inv_cancel hb0`. Use `⟨b', ?_⟩` and prove the remaining obligations.

Use `congrArg Subtype.val hb'` as an intermediate fact. Simplify `this` using `[mul_comm]`. Establish `hXeq : (X : Set Ω) = (fun y => f i * y) '' (B : Set Ω)`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce `hz`. Take `⟨b, c, hbm, hbc⟩` from `hgen z hz`. Take `⟨b', hb'⟩` from `hunit b hbm`. Use `⟨((b' * c : B) : Ω), (b' * c).2, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Introduce and unpack `⟨y, hy, rfl⟩`. Take `⟨b', hb'⟩` from `hunit b₀ hb₀m`. Establish `hfX : f i ∈ X`. Use `hX b' b'.2 _ hb₀X` as an intermediate fact. Rewrite `this` using `[← mul_assoc, hb', one_mul]`. Then use the resulting hypothesis.

Use `hX y hy _ hfX` as an intermediate fact. Rewrite `this` using `[mul_comm]`. Conclude with `this`. Use `set A := B.toAddSubgroup with hA`. Establish `hAfin : Finite A` using `hfin`.

Establish `hXfin' : (X : Set Ω).Finite`. Rewrite using `[hXeq]`. Conclude with `(Set.toFinite (B : Set Ω)).image _`. Establish `hXfin : Finite X` using `hXfin'.to_subtype`. Establish `hcard : Nat.card X = Nat.card A`.

Establish `h` using `Nat.card_image_of_injective (mul_right_injective₀ (hf i)) (B : Set Ω)`. Rewrite `h` using `[← hXeq]`. Conclude with `h`. Establish `hc : Nat.card (A.addSubgroupOf X) = Nat.card (X.addSubgroupOf A)` using `Nat.card_congr { toFun := fun x => ⟨⟨x.1.1, AddSubgroup.mem_addSubgroupOf.1 x.2⟩, AddSubgroup.mem_addSubgroupOf.2 x.1.2⟩ invFun := fun x => ⟨⟨x.1.1, AddSubgroup.mem_addSubgroupOf.1 x.2⟩, AddSubgroup.mem_addSubgroupOf.2 x.1.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Establish `k1 : Nat.card (A.addSubgroupOf X) * A.relIndex X = Nat.card X` using `(A.addSubgroupOf X).card_mul_index`.

Establish `k2 : Nat.card (X.addSubgroupOf A) * X.relIndex A = Nat.card A` using `(X.addSubgroupOf A).card_mul_index`. Establish `hpos : 0 < Nat.card (A.addSubgroupOf X)` using `Nat.card_pos`. Establish `hApos : 0 < Nat.card A` using `Nat.card_pos`. Establish `heq : A.relIndex X = X.relIndex A`. Apply `Nat.eq_of_mul_eq_mul_left hpos` to reduce the goal to its premises.

Rewrite using `[k1, hc, k2, hcard]`. Establish `hne : X.relIndex A ≠ 0`. Introduce `h0`. Rewrite `k2` using `[h0, mul_zero]`. Use linear arithmetic over natural numbers and integers.

Unfold `genIndex`. Rewrite using `[heq]`. Conclude with `div_self (by exact_mod_cast hne)`.
-/
theorem InvertibleIndexCharP.proof : InvertibleIndexCharP.Statement := by
  intro Ω _ B X η _ f hp hB hX hf hloc
  have hfin : Finite B := InvertibleIndexCharP.finite_subring B hp hB
  have hfield : IsField B := Finite.isField_of_domain B
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  obtain ⟨i, ⟨b₀, hb₀m, hb₀X⟩, hgen⟩ := hloc m hm

  have hunit : ∀ b : B, b ∉ m → ∃ b' : B, (b' : Ω) * b = 1 := by
    intro b hb
    have hb0 : b ≠ 0 := fun h => hb (h ▸ m.zero_mem)
    obtain ⟨b', hb'⟩ := hfield.mul_inv_cancel hb0
    refine ⟨b', ?_⟩
    have := congrArg Subtype.val hb'
    simpa [mul_comm] using this

  have hXeq : (X : Set Ω) = (fun y => f i * y) '' (B : Set Ω) := by
    ext z
    constructor
    · intro hz
      obtain ⟨b, c, hbm, hbc⟩ := hgen z hz
      obtain ⟨b', hb'⟩ := hunit b hbm
      refine ⟨((b' * c : B) : Ω), (b' * c).2, ?_⟩
      calc f i * ((b' * c : B) : Ω) = b' * (c * f i) := by push_cast; ring
        _ = b' * (b * z) := by rw [hbc]
        _ = z := by rw [← mul_assoc, hb', one_mul]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨b', hb'⟩ := hunit b₀ hb₀m
      have hfX : f i ∈ X := by
        have := hX b' b'.2 _ hb₀X
        rwa [← mul_assoc, hb', one_mul] at this
      have := hX y hy _ hfX
      rw [mul_comm] at this
      exact this
  set A := B.toAddSubgroup with hA
  have hAfin : Finite A := hfin
  have hXfin' : (X : Set Ω).Finite := by
    rw [hXeq]; exact (Set.toFinite (B : Set Ω)).image _
  have hXfin : Finite X := hXfin'.to_subtype

  have hcard : Nat.card X = Nat.card A := by
    have h := Nat.card_image_of_injective (mul_right_injective₀ (hf i)) (B : Set Ω)
    rw [← hXeq] at h
    exact h
  have hc : Nat.card (A.addSubgroupOf X) = Nat.card (X.addSubgroupOf A) :=
    Nat.card_congr
      { toFun := fun x => ⟨⟨x.1.1, AddSubgroup.mem_addSubgroupOf.1 x.2⟩,
          AddSubgroup.mem_addSubgroupOf.2 x.1.2⟩
        invFun := fun x => ⟨⟨x.1.1, AddSubgroup.mem_addSubgroupOf.1 x.2⟩,
          AddSubgroup.mem_addSubgroupOf.2 x.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have k1 : Nat.card (A.addSubgroupOf X) * A.relIndex X = Nat.card X :=
    (A.addSubgroupOf X).card_mul_index
  have k2 : Nat.card (X.addSubgroupOf A) * X.relIndex A = Nat.card A :=
    (X.addSubgroupOf A).card_mul_index
  have hpos : 0 < Nat.card (A.addSubgroupOf X) := Nat.card_pos
  have hApos : 0 < Nat.card A := Nat.card_pos
  have heq : A.relIndex X = X.relIndex A := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [k1, hc, k2, hcard]
  have hne : X.relIndex A ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at k2
    omega
  unfold genIndex
  rw [heq]
  exact div_self (by exact_mod_cast hne)

end GroundTheory.Heights₂.Heights.Targets
