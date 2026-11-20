import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsVectorOrbits

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

/- English proof (translation)
Introduce `A B hB hAB C`. Establish `: Module.Finite ℤ B` using `Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg B).mpr hB)`. Establish `: Module.Finite ℤ A` using `Module.Finite.of_injective (AddSubgroup.inclusion hAB).toIntLinearMap (AddSubgroup.inclusion_injective hAB)`. Use `set n := C.factorial with hn`. Set `K : AddSubgroup A` to `(nsmulAddMonoidHom n : A →+ A).range`.

Establish `: Module.Finite ℤ (A ⧸ K)` using `Module.Finite.of_surjective (QuotientAddGroup.mk' K).toIntLinearMap (QuotientAddGroup.mk'_surjective K)`. Establish `htors : Module.IsTorsion ℤ (A ⧸ K)`. Introduce `x`. Use `⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (Nat.factorial_pos C).ne')⟩, ?_⟩` and prove the remaining obligations. Proceed by induction on `x using QuotientAddGroup.induction_on with`.

Consider the case `H a => show (n : ℤ) • (QuotientAddGroup.mk a : A ⧸ K) = 0`. Rewrite using `[← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, natCast_zsmul]`. Conclude with `⟨a, rfl⟩`. Establish `: Finite (A ⧸ K)` using `Module.finite_of_fg_torsion _ htors`. Establish `hK : ∀ H ∈ {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C}, K ≤ H.addSubgroupOf A`.

Introduce and unpack `H ⟨-, h0, hC⟩ _ ⟨a, rfl⟩`. Take `⟨k, hk⟩` from `Nat.dvd_factorial (Nat.pos_of_ne_zero h0) hC`. Rewrite using `[AddSubgroup.mem_addSubgroupOf]`. Use `show n • (a : G) ∈ H`. Rewrite using `[hn, hk, mul_nsmul]`.

Conclude with `H.nsmul_mem (H.nsmul_relIndex_mem a.2) k`. Use `Set.Finite.of_finite_image (f := fun H : AddSubgroup G => (QuotientAddGroup.mk '' ((H.addSubgroupOf A : AddSubgroup A) : Set A) : Set (A ⧸ K))) (Set.toFinite _) ?_` and prove the remaining obligations. Establish `key : ∀ H₁ ∈ {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C}, ∀ H₂ ∈ {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C}, (QuotientAddGroup.mk '' ((H₁.addSubgroupOf A : AddSubgroup A) : Set A) : Set (A ⧸ K)) = QuotientAddGroup.mk '' ((H₂.addSubgrou …`. Introduce `H₁ h₁ H₂ h₂ he x hx`. Establish `hxA : x ∈ A` using `h₁.1 hx`.

Establish `hmem : (QuotientAddGroup.mk (⟨x, hxA⟩ : A) : A ⧸ K) ∈ QuotientAddGroup.mk '' ((H₁.addSubgroupOf A : AddSubgroup A) : Set A)` using `⟨⟨x, hxA⟩, AddSubgroup.mem_addSubgroupOf.mpr hx, rfl⟩`. Rewrite `hmem` using `[he]`. Take `⟨y, hy, hyx⟩` from `hmem`. Establish `hd : -y + ⟨x, hxA⟩ ∈ H₂.addSubgroupOf A` using `hK H₂ h₂ (QuotientAddGroup.eq.mp hyx)`. Establish `: (⟨x, hxA⟩ : A) ∈ H₂.addSubgroupOf A`.

Simplify using `using (H₂.addSubgroupOf A).add_mem hy hd`. Conclude with `AddSubgroup.mem_addSubgroupOf.mp this`. Conclude with `fun H₁ h₁ H₂ h₂ he => le_antisymm (key H₁ h₁ H₂ h₂ he) (key H₂ h₂ H₁ h₁ he.symm)`.
-/
theorem BoundedIndexSubgroupsFinite.proof (G : Type*) [AddCommGroup G] :
    BoundedIndexSubgroupsFinite.Statement G := by
  intro A B hB hAB C
  classical

  have : Module.Finite ℤ B :=
    Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg B).mpr hB)
  have : Module.Finite ℤ A :=
    Module.Finite.of_injective (AddSubgroup.inclusion hAB).toIntLinearMap
      (AddSubgroup.inclusion_injective hAB)

  set n := C.factorial with hn
  let K : AddSubgroup A := (nsmulAddMonoidHom n : A →+ A).range

  have : Module.Finite ℤ (A ⧸ K) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' K).toIntLinearMap
      (QuotientAddGroup.mk'_surjective K)
  have htors : Module.IsTorsion ℤ (A ⧸ K) := by
    intro x
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (Nat.factorial_pos C).ne')⟩, ?_⟩
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      show (n : ℤ) • (QuotientAddGroup.mk a : A ⧸ K) = 0
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, natCast_zsmul]
      exact ⟨a, rfl⟩
  have : Finite (A ⧸ K) := Module.finite_of_fg_torsion _ htors

  have hK : ∀ H ∈ {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C},
      K ≤ H.addSubgroupOf A := by
    rintro H ⟨-, h0, hC⟩ _ ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero h0) hC
    rw [AddSubgroup.mem_addSubgroupOf]
    show n • (a : G) ∈ H
    rw [hn, hk, mul_nsmul]
    exact H.nsmul_mem (H.nsmul_relIndex_mem a.2) k

  refine Set.Finite.of_finite_image (f := fun H : AddSubgroup G =>
    (QuotientAddGroup.mk '' ((H.addSubgroupOf A : AddSubgroup A) : Set A) : Set (A ⧸ K)))
    (Set.toFinite _) ?_
  have key : ∀ H₁ ∈ {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C},
      ∀ H₂ ∈ {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C},
      (QuotientAddGroup.mk '' ((H₁.addSubgroupOf A : AddSubgroup A) : Set A) : Set (A ⧸ K)) =
        QuotientAddGroup.mk '' ((H₂.addSubgroupOf A : AddSubgroup A) : Set A) → H₁ ≤ H₂ := by
    intro H₁ h₁ H₂ h₂ he x hx
    have hxA : x ∈ A := h₁.1 hx
    have hmem : (QuotientAddGroup.mk (⟨x, hxA⟩ : A) : A ⧸ K) ∈
        QuotientAddGroup.mk '' ((H₁.addSubgroupOf A : AddSubgroup A) : Set A) :=
      ⟨⟨x, hxA⟩, AddSubgroup.mem_addSubgroupOf.mpr hx, rfl⟩
    rw [he] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hd : -y + ⟨x, hxA⟩ ∈ H₂.addSubgroupOf A := hK H₂ h₂ (QuotientAddGroup.eq.mp hyx)
    have : (⟨x, hxA⟩ : A) ∈ H₂.addSubgroupOf A := by
      simpa using (H₂.addSubgroupOf A).add_mem hy hd
    exact AddSubgroup.mem_addSubgroupOf.mp this
  exact fun H₁ h₁ H₂ h₂ he => le_antisymm (key H₁ h₁ H₂ h₂ he) (key H₂ h₂ H₁ h₁ he.symm)

end GroundTheory.Heights₂.Heights.FiniteCovolume
