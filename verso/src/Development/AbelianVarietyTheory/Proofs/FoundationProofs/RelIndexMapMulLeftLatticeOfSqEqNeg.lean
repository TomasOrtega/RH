import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `L α N hN hα hL`. Establish `hα0 : α ≠ 0`. Introduce and unpack `rfl`. Establish `: (N : ℂ) = 0` using `by simpa using hα`. Conclude with `hN.ne' (by exact_mod_cast this)`.

Establish `hinj : Function.Injective (AddMonoidHom.mulLeft α)` using `mul_right_injective₀ hα0`. Use `set A := L.lattice.toAddSubgroup with hA`. Use `set f := AddMonoidHom.mulLeft α with hf`. Establish `h1 : A.map f ≤ A`. Introduce and unpack `_ ⟨l, hl, rfl⟩`.

Conclude with `hL l hl`. Establish `h2 : (A.map f).map f ≤ A.map f` using `AddSubgroup.map_mono h1`. Establish `hmul` using `AddSubgroup.relIndex_mul_relIndex _ _ _ h2 h1`. Rewrite `hmul` using `[AddSubgroup.relIndex_map_map_of_injective _ _ hinj]`. Establish `hr : Module.finrank ℤ L.lattice = 2`.

Simplify using `using Module.finrank_eq_card_basis L.latticeBasis`. Establish `hidx : ((A.map f).map f).relIndex A = N ^ 2`. Rewrite using `[← hr, ← AddSubgroup.index_range_nsmul, AddSubgroup.relIndex]`. Use `congr 1`. Use extensionality with `x`.

Rewrite using `[AddSubgroup.mem_addSubgroupOf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨l, hl, rfl⟩, hx⟩`. Use `⟨⟨-l, L.lattice.neg_mem hl⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Establish `hx' : α * (α * l) = (x : ℂ)` using `hx`.

Use `show N • (-l) = (x : ℂ)`. Rewrite using `[← hx', nsmul_eq_mul]`. Take the linear combination `(-l) * hα`. Introduce and unpack `⟨l, hx⟩`. Establish `hx' : N • (l : ℂ) = (x : ℂ)` using `congrArg Subtype.val hx`.

Use `⟨_, ⟨-(l : ℂ), L.lattice.neg_mem l.2, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show α * (α * -(l : ℂ)) = (x : ℂ)`. Rewrite using `[← hx', nsmul_eq_mul]`. Take the linear combination `(-(l : ℂ)) * hα`. Rewrite `hmul` using `[hidx, ← sq]`.

Conclude with `Nat.pow_left_injective two_ne_zero hmul`.
-/
theorem relIndex_map_mulLeft_lattice_of_sq_eq_neg :
    ∀ (L : PeriodPair) (α : ℂ) (N : ℕ), 0 < N → α ^ 2 = -(N : ℂ) →
      (∀ l ∈ L.lattice, α * l ∈ L.lattice) →
      (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex L.lattice.toAddSubgroup
        = N := by
  intro L α N hN hα hL
  have hα0 : α ≠ 0 := by
    rintro rfl
    have : (N : ℂ) = 0 := by simpa using hα
    exact hN.ne' (by exact_mod_cast this)
  have hinj : Function.Injective (AddMonoidHom.mulLeft α) := mul_right_injective₀ hα0
  set A := L.lattice.toAddSubgroup with hA
  set f := AddMonoidHom.mulLeft α with hf
  have h1 : A.map f ≤ A := by
    rintro _ ⟨l, hl, rfl⟩
    exact hL l hl
  have h2 : (A.map f).map f ≤ A.map f := AddSubgroup.map_mono h1
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ h2 h1
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hinj] at hmul
  have hr : Module.finrank ℤ L.lattice = 2 := by
    simpa using Module.finrank_eq_card_basis L.latticeBasis
  have hidx : ((A.map f).map f).relIndex A = N ^ 2 := by
    rw [← hr, ← AddSubgroup.index_range_nsmul, AddSubgroup.relIndex]
    congr 1
    ext x
    rw [AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, hx⟩
      refine ⟨⟨-l, L.lattice.neg_mem hl⟩, Subtype.ext ?_⟩
      have hx' : α * (α * l) = (x : ℂ) := hx
      show N • (-l) = (x : ℂ)
      rw [← hx', nsmul_eq_mul]
      linear_combination (-l) * hα
    · rintro ⟨l, hx⟩
      have hx' : N • (l : ℂ) = (x : ℂ) := congrArg Subtype.val hx
      refine ⟨_, ⟨-(l : ℂ), L.lattice.neg_mem l.2, rfl⟩, ?_⟩
      show α * (α * -(l : ℂ)) = (x : ℂ)
      rw [← hx', nsmul_eq_mul]
      linear_combination (-(l : ℂ)) * hα
  rw [hidx, ← sq] at hmul
  exact Nat.pow_left_injective two_ne_zero hmul

end GlobalTheory
