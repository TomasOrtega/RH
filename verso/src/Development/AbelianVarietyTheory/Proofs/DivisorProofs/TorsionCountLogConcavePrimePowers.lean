import Mathlib
open NumberField

namespace GlobalTheory

def killedBy {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (I : Ideal R) :
    AddSubgroup M where
  carrier := {x | ∀ a ∈ I, a • x = 0}
  zero_mem' := fun a _ => smul_zero a
  add_mem' := fun hx hy a ha => by rw [smul_add, hx a ha, hy a ha, add_zero]
  neg_mem' := fun hx a ha => by rw [smul_neg, hx a ha, neg_zero]

/- English proof (translation)
Introduce `_ hx a ha` and use `hx a (h ha)`.
-/
theorem killedBy_anti {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    {I J : Ideal R} (h : I ≤ J) : killedBy M J ≤ killedBy M I :=
  fun _ hx a ha => hx a (h ha)

/- English proof (translation)
Rewrite using `[← AddSubgroup.index_ker, AddSubgroup.card_mul_index]`.
-/
theorem card_eq_card_ker_mul_card_range {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) : Nat.card G = Nat.card f.ker * Nat.card f.range := by
  rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]

/- English proof (translation)
Introduce `F _ _ M _ _ 𝔭 hmax k hfin`. Establish `hp0 : 𝔭 ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hmax (RingOfIntegers.not_isField F)`. Establish `hp2 : 𝔭 ^ 2 ≠ ⊥` using `pow_ne_zero 2 hp0`. Take `⟨a, ha⟩` from `IsDedekindDomain.exists_sup_span_eq (Ideal.pow_le_self two_ne_zero : 𝔭 ^ 2 ≤ 𝔭) hp2`. Establish `haP : a ∈ 𝔭` using `ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)`.

Establish `key : 𝔭 ^ (k + 2) ⊔ 𝔭 ^ k * Ideal.span {a} = 𝔭 ^ (k + 1)`. Establish `e : 𝔭 ^ (k + 1) = 𝔭 ^ k * (𝔭 ^ 2 ⊔ Ideal.span {a})` using `by rw [ha, pow_succ]`. Rewrite using `[e, Ideal.mul_sup, ← pow_add]`. Use `set A := killedBy M (𝔭 ^ (k + 2)) with hA`. Use `set B := killedBy M (𝔭 ^ (k + 1)) with hB`.

Use `set C := killedBy M (𝔭 ^ k) with hC`. Establish `eA : Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 2), a • x = 0} = Nat.card A` using `rfl`. Establish `eB : Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 1), a • x = 0} = Nat.card B` using `rfl`. Establish `eC : Nat.card {x : M // ∀ a ∈ 𝔭 ^ k, a • x = 0} = Nat.card C` using `rfl`. Rewrite using `[eA, eB, eC]`.

Establish `hBA : B ≤ A` using `killedBy_anti M (Ideal.pow_le_pow_right (by omega))`. Establish `hCB : C ≤ B` using `killedBy_anti M (Ideal.pow_le_pow_right (by omega))`. Use `haveI : Finite A := hfin`. Use `haveI : Finite B := Finite.of_injective _ (AddSubgroup.inclusion_injective hBA)`. Establish `hAB : ∀ x ∈ A, a • x ∈ B`.

Introduce `x hx b hb`. Rewrite using `[← mul_smul]`. Apply `hx` to reduce the goal to its premises. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul hb haP`.

Establish `hiff : ∀ x ∈ A, (a • x ∈ C ↔ x ∈ B)`. Introduce `x hx`. Prove the components needed by the constructor for the conclusion. Introduce `hax`. Establish `hle : 𝔭 ^ (k + 1) ≤ LinearMap.ker (LinearMap.toSpanSingleton (𝓞 F) M x)`.

Rewrite using `[← key]`. Apply `sup_le` to reduce the goal to its premises. Introduce `b hb`. Simplify using `using hx b hb`. Rewrite using `[Ideal.mul_le]`.

Introduce `r hr s hs`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hs`. Simplify using `only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]`. Rewrite using `[← mul_assoc, mul_smul]`. Conclude with `hax _ (Ideal.mul_mem_right c _ hr)`.

Introduce `b hb`. Simplify using `using hle hb`. Introduce `hxB b hb`. Rewrite using `[← mul_smul]`. Apply `hxB` to reduce the goal to its premises.

Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul hb haP`. Set `π : M →+ M ⧸ C` to `QuotientAddGroup.mk' C`. Set `g : A →+ M ⧸ C` to `(π.comp (DistribMulAction.toAddMonoidHom M a)).comp A.subtype`. Set `h : B →+ M ⧸ C` to `π.comp B.subtype`.

Establish `hg : Nat.card g.ker = Nat.card B`. Establish `: g.ker = B.addSubgroupOf A`. Use extensionality with `x`. Simplify using `only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, g, π, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, DistribMulAction.toAddMonoidHom_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]`. Conclude with `hiff x.1 x.2`.

Rewrite using `[this]`. Conclude with `Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hBA).toEquiv`. Establish `hh : Nat.card h.ker = Nat.card C`. Establish `: h.ker = C.addSubgroupOf B`. Use extensionality with `x`.

Simplify using `only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, h, π, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]`. Rewrite using `[this]`. Conclude with `Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hCB).toEquiv`. Establish `hrange : g.range ≤ h.range`. Introduce and unpack `_ ⟨x, rfl⟩`.

Conclude with `⟨⟨a • (x : M), hAB x.1 x.2⟩, rfl⟩`. Use `haveI : Finite h.range := Finite.of_surjective _ h.rangeRestrict_surjective`. Establish `hcard : Nat.card g.range ≤ Nat.card h.range` using `Nat.card_le_card_of_injective _ (AddSubgroup.inclusion_injective hrange)`. Establish `e1` using `card_eq_card_ker_mul_card_range g`. Establish `e2` using `card_eq_card_ker_mul_card_range h`.

Rewrite `e1` using `[hg]`. Rewrite `e2` using `[hh]`. Rewrite using `[e1, sq]`. Use `nth_rewrite 3 [e2]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_torsion_pow_log_concave : ∀ (F : Type) [Field F] [NumberField F] (M : Type)
    [AddCommGroup M] [Module (𝓞 F) M] (𝔭 : Ideal (𝓞 F)), 𝔭.IsMaximal → ∀ k : ℕ,
    Finite {x : M // ∀ a ∈ 𝔭 ^ (k + 2), a • x = 0} →
    Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 2), a • x = 0} * Nat.card {x : M // ∀ a ∈ 𝔭 ^ k, a • x = 0} ≤
      Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 1), a • x = 0} ^ 2 := by
  intro F _ _ M _ _ 𝔭 hmax k hfin
  have hp0 : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hmax (RingOfIntegers.not_isField F)
  have hp2 : 𝔭 ^ 2 ≠ ⊥ := pow_ne_zero 2 hp0
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.pow_le_self two_ne_zero : 𝔭 ^ 2 ≤ 𝔭) hp2
  have haP : a ∈ 𝔭 := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  have key : 𝔭 ^ (k + 2) ⊔ 𝔭 ^ k * Ideal.span {a} = 𝔭 ^ (k + 1) := by
    have e : 𝔭 ^ (k + 1) = 𝔭 ^ k * (𝔭 ^ 2 ⊔ Ideal.span {a}) := by rw [ha, pow_succ]
    rw [e, Ideal.mul_sup, ← pow_add]
  set A := killedBy M (𝔭 ^ (k + 2)) with hA
  set B := killedBy M (𝔭 ^ (k + 1)) with hB
  set C := killedBy M (𝔭 ^ k) with hC
  have eA : Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 2), a • x = 0} = Nat.card A := rfl
  have eB : Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 1), a • x = 0} = Nat.card B := rfl
  have eC : Nat.card {x : M // ∀ a ∈ 𝔭 ^ k, a • x = 0} = Nat.card C := rfl
  rw [eA, eB, eC]
  have hBA : B ≤ A := killedBy_anti M (Ideal.pow_le_pow_right (by omega))
  have hCB : C ≤ B := killedBy_anti M (Ideal.pow_le_pow_right (by omega))
  haveI : Finite A := hfin
  haveI : Finite B := Finite.of_injective _ (AddSubgroup.inclusion_injective hBA)

  have hAB : ∀ x ∈ A, a • x ∈ B := by
    intro x hx b hb
    rw [← mul_smul]
    apply hx
    rw [pow_succ]
    exact Ideal.mul_mem_mul hb haP

  have hiff : ∀ x ∈ A, (a • x ∈ C ↔ x ∈ B) := by
    intro x hx
    constructor
    · intro hax
      have hle : 𝔭 ^ (k + 1) ≤ LinearMap.ker (LinearMap.toSpanSingleton (𝓞 F) M x) := by
        rw [← key]
        apply sup_le
        · intro b hb
          simpa using hx b hb
        · rw [Ideal.mul_le]
          intro r hr s hs
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hs
          simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
          rw [← mul_assoc, mul_smul]
          exact hax _ (Ideal.mul_mem_right c _ hr)
      intro b hb
      simpa using hle hb
    · intro hxB b hb
      rw [← mul_smul]
      apply hxB
      rw [pow_succ]
      exact Ideal.mul_mem_mul hb haP
  let π : M →+ M ⧸ C := QuotientAddGroup.mk' C
  let g : A →+ M ⧸ C := (π.comp (DistribMulAction.toAddMonoidHom M a)).comp A.subtype
  let h : B →+ M ⧸ C := π.comp B.subtype
  have hg : Nat.card g.ker = Nat.card B := by
    have : g.ker = B.addSubgroupOf A := by
      ext x
      simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, g, π,
        AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, DistribMulAction.toAddMonoidHom_apply,
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      exact hiff x.1 x.2
    rw [this]
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hBA).toEquiv
  have hh : Nat.card h.ker = Nat.card C := by
    have : h.ker = C.addSubgroupOf B := by
      ext x
      simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, h, π,
        AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    rw [this]
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hCB).toEquiv
  have hrange : g.range ≤ h.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨a • (x : M), hAB x.1 x.2⟩, rfl⟩
  haveI : Finite h.range := Finite.of_surjective _ h.rangeRestrict_surjective
  have hcard : Nat.card g.range ≤ Nat.card h.range :=
    Nat.card_le_card_of_injective _ (AddSubgroup.inclusion_injective hrange)
  have e1 := card_eq_card_ker_mul_card_range g
  have e2 := card_eq_card_ker_mul_card_range h
  rw [hg] at e1
  rw [hh] at e2
  rw [e1, sq]
  nth_rewrite 3 [e2]
  calc Nat.card B * Nat.card g.range * Nat.card C
      ≤ Nat.card B * Nat.card h.range * Nat.card C := by gcongr
    _ = Nat.card B * (Nat.card C * Nat.card h.range) := by ring

end GlobalTheory
