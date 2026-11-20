import Mathlib
import GroundTheory.ProfiniteCohomology.CyclicCup
import GroundTheory.TateCohomology.InfRes
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits MonoidalCategory groupCohomology GroundTheory.GroupCoh

section Cyclicity

variable {G : Type} [Group G]

/- English proof (translation)
Use `Fintype.ofFinite G` as an intermediate fact. Use `set m := Fintype.card G with hmdef`. Break down `Nat.lt_or_ge m 2 with hm | hm` into its components or cases. Establish `: Subsingleton G` using `Fintype.card_le_one_iff_subsingleton.1 (by omega) infer_instance`. Establish `hk : ∀ x : G, ∃ k : ℕ, k < m ∧ ((((k : ℚ) / m : ℚ)) : AddCircle (1 : ℚ)) = χ (Additive.ofMul x)`.

Introduce `x`. Establish `hy01` using `reprIco_mem (χ (Additive.ofMul x))`. Establish `h0 : (((m : ℚ) * reprIco (χ (Additive.ofMul x)) : ℚ) : AddCircle (1 : ℚ)) = 0`. Rewrite using `[← nsmul_eq_mul, AddCircle.coe_nsmul, coe_reprIco, ← map_nsmul, ← ofMul_pow, pow_card_eq_one, ofMul_one, map_zero]`. Take `⟨n, hn⟩` from `(AddCircle.coe_eq_zero_iff _).1 h0`.

Rewrite `hn` using `[zsmul_one]`. Simplify using `only [Set.mem_Ico] at hy01`. Establish `hmpos : (0 : ℚ) < m` using `by exact_mod_cast (by omega : 0 < m)`. Establish `hn0 : 0 ≤ n`. Establish `: (0 : ℚ) ≤ n` using `by rw [hn]; exact mul_nonneg hmpos.le hy01.1`.

Conclude with `this` after adjusting the coercions. Establish `hnm : n < m`. Establish `: (n : ℚ) < m` using `by rw [hn]; nlinarith`. Conclude with `this` after adjusting the coercions. Use `⟨n.toNat, by omega, ?_⟩` and prove the remaining obligations.

Rewrite using `[← coe_reprIco (χ (Additive.ofMul x))]`. Use `congr 1`. Rewrite using `[show ((n.toNat : ℕ) : ℚ) = (n : ℚ) by exact_mod_cast Int.toNat_of_nonneg hn0, hn]`. Clear the denominators using the available nonvanishing facts. Use `choose k hkm hkeq using hk`.

Establish `hkinj : Function.Injective k`. Introduce `x x' h`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Apply `hχ` to reduce the goal to its premises. Rewrite using `[← hkeq x, ← hkeq x', h]`.

Establish `himage : Finset.univ.image k = Finset.range m`. Apply `Finset.eq_of_subset_of_card_le` to reduce the goal to its premises. Introduce `i hi`. Take `⟨x, -, rfl⟩` from `Finset.mem_image.1 hi`. Conclude with `Finset.mem_range.2 (hkm x)`.

Rewrite using `[Finset.card_range, Finset.card_image_of_injective _ hkinj, Finset.card_univ]`. Establish `h1 : 1 ∈ Finset.univ.image k`. Rewrite using `[himage]`. Conclude with `Finset.mem_range.2 (by omega)`. Take `⟨g, -, hg⟩` from `Finset.mem_image.1 h1`.

Establish `hχg` using `hkeq g`. Rewrite `hχg` using `[hg, Nat.cast_one]`. Establish `hord : orderOf g = m`. Rewrite using `[← addOrderOf_ofMul_eq_orderOf, ← addOrderOf_injective χ hχ, ← hχg]`. Conclude with `AddCircle.addOrderOf_period_div (p := (1 : ℚ)) (n := m) (by omega)`.

Conclude with `isCyclic_of_orderOf_eq_card g (by rw [hord, Nat.card_eq_fintype_card])`.
-/
theorem isCyclic_of_injective_char [Finite G] (χ : Additive G →+ AddCircle (1 : ℚ))
    (hχ : Function.Injective χ) : IsCyclic G := by
  classical
  have := Fintype.ofFinite G
  set m := Fintype.card G with hmdef
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have : Subsingleton G := Fintype.card_le_one_iff_subsingleton.1 (by omega)
    infer_instance
  have hk : ∀ x : G, ∃ k : ℕ, k < m ∧
      ((((k : ℚ) / m : ℚ)) : AddCircle (1 : ℚ)) = χ (Additive.ofMul x) := by
    intro x
    have hy01 := reprIco_mem (χ (Additive.ofMul x))
    have h0 : (((m : ℚ) * reprIco (χ (Additive.ofMul x)) : ℚ) : AddCircle (1 : ℚ)) = 0 := by
      rw [← nsmul_eq_mul, AddCircle.coe_nsmul, coe_reprIco, ← map_nsmul, ← ofMul_pow,
        pow_card_eq_one, ofMul_one, map_zero]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h0
    rw [zsmul_one] at hn
    simp only [Set.mem_Ico] at hy01
    have hmpos : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
    have hn0 : 0 ≤ n := by
      have : (0 : ℚ) ≤ n := by rw [hn]; exact mul_nonneg hmpos.le hy01.1
      exact_mod_cast this
    have hnm : n < m := by
      have : (n : ℚ) < m := by rw [hn]; nlinarith
      exact_mod_cast this
    refine ⟨n.toNat, by omega, ?_⟩
    rw [← coe_reprIco (χ (Additive.ofMul x))]
    congr 1
    rw [show ((n.toNat : ℕ) : ℚ) = (n : ℚ) by exact_mod_cast Int.toNat_of_nonneg hn0, hn]
    field_simp
  choose k hkm hkeq using hk
  have hkinj : Function.Injective k := by
    intro x x' h
    apply Additive.ofMul.injective
    apply hχ
    rw [← hkeq x, ← hkeq x', h]
  have himage : Finset.univ.image k = Finset.range m := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hi
      exact Finset.mem_range.2 (hkm x)
    · rw [Finset.card_range, Finset.card_image_of_injective _ hkinj, Finset.card_univ]
  have h1 : 1 ∈ Finset.univ.image k := by
    rw [himage]
    exact Finset.mem_range.2 (by omega)
  obtain ⟨g, -, hg⟩ := Finset.mem_image.1 h1
  have hχg := hkeq g
  rw [hg, Nat.cast_one] at hχg
  have hord : orderOf g = m := by
    rw [← addOrderOf_ofMul_eq_orderOf, ← addOrderOf_injective χ hχ, ← hχg]
    exact AddCircle.addOrderOf_period_div (p := (1 : ℚ)) (n := m) (by omega)
  exact isCyclic_of_orderOf_eq_card g (by rw [hord, Nat.card_eq_fintype_card])

end Cyclicity

section Kernel

variable {G : Type} [Group G]

def charComp (S : Subgroup G) [S.Normal] (ψ : Additive (G ⧸ S) →+ AddCircle (1 : ℚ)) :
    Additive G →+ AddCircle (1 : ℚ) :=
  ψ.comp (MonoidHom.toAdditive (QuotientGroup.mk' S))

def charKer (χ : Additive G →+ AddCircle (1 : ℚ)) : Subgroup G :=
  (AddMonoidHom.toMultiplicativeRight χ).ker

/- English proof (translation)
Rewrite using `[charKer, MonoidHom.mem_ker, AddMonoidHom.toMultiplicativeRight_apply_apply, ofAdd_eq_one]`.
-/
theorem mem_charKer {χ : Additive G →+ AddCircle (1 : ℚ)} {x : G} :
    x ∈ charKer χ ↔ χ (Additive.ofMul x) = 0 := by
  rw [charKer, MonoidHom.mem_ker, AddMonoidHom.toMultiplicativeRight_apply_apply, ofAdd_eq_one]

instance (χ : Additive G →+ AddCircle (1 : ℚ)) : (charKer χ).Normal :=
  MonoidHom.normal_ker _

def charBar (χ : Additive G →+ AddCircle (1 : ℚ)) :
    Additive (G ⧸ charKer χ) →+ AddCircle (1 : ℚ) :=
  MonoidHom.toAdditiveLeft (QuotientGroup.kerLift (AddMonoidHom.toMultiplicativeRight χ))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem charBar_apply (χ : Additive G →+ AddCircle (1 : ℚ)) (x : G) :
    charBar χ (Additive.ofMul (x : G ⧸ charKer χ)) = χ (Additive.ofMul x) :=
  rfl

/- English proof (translation)
Introduce `x y h`. Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `QuotientGroup.kerLift_injective (AddMonoidHom.toMultiplicativeRight χ)` to reduce the goal to its premises. Conclude with `congrArg Multiplicative.ofAdd h`.
-/
theorem charBar_injective (χ : Additive G →+ AddCircle (1 : ℚ)) :
    Function.Injective (charBar χ) := by
  intro x y h
  apply Additive.toMul.injective
  apply QuotientGroup.kerLift_injective (AddMonoidHom.toMultiplicativeRight χ)
  exact congrArg Multiplicative.ofAdd h

/- English proof (translation)
Use extensionality with `x`. Conclude with `charBar_apply χ (Additive.toMul x)`.
-/
theorem charComp_charBar (χ : Additive G →+ AddCircle (1 : ℚ)) :
    charComp (charKer χ) (charBar χ) = χ := by
  ext x
  exact charBar_apply χ (Additive.toMul x)

end Kernel

section Inflation

attribute [local instance 2000] Rep.hV2 Submodule.module Submodule.Quotient.module

variable {G : Type} [Group G] {A : Rep ℤ G} (S : Subgroup G) [S.Normal]

def invariantsToQuotient (a : A.ρ.invariants) : (A.quotientToInvariants S).ρ.invariants :=
  ⟨⟨a, fun s => a.2 s⟩, fun q => by
    induction q using QuotientGroup.induction_on with
    | H g => exact Subtype.ext (a.2 g)⟩

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_coe_invariantsToQuotient (a : A.ρ.invariants) :
    (invariantsToQuotient S a).1.1 = (a : A) :=
  rfl

end Inflation

end GroundTheory.ProfCoh
