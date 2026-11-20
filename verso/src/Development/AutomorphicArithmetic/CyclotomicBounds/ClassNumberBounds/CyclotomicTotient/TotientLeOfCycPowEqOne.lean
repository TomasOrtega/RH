import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuInf

namespace KStar.Tree

open Polynomial IntermediateField in
/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective`. Use `haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance`. Establish `hl` using `(Fact.out : l.Prime)`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ k)`.

Establish `hint : IsIntegral E ζ` using `(hζ.isIntegral (pow_pos hl.pos k)).tower_top`. Use `set S : Finset ℤ_[l] := (Polynomial.nthRoots n (1 : ℤ_[l])).toFinset with hSdef`. Establish `hS : S.card ≤ n` using `(Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots n 1)`. Establish `hsub : ∀ r ∈ (minpoly E ζ).rootSet Ω, r ∈ S.image fun x => ζ ^ (PadicInt.toZModPow k x).val`. Introduce `r hr`.

Rewrite `hr` using `[Polynomial.mem_rootSet]`. Establish `hmin : minpoly E r = minpoly E ζ` using `(minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hr.2 (minpoly.monic hint)).symm`. Take `⟨g, hg⟩` from `(Normal.minpoly_eq_iff_mem_orbit Ω).1 hmin`. Establish `hspec` using `cyclotomicCharacter.spec l (MulSemiringAction.toRingAut Gal(Ω/E) Ω g) ζ hζ.pow_eq_one`. Rewrite using `[Finset.mem_image]`.

Use `⟨((cyc l E Ω g : ℤ_[l]ˣ) : ℤ_[l]), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hSdef, Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hn), ← Units.val_pow_eq_pow_val, h g, Units.val_one]`. Rewrite using `[← hg]`. Conclude with `hspec.symm`. Establish `hdeg : (minpoly E ζ).natDegree ≤ n`.

Rewrite using `[← Polynomial.card_rootSet_eq_natDegree (K := Ω) (minpoly.irreducible hint).separable (IsAlgClosed.splits ((minpoly E ζ).map (algebraMap E Ω)))]`. Combine the equalities or inequalities in the displayed calculation. Use `haveI : FiniteDimensional E E⟮ζ⟯ := IntermediateField.adjoin.finiteDimensional hint`. Use `haveI : FiniteDimensional ℚ E⟮ζ⟯ := Module.Finite.trans E E⟮ζ⟯`. Establish `hζF : IsPrimitiveRoot (⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩ : E⟮ζ⟯) (l ^ k)` using `IsPrimitiveRoot.of_map_of_injective (f := (E⟮ζ⟯).val) hζ Subtype.val_injective`.

Establish `hq : (l ^ k).totient ≤ Module.finrank ℚ E⟮ζ⟯`. Rewrite using `[← Polynomial.natDegree_cyclotomic (l ^ k) ℚ, Polynomial.cyclotomic_eq_minpoly_rat hζF (pow_pos hl.pos k)]`. Conclude with `minpoly.natDegree_le _`. Combine the equalities or inequalities in the displayed calculation. Apply `Nat.mul_le_mul_left` to reduce the goal to its premises.

Rewrite using `[IntermediateField.adjoin.finrank hint]`. Conclude with `hdeg`.
-/
private theorem totient_le_of_cyc_pow_eq_one (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ) (hn : n ≠ 0) (h : ∀ g : Ω ≃ₐ[E] Ω, cyc l E Ω g ^ n = 1) (k : ℕ) :
    Nat.totient (l ^ k) ≤ Module.finrank ℚ E * n := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have hl := (Fact.out : l.Prime)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ k)
  have hint : IsIntegral E ζ := (hζ.isIntegral (pow_pos hl.pos k)).tower_top
  set S : Finset ℤ_[l] := (Polynomial.nthRoots n (1 : ℤ_[l])).toFinset with hSdef
  have hS : S.card ≤ n := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots n 1)
  have hsub : ∀ r ∈ (minpoly E ζ).rootSet Ω, r ∈ S.image fun x => ζ ^ (PadicInt.toZModPow k x).val := by
    intro r hr
    rw [Polynomial.mem_rootSet] at hr
    have hmin : minpoly E r = minpoly E ζ :=
      (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hr.2 (minpoly.monic hint)).symm
    obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit Ω).1 hmin
    have hspec := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut Gal(Ω/E) Ω g) ζ hζ.pow_eq_one
    rw [Finset.mem_image]
    refine ⟨((cyc l E Ω g : ℤ_[l]ˣ) : ℤ_[l]), ?_, ?_⟩
    · rw [hSdef, Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hn),
        ← Units.val_pow_eq_pow_val, h g, Units.val_one]
    · rw [← hg]
      exact hspec.symm
  have hdeg : (minpoly E ζ).natDegree ≤ n := by
    rw [← Polynomial.card_rootSet_eq_natDegree (K := Ω) (minpoly.irreducible hint).separable
      (IsAlgClosed.splits ((minpoly E ζ).map (algebraMap E Ω)))]
    calc Fintype.card ((minpoly E ζ).rootSet Ω) = ((minpoly E ζ).rootSet Ω).toFinset.card :=
          (Set.toFinset_card _).symm
      _ ≤ (S.image fun x => ζ ^ (PadicInt.toZModPow k x).val).card :=
          Finset.card_le_card fun x hx => hsub x (Set.mem_toFinset.1 hx)
      _ ≤ S.card := Finset.card_image_le
      _ ≤ n := hS
  haveI : FiniteDimensional E E⟮ζ⟯ := IntermediateField.adjoin.finiteDimensional hint
  haveI : FiniteDimensional ℚ E⟮ζ⟯ := Module.Finite.trans E E⟮ζ⟯
  have hζF : IsPrimitiveRoot (⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩ : E⟮ζ⟯) (l ^ k) :=
    IsPrimitiveRoot.of_map_of_injective (f := (E⟮ζ⟯).val) hζ Subtype.val_injective
  have hq : (l ^ k).totient ≤ Module.finrank ℚ E⟮ζ⟯ := by
    rw [← Polynomial.natDegree_cyclotomic (l ^ k) ℚ,
      Polynomial.cyclotomic_eq_minpoly_rat hζF (pow_pos hl.pos k)]
    exact minpoly.natDegree_le _
  calc (l ^ k).totient ≤ Module.finrank ℚ E⟮ζ⟯ := hq
    _ = Module.finrank ℚ E * Module.finrank E E⟮ζ⟯ := (Module.finrank_mul_finrank ℚ E E⟮ζ⟯).symm
    _ ≤ Module.finrank ℚ E * n := by
        apply Nat.mul_le_mul_left
        rw [IntermediateField.adjoin.finrank hint]
        exact hdeg

/- English proof (translation)
Establish `hl` using `(Fact.out : l.Prime)`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `key` using `totient_le_of_cyc_pow_eq_one l E Ω n hn hne (Module.finrank ℚ E * n + 1)`. Rewrite `key` using `[Nat.totient_prime_pow_succ hl]`.

Establish `h1 : Module.finrank ℚ E * n < l ^ (Module.finrank ℚ E * n)` using `Nat.lt_pow_self hl.one_lt`. Establish `h2 : l ^ (Module.finrank ℚ E * n) ≤ l ^ (Module.finrank ℚ E * n) * (l - 1)` using `Nat.le_mul_of_pos_right _ (Nat.sub_pos_of_lt hl.one_lt)`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_cyc_pow_ne_one (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (n : ℕ) (hn : n ≠ 0) : ∃ g : Ω ≃ₐ[E] Ω, cyc l E Ω g ^ n ≠ 1 := by
  have hl := (Fact.out : l.Prime)
  by_contra hne
  push_neg at hne
  have key := totient_le_of_cyc_pow_eq_one l E Ω n hn hne (Module.finrank ℚ E * n + 1)
  rw [Nat.totient_prime_pow_succ hl] at key
  have h1 : Module.finrank ℚ E * n < l ^ (Module.finrank ℚ E * n) := Nat.lt_pow_self hl.one_lt
  have h2 : l ^ (Module.finrank ℚ E * n) ≤ l ^ (Module.finrank ℚ E * n) * (l - 1) :=
    Nat.le_mul_of_pos_right _ (Nat.sub_pos_of_lt hl.one_lt)
  omega

end KStar.Tree
