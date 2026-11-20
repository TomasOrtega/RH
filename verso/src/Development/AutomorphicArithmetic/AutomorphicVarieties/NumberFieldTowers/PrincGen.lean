import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.EqOneOfMemPrincOne
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.NuFormula
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Generate
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.UnitsMapSurjOfZmod
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.EmultiplicityPowSubOneOdd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

/- English proof (translation)
Establish `hp : Prime (l : ℕ)` using `(Fact.out : l.Prime).prime`. Distinguish the cases in `hl : l = 2`. Establish `hc : 2 ≤ c` using `h2 hl`. Establish `hd2 : (l : ℤ_[l]) ^ 2 ∣ u - 1` using `(pow_dvd_pow _ hc).trans hd`. Rewrite using `[KStar.TotallyRealRoots.emultiplicity_pow_sub_one_sq hd2, emultiplicity_pow_self_of_prime hp]`.

Establish `hd1 : (l : ℤ_[l]) ∣ u - 1` using `(dvd_pow_self _ (by omega)).trans hd`. Rewrite using `[KStar.TotallyRealRoots.emultiplicity_pow_sub_one_odd hl hd1, emultiplicity_pow_self_of_prime hp]`.
-/
private theorem pg_emult {l : ℕ} [Fact l.Prime] {c : ℕ} (h1 : 1 ≤ c) (h2 : l = 2 → 2 ≤ c) {u : ℤ_[l]}
    (hd : (l : ℤ_[l]) ^ c ∣ u - 1) (n : ℕ) :
    emultiplicity (l : ℤ_[l]) (u ^ l ^ n - 1) = emultiplicity (l : ℤ_[l]) (u - 1) + n := by
  have hp : Prime (l : ℕ) := (Fact.out : l.Prime).prime
  by_cases hl : l = 2
  · have hc : 2 ≤ c := h2 hl
    have hd2 : (l : ℤ_[l]) ^ 2 ∣ u - 1 := (pow_dvd_pow _ hc).trans hd
    rw [KStar.TotallyRealRoots.emultiplicity_pow_sub_one_sq hd2, emultiplicity_pow_self_of_prime hp]
  · have hd1 : (l : ℤ_[l]) ∣ u - 1 := (dvd_pow_self _ (by omega)).trans hd
    rw [KStar.TotallyRealRoots.emultiplicity_pow_sub_one_odd hl hd1, emultiplicity_pow_self_of_prime hp]

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Use `haveI : NeZero (l ^ a) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Establish `hker : KStar.TotallyRealRoots.princ l a = (KStar.TotallyRealRoots.redPow l a).ker` using `rfl`. Rewrite using `[hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (KStar.TotallyRealRoots.redPow_surjective a), Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hl ha]`.
-/
private theorem pg_index {l : ℕ} [Fact l.Prime] {a : ℕ} (ha : 0 < a) :
    (KStar.TotallyRealRoots.princ l a).index = l ^ (a - 1) * (l - 1) := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ a) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hker : KStar.TotallyRealRoots.princ l a = (KStar.TotallyRealRoots.redPow l a).ker := rfl
  rw [hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (KStar.TotallyRealRoots.redPow_surjective a),
    Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hl ha]

/- English proof (translation)
Establish `hirr : Irreducible (l : ℤ_[l])` using `PadicInt.irreducible_p`. Establish `hnu : ¬ IsUnit (-((l : ℤ_[l]) ^ c))`. Rewrite using `[IsUnit.neg_iff, isUnit_pow_iff (by omega)]`. Conclude with `hirr.not_isUnit`. Establish `hu : IsUnit (1 + (l : ℤ_[l]) ^ c)`.

Use `(IsLocalRing.isUnit_or_isUnit_one_sub_self (-((l : ℤ_[l]) ^ c))).resolve_left hnu` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg]`. Use `⟨hu.unit, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[KStar.TotallyRealRoots.mem_princ]`. Simplify using the standard rewrite rules.

Rewrite using `[KStar.TotallyRealRoots.mem_princ]`. Simplify using `only [IsUnit.unit_spec, add_sub_cancel_left]`. Rewrite using `[pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem pg_exists {l : ℕ} [Fact l.Prime] {c : ℕ} (h1 : 1 ≤ c) :
    ∃ v ∈ KStar.TotallyRealRoots.princ l c, v ∉ KStar.TotallyRealRoots.princ l (c + 1) := by
  have hirr : Irreducible (l : ℤ_[l]) := PadicInt.irreducible_p
  have hnu : ¬ IsUnit (-((l : ℤ_[l]) ^ c)) := by
    rw [IsUnit.neg_iff, isUnit_pow_iff (by omega)]
    exact hirr.not_isUnit
  have hu : IsUnit (1 + (l : ℤ_[l]) ^ c) := by
    have := (IsLocalRing.isUnit_or_isUnit_one_sub_self (-((l : ℤ_[l]) ^ c))).resolve_left hnu
    simpa [sub_eq_add_neg] using this
  refine ⟨hu.unit, ?_, ?_⟩
  · rw [KStar.TotallyRealRoots.mem_princ]
    simp
  · rw [KStar.TotallyRealRoots.mem_princ]
    simp only [IsUnit.unit_spec, add_sub_cancel_left]
    rw [pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit]
    omega

/- English proof (translation)
Introduce `l _ c hc`. Establish `hl : l.Prime` using `Fact.out`. Establish `h1 : 1 ≤ c`. Apply the tactic sequence `unfold qExp at hc; split_ifs at hc <;> omega`. Establish `h2 : l = 2 → 2 ≤ c`.

Introduce `h`. Unfold `qExp at hc`. Simplify using `[h] at hc`. Use linear arithmetic over natural numbers and integers. Establish `hexact : ∀ u : ℤ_[l]ˣ, u ∈ KStar.TotallyRealRoots.princ l c → u ∉ KStar.TotallyRealRoots.princ l (c + 1) → emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = c`.

Introduce `u hu hu1`. Rewrite `hu`, `hu1` using `[KStar.TotallyRealRoots.mem_princ]`. Conclude with `emultiplicity_eq_coe.mpr ⟨hu, hu1⟩`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `u hu`.

Prove the components needed by the constructor for the conclusion. Introduce `hle hu1`. Establish `hcl : IsClosed ((KStar.TotallyRealRoots.princ l (c + 1) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ)` using `Subgroup.isClosed_of_isOpen _ (KStar.TotallyRealRoots.isOpen_princ _)`. Establish `hcle` using `Subgroup.topologicalClosure_minimal _ (Subgroup.zpowers_le.mpr hu1) hcl`. Take `⟨v, hv, hv'⟩` from `pg_exists (l := l) h1`.

Conclude with `hv' (hcle (hle hv))`. Introduce `hu1`. Conclude with `KStar.TotallyRealRoots.princ_le_of_isClosed h1 h2 (Subgroup.isClosed_topologicalClosure _) (Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers u)) (hexact u hu hu1)`. Introduce `u hu hu1`. Establish `he` using `hexact u hu hu1`.

Use `⟨⟨?_, h1, h2⟩, ?_⟩` and prove the remaining obligations. Establish `hpow : ∀ n : ℕ, IsDiscreteValuationRing.addVal ℤ_[l] ((l : ℤ_[l]) ^ n) = n`. Introduce `n`. Rewrite using `[IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer PadicInt.irreducible_p]`. Simplify using the standard rewrite rules.

Take `⟨hd, hnd⟩` from `emultiplicity_eq_coe.mp he`. Establish `a1` using `(IsDiscreteValuationRing.addVal_le_iff_dvd).mpr hd`. Rewrite `a1` using `[hpow]`. Establish `a2 : ¬ (((c + 1 : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal ℤ_[l] ((u : ℤ_[l]) - 1))`. Introduce `h`.

Apply `hnd` to reduce the goal to its premises. Apply `(IsDiscreteValuationRing.addVal_le_iff_dvd).mp` to reduce the goal to its premises. Rewrite using `[hpow]`. Conclude with `h`. Use `show IsDiscreteValuationRing.addVal ℤ_[l] ((u : ℤ_[l]) - 1) = c`.

Apply `le_antisymm _ a1` to reduce the goal to its premises. Use `push_neg at a2`. Move the coercions through the operations in `at a2`. Conclude with `ENat.lt_natCast_add_one_iff.mp a2`. Introduce `m`.

Establish `hm` using `pg_emult h1 h2 (KStar.TotallyRealRoots.mem_princ.mp hu) m`. Rewrite `hm` using `[he]`. Establish `hm' : emultiplicity (l : ℤ_[l]) (((u ^ l ^ m : ℤ_[l]ˣ) : ℤ_[l]) - 1) = ((c + m : ℕ) : ℕ∞)`. Use `push_cast`. Conclude with `hm`.

Take `⟨a, b⟩` from `emultiplicity_eq_coe.mp hm'`. Conclude with `⟨KStar.TotallyRealRoots.mem_princ.mpr a, fun h => b (KStar.TotallyRealRoots.mem_princ.mp h)⟩`. Introduce `m`. Establish `hle` using `KStar.TotallyRealRoots.princ_anti (l := l) (Nat.le_add_right c m)`. Establish `key` using `Subgroup.relIndex_mul_index hle`.

Rewrite `key` using `[pg_index (by omega : 0 < c), pg_index (by omega : 0 < c + m)]`. Establish `hcm : c + m - 1 = (c - 1) + m` using `by omega`. Rewrite `key` using `[hcm, pow_add]`. Establish `hpos : 0 < l ^ (c - 1) * (l - 1)` using `Nat.mul_pos (pow_pos hl.pos _) (by have := hl.two_le; omega)`. Apply `Nat.eq_of_mul_eq_mul_right hpos` to reduce the goal to its premises.

Rewrite using `[key]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Tower.princGen :
    ∀ (l : ℕ) [Fact l.Prime] (c : ℕ), qExp l ≤ c →
        (∀ u ∈ KStar.TotallyRealRoots.princ l c, (KStar.TotallyRealRoots.princ l c ≤ (Subgroup.zpowers u).topologicalClosure ↔ u ∉ KStar.TotallyRealRoots.princ l (c + 1))) ∧
        (∀ u ∈ KStar.TotallyRealRoots.princ l c, u ∉ KStar.TotallyRealRoots.princ l (c + 1) → PropA.IsLevel l (u : ℤ_[l]) c ∧
          ∀ m : ℕ, u ^ l ^ m ∈ KStar.TotallyRealRoots.princ l (c + m) ∧ u ^ l ^ m ∉ KStar.TotallyRealRoots.princ l (c + m + 1)) ∧
        ∀ m : ℕ, (KStar.TotallyRealRoots.princ l (c + m)).relIndex (KStar.TotallyRealRoots.princ l c) = l ^ m := by
  intro l _ c hc
  have hl : l.Prime := Fact.out
  have h1 : 1 ≤ c := by
    unfold qExp at hc; split_ifs at hc <;> omega
  have h2 : l = 2 → 2 ≤ c := by
    intro h; unfold qExp at hc; simp [h] at hc; omega
  have hexact : ∀ u : ℤ_[l]ˣ, u ∈ KStar.TotallyRealRoots.princ l c → u ∉ KStar.TotallyRealRoots.princ l (c + 1) →
      emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = c := by
    intro u hu hu1
    rw [KStar.TotallyRealRoots.mem_princ] at hu hu1
    exact emultiplicity_eq_coe.mpr ⟨hu, hu1⟩
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    constructor
    · intro hle hu1
      have hcl : IsClosed ((KStar.TotallyRealRoots.princ l (c + 1) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) :=
        Subgroup.isClosed_of_isOpen _ (KStar.TotallyRealRoots.isOpen_princ _)
      have hcle := Subgroup.topologicalClosure_minimal _ (Subgroup.zpowers_le.mpr hu1) hcl
      obtain ⟨v, hv, hv'⟩ := pg_exists (l := l) h1
      exact hv' (hcle (hle hv))
    · intro hu1
      exact KStar.TotallyRealRoots.princ_le_of_isClosed h1 h2 (Subgroup.isClosed_topologicalClosure _)
        (Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers u)) (hexact u hu hu1)
  · intro u hu hu1
    have he := hexact u hu hu1
    refine ⟨⟨?_, h1, h2⟩, ?_⟩
    · have hpow : ∀ n : ℕ, IsDiscreteValuationRing.addVal ℤ_[l] ((l : ℤ_[l]) ^ n) = n := by
        intro n
        rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer PadicInt.irreducible_p]
        simp
      obtain ⟨hd, hnd⟩ := emultiplicity_eq_coe.mp he
      have a1 := (IsDiscreteValuationRing.addVal_le_iff_dvd).mpr hd
      rw [hpow] at a1
      have a2 : ¬ (((c + 1 : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal ℤ_[l] ((u : ℤ_[l]) - 1)) := by
        intro h
        apply hnd
        apply (IsDiscreteValuationRing.addVal_le_iff_dvd).mp
        rw [hpow]
        exact h
      show IsDiscreteValuationRing.addVal ℤ_[l] ((u : ℤ_[l]) - 1) = c
      apply le_antisymm _ a1
      push_neg at a2
      push_cast at a2
      exact ENat.lt_natCast_add_one_iff.mp a2
    · intro m
      have hm := pg_emult h1 h2 (KStar.TotallyRealRoots.mem_princ.mp hu) m
      rw [he] at hm
      have hm' : emultiplicity (l : ℤ_[l]) (((u ^ l ^ m : ℤ_[l]ˣ) : ℤ_[l]) - 1) = ((c + m : ℕ) : ℕ∞) := by
        push_cast
        exact hm
      obtain ⟨a, b⟩ := emultiplicity_eq_coe.mp hm'
      exact ⟨KStar.TotallyRealRoots.mem_princ.mpr a, fun h => b (KStar.TotallyRealRoots.mem_princ.mp h)⟩
  · intro m
    have hle := KStar.TotallyRealRoots.princ_anti (l := l) (Nat.le_add_right c m)
    have key := Subgroup.relIndex_mul_index hle
    rw [pg_index (by omega : 0 < c), pg_index (by omega : 0 < c + m)] at key
    have hcm : c + m - 1 = (c - 1) + m := by omega
    rw [hcm, pow_add] at key
    have hpos : 0 < l ^ (c - 1) * (l - 1) :=
      Nat.mul_pos (pow_pos hl.pos _) (by have := hl.two_le; omega)
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [key]
    ring
