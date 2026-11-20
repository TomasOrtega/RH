import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.SplittingFieldIsoQuadratic
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.KstarRam
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV

namespace UpperTheory.V.SmallClassNumbers

def len (Ω : Type) [Field Ω] [CharZero Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ) : ℕ∞ :=
  Module.length c.O (ShaU (twist₂ l (chiO ℚ Ω l c.O ^ (-(e : ℤ)))) (l * 2) ⊤)

def Bound : Prop :=
  ∃ C A : ℕ, ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (e : ℕ), 1 ≤ e → Even e →
    ∀ (c : ∀ l : Nat.Primes, Coef l) (Ls : Finset Nat.Primes), (∀ l ∈ Ls, 5 ≤ (l : ℕ) ∧ ¬ (l : ℕ) - 1 ∣ 2 * e) →
      (∀ l ∈ Ls, len Ω l (c l) e ≠ ⊤) ∧
      ∑ l ∈ Ls, Real.log (l : ℕ) * (((len Ω l (c l) e).toNat : ℝ) / ((eO l (c l).O).toNat : ℝ)) ≤ C * ((e : ℝ) + 1) ^ A

/- English proof (translation)
Establish `h : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O 2) = 1`. Use extensionality with `g`. Simplify using `[Chr.dirG]`. Rewrite using `[Vlen, h, Chr.V', Chr.VS, len]`. Establish `e1 : (1 : G ℚ Ω →* c.Oˣ)⁻¹ * chiO ℚ Ω l c.O ^ (-(e : ℤ)) = chiO ℚ Ω l c.O ^ (-(e : ℤ))` using `by rw [inv_one, one_mul]`.

Use `show Module.length c.O (ShaU (twist₂ l ((1 : G ℚ Ω →* c.Oˣ)⁻¹ * chiO ℚ Ω l c.O ^ (-(e : ℤ)))) (l * 2) ⊤) = _`. Rewrite using `[e1]`.
-/
theorem vlen_one (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ) :
    Vlen Ω c e (1 : DirichletCharacter c.O 2) = len Ω l c e := by
  have h : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O 2) = 1 := by
    ext g
    simp [Chr.dirG]
  rw [Vlen, h, Chr.V', Chr.VS, len]
  have e1 : (1 : G ℚ Ω →* c.Oˣ)⁻¹ * chiO ℚ Ω l c.O ^ (-(e : ℤ)) = chiO ℚ Ω l c.O ^ (-(e : ℤ)) := by rw [inv_one, one_mul]
  show Module.length c.O (ShaU (twist₂ l ((1 : G ℚ Ω →* c.Oˣ)⁻¹ * chiO ℚ Ω l c.O ^ (-(e : ℤ)))) (l * 2) ⊤) = _
  rw [e1]

/- English proof (translation)
Take `⟨hd, himag, hquad, -⟩` from `kstar 3 Nat.prime_three (by norm_num)`. Rewrite using `[classNumber_eq_one_iff]`. Apply `RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt` to reduce the goal to its premises. Establish `h1 : InfinitePlace.nrComplexPlaces (Kstar 3) = 1`. Use `IsTotallyComplex.finrank (K := Kstar 3)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hd, h1, hquad]`. Use `Real.pi_gt_three` as an intermediate fact. Evaluate the numerical expressions using `[Nat.factorial]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem classNumber_three : classNumber (Kstar 3) = 1 := by
  obtain ⟨hd, himag, hquad, -⟩ := kstar 3 Nat.prime_three (by norm_num)
  rw [classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  have h1 : InfinitePlace.nrComplexPlaces (Kstar 3) = 1 := by
    have := IsTotallyComplex.finrank (K := Kstar 3)
    omega
  rw [hd, h1, hquad]
  have := Real.pi_gt_three
  norm_num [Nat.factorial]
  nlinarith

/- English proof (translation)
Introduce `hn`. Establish `hz : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1` using `fun z => (A.valuation_le_one_iff _).2 (intCast_mem A z)`. Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.2 hc`. Establish `e : (1 : Ω) = (a : Ω) * (p : Ω) + (b : Ω) * (n : Ω)` using `by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab.symm`. Establish `h1 : A.valuation ((a : Ω) * (p : Ω) + (b : Ω) * (n : Ω)) < 1`.

Use `A.valuation.map_add_lt ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hz a)) hp`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hz b)) hn`.

Rewrite `h1` using `[← e, map_one]`. Conclude with `lt_irrefl _ h1`.
-/
private theorem val_not_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p n : ℕ} (hc : p.Coprime n)
    (hp : A.valuation (p : Ω) < 1) : ¬ A.valuation (n : Ω) < 1 := by
  intro hn
  have hz : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => (A.valuation_le_one_iff _).2 (intCast_mem A z)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
  have e : (1 : Ω) = (a : Ω) * (p : Ω) + (b : Ω) * (n : Ω) := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab.symm
  have h1 : A.valuation ((a : Ω) * (p : Ω) + (b : Ω) * (n : Ω)) < 1 := by
    refine A.valuation.map_add_lt ?_ ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (hz a)) hp
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (hz b)) hn
  rw [← e, map_one] at h1
  exact lt_irrefl _ h1

/- English proof (translation)
Use extensionality with `a`. Rewrite using `[Subsingleton.elim a 1]`. Simplify using the standard rewrite rules.
-/
theorem eq_one {O : Type} [CommRing O] (ψ : DirichletCharacter O 2) : ψ = 1 := by
  ext a
  rw [Subsingleton.elim a 1]
  simp

/- English proof (translation)
Take `⟨hd, himag, hquad, -⟩` from `kstar 3 Nat.prime_three (by norm_num)`. Establish `hd' : (discr (Kstar 3)).natAbs = 3` using `by rw [hd]; simp`. Use `⟨by omega, he, by decide, ?_, eq_one _, ?_, hquad, himag, ?_, by rw [hd']; decide, ?_, hg⟩` and prove the remaining obligations. Rewrite using `[orderOf_one, Nat.dvd_one]`. Use linear arithmetic over natural numbers and integers.

Use `show (1 : DirichletCharacter O 2) (-1) = (-1) ^ e`. Rewrite using `[hev.neg_one_pow, MulChar.one_apply isUnit_one.neg]`. Rewrite using `[hd', classNumber_three]`. Introduce `h`. Use `Nat.le_of_dvd (by norm_num) h` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Introduce `hle`. Take `⟨A, hA⟩` from `(Chr.placesQ Ω).1 _ Nat.prime_three`. Use `kstarRam _ Nat.prime_three (by norm_num) Ω A hA (le_trans (le_inf (fun σ hσ => ?_) fun σ _ => ?_) hle)` and prove the remaining obligations. Establish `h1 : cycZ ℚ Ω l σ = 1` using `(places ℚ Ω l A).2.2.2 (val_not_lt A ((Nat.coprime_primes Nat.prime_three hl.out).2 (by omega)) hA) hσ show cycMod ℚ Ω l 1 σ = 1`.

Simplify using `[cycMod, h1]`. Use `show (chiP l (1 : DirichletCharacter O 2)).toUnitHom (Chr.cls ℚ Ω 2 σ) = 1`. Rewrite using `[Subsingleton.elim (Chr.cls ℚ Ω 2 σ) 1, map_one]`.
-/
theorem gd (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra (Kstar 3) Ω] (l : ℕ) [hl : Fact l.Prime] (e : ℕ)
    (he : 1 ≤ e) (hev : Even e) (h5 : 5 ≤ l) (hg : ¬ l - 1 ∣ 2 * e) {O : Type} [CommRing O] :
    GD Ω (Kstar 3) l e (1 : DirichletCharacter O 2) := by
  obtain ⟨hd, himag, hquad, -⟩ := kstar 3 Nat.prime_three (by norm_num)
  have hd' : (discr (Kstar 3)).natAbs = 3 := by rw [hd]; simp
  refine ⟨by omega, he, by decide, ?_, eq_one _, ?_, hquad, himag, ?_, by rw [hd']; decide, ?_, hg⟩
  · rw [orderOf_one, Nat.dvd_one]
    omega
  · show (1 : DirichletCharacter O 2) (-1) = (-1) ^ e
    rw [hev.neg_one_pow, MulChar.one_apply isUnit_one.neg]
  · rw [hd', classNumber_three]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  · intro hle
    obtain ⟨A, hA⟩ := (Chr.placesQ Ω).1 _ Nat.prime_three
    refine kstarRam _ Nat.prime_three (by norm_num) Ω A hA (le_trans (le_inf (fun σ hσ => ?_) fun σ _ => ?_) hle)
    · have h1 : cycZ ℚ Ω l σ = 1 := (places ℚ Ω l A).2.2.2
        (val_not_lt A ((Nat.coprime_primes Nat.prime_three hl.out).2 (by omega)) hA) hσ
      show cycMod ℚ Ω l 1 σ = 1
      simp [cycMod, h1]
    · show (chiP l (1 : DirichletCharacter O 2)).toUnitHom (Chr.cls ℚ Ω 2 σ) = 1
      rw [Subsingleton.elim (Chr.cls ℚ Ω 2 σ) 1, map_one]

/- English proof (translation)
Take `⟨c5, a, hG⟩` from `hG (Kstar 3)`. Take `⟨hd, -, -, -⟩` from `kstar 3 Nat.prime_three (by norm_num)`. Establish `hd' : (discr (Kstar 3)).natAbs = 3` using `by rw [hd]; simp`. Use `⟨2 * c5 * 2 ^ a * 18, a, fun Ω _ _ _ e he hev c Ls hLs => ?_⟩` and prove the remaining obligations. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`.

Use `letI : Algebra (Kstar 3) Ω := (IsAlgClosed.lift (R := ℚ) (S := Kstar 3) (M := Ω)).toRingHom.toAlgebra`. Establish `hm : ∀ l : Nat.Primes, (1 : DirichletCharacter (c l).O 2) ∈ orb (c l) ⊤` using `fun l => (mem_orb _).2 (Subsingleton.elim _ _)`. Establish `ho : ∀ l : Nat.Primes, orb (c l) (⊤ : Subgroup (ZMod 2)ˣ) = {1}` using `fun l => Finset.eq_singleton_iff_unique_mem.2 ⟨hm l, fun ψ _ => eq_one ψ⟩`. Take `⟨h1, h2⟩` from `hG Ω e 2 ⊤ 7 11 (by norm_num) (by norm_num) (by norm_num) (by rw [hd']; norm_num) (by rw [hd']; norm_num) c Ls fun l hl => ⟨1, hm l, gd Ω l e he hev (hLs l hl).1 (hLs l hl).2⟩`. Use `⟨fun l hl => by rw [← vlen_one]; exact h1 l hl 1 (hm l), ?_⟩` and prove the remaining obligations.

Simplify using `only [ho, Finset.sum_singleton, Vn, vlen_one, Chr.nrm, Subgroup.index_top, Nat.totient_one, Nat.cast_one, mul_one] at h2`. Use `h2.trans ?_` and prove the remaining obligations. Establish `a7 : Real.log (7 : ℕ) ≤ 7` using `(Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)`. Establish `a11 : Real.log (11 : ℕ) ≤ 11` using `(Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)`. Rewrite using `[mul_pow]`.

Use `push_cast`. Establish `: (0 : ℝ) ≤ 2 * c5 * (2 ^ a * ((e : ℝ) + 1) ^ a)` using `by positivity`. Move the coercions through the operations in `at a7 a11`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem bound_of (hG : U3.CorGK) : Bound := by
  classical
  obtain ⟨c5, a, hG⟩ := hG (Kstar 3)
  obtain ⟨hd, -, -, -⟩ := kstar 3 Nat.prime_three (by norm_num)
  have hd' : (discr (Kstar 3)).natAbs = 3 := by rw [hd]; simp
  refine ⟨2 * c5 * 2 ^ a * 18, a, fun Ω _ _ _ e he hev c Ls hLs => ?_⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra (Kstar 3) Ω := (IsAlgClosed.lift (R := ℚ) (S := Kstar 3) (M := Ω)).toRingHom.toAlgebra
  have hm : ∀ l : Nat.Primes, (1 : DirichletCharacter (c l).O 2) ∈ orb (c l) ⊤ := fun l =>
    (mem_orb _).2 (Subsingleton.elim _ _)
  have ho : ∀ l : Nat.Primes, orb (c l) (⊤ : Subgroup (ZMod 2)ˣ) = {1} := fun l =>
    Finset.eq_singleton_iff_unique_mem.2 ⟨hm l, fun ψ _ => eq_one ψ⟩
  obtain ⟨h1, h2⟩ := hG Ω e 2 ⊤ 7 11 (by norm_num) (by norm_num) (by norm_num) (by rw [hd']; norm_num) (by rw [hd']; norm_num) c Ls
    fun l hl => ⟨1, hm l, gd Ω l e he hev (hLs l hl).1 (hLs l hl).2⟩
  refine ⟨fun l hl => by rw [← vlen_one]; exact h1 l hl 1 (hm l), ?_⟩
  simp only [ho, Finset.sum_singleton, Vn, vlen_one, Chr.nrm, Subgroup.index_top, Nat.totient_one, Nat.cast_one, mul_one] at h2
  refine h2.trans ?_
  have a7 : Real.log (7 : ℕ) ≤ 7 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have a11 : Real.log (11 : ℕ) ≤ 11 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  rw [mul_pow]
  push_cast
  have : (0 : ℝ) ≤ 2 * c5 * (2 ^ a * ((e : ℝ) + 1) ^ a) := by positivity
  push_cast at a7 a11
  nlinarith

end UpperTheory.V.SmallClassNumbers

end
