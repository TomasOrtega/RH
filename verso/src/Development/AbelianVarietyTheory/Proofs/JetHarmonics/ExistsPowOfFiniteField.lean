import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueMaximalAbovePlace

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.EmbFrob

open Polynomial

/- English proof (translation)
Use `haveI : CharP F p := f.charP f.injective p`. Use `letI : Algebra (ZMod p) F := ZMod.algebra F p`. Use `letI : Algebra (ZMod p) k := ZMod.algebra k p`. Use `letI : Algebra F k := f.toAlgebra`. Use `haveI : IsScalarTower (ZMod p) F k := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`.

Set `g' : F →ₐ[ZMod p] k` to `{ g with commutes' := fun z => RingHom.congr_fun (Subsingleton.elim (g.comp (algebraMap (ZMod p) F)) (algebraMap _ k)) z }`. Take `⟨n, hn⟩` from `(FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F).2 (g'.restrictNormal' F)`. Use `⟨n, fun a => ?_⟩` and prove the remaining obligations. Establish `h1 : algebraMap F k (g'.restrictNormal' F a) = g' (algebraMap F F a)` using `AlgHom.restrictNormal_commutes g' F a`. Establish `h2 : g'.restrictNormal' F a = a ^ p ^ (n : ℕ)`.

Rewrite using `[← hn]`. Simplify using `[AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]`. Rewrite `h1` using `[h2, map_pow]`. Conclude with `h1.symm`.
-/
theorem exists_pow_of_finite_field (p : ℕ) [Fact p.Prime] {F k : Type} [Field F] [Finite F]
    [Field k] [CharP k p] (f g : F →+* k) : ∃ i : ℕ, ∀ a : F, g a = f a ^ p ^ i := by
  haveI : CharP F p := f.charP f.injective p
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : Algebra F k := f.toAlgebra
  haveI : IsScalarTower (ZMod p) F k := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let g' : F →ₐ[ZMod p] k :=
    { g with commutes' := fun z =>
        RingHom.congr_fun (Subsingleton.elim (g.comp (algebraMap (ZMod p) F)) (algebraMap _ k)) z }
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F).2
    (g'.restrictNormal' F)
  refine ⟨n, fun a => ?_⟩
  have h1 : algebraMap F k (g'.restrictNormal' F a) = g' (algebraMap F F a) :=
    AlgHom.restrictNormal_commutes g' F a
  have h2 : g'.restrictNormal' F a = a ^ p ^ (n : ℕ) := by
    rw [← hn]
    simp [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  rw [h2, map_pow] at h1
  exact h1.symm

open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hpQ : (p : OE) ∈ (IsLocalRing.maximalIdeal R).comap σ`. Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `hp`. Establish `hQ : ((IsLocalRing.maximalIdeal R).comap σ).IsMaximal`.

Use `Ideal.IsPrime.isMaximal inferInstance fun h => ?_` and prove the remaining obligations. Rewrite `hpQ` using `[h, Ideal.mem_bot]`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hpQ`. Set `φ : w.Ow →+* R` to `Ideal.Quotient.lift _ (extend σ).toRingHom (by`. Introduce `z hz`.

Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hz`. Simplify using `[hσ])`. Establish `hφ : ∀ a, φ (w.toOw a) = σ a` using `fun a => by show extend (p := p) σ (1 ⊗ₜ a) = σ a`. Simplify using the standard rewrite rules. Establish `hle : ((IsLocalRing.maximalIdeal R).comap σ).map w.toOw ≤ (IsLocalRing.maximalIdeal R).comap φ`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, hφ]`. Conclude with `ha`. Rewrite `hle` using `[hP _ hQ hne, top_le_iff]`.

Conclude with `Ideal.comap_ne_top φ (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle`.
-/
theorem comap_eq {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE] [IsDedekindDomain OE]
    [CharZero OE] {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[p] R]
    (hp : ¬ IsUnit (p : R)) (w : Place p OE) {P : Ideal OE}
    (hP : ∀ Q : Ideal OE, Q.IsMaximal → Q ≠ P → Q.map w.toOw = ⊤) (σ : OE →+* R)
    (hσ : extend σ w.e = 1) : (IsLocalRing.maximalIdeal R).comap σ = P := by
  by_contra hne
  have hpQ : (p : OE) ∈ (IsLocalRing.maximalIdeal R).comap σ := by
    rw [Ideal.mem_comap, map_natCast]; exact hp
  have hQ : ((IsLocalRing.maximalIdeal R).comap σ).IsMaximal := by
    refine Ideal.IsPrime.isMaximal inferInstance fun h => ?_
    rw [h, Ideal.mem_bot] at hpQ
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hpQ
  let φ : w.Ow →+* R := Ideal.Quotient.lift _ (extend σ).toRingHom (by
    intro z hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    simp [hσ])
  have hφ : ∀ a, φ (w.toOw a) = σ a := fun a => by
    show extend (p := p) σ (1 ⊗ₜ a) = σ a
    simp
  have hle : ((IsLocalRing.maximalIdeal R).comap σ).map w.toOw ≤
      (IsLocalRing.maximalIdeal R).comap φ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, hφ]
    exact ha
  rw [hP _ hQ hne, top_le_iff] at hle
  exact Ideal.comap_ne_top φ (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle

/- English proof (translation)
Introduce `p _ OE _ _ _ _ C _ v R _ _ _ hv hp w σ τ hσ hτ`. Use `haveI : IsDomain R := hv.hom_inj.isDomain (algebraMap R C)`. Use `haveI : ValuationRing R := ValuationRing.of_integers v hv`. Set `w' : Place p OE` to `⟨w.e, w.idem, w.ne_zero, w.prim⟩`. Take `⟨P, hPm, hpP, -, hP⟩` from `GlobalTheory.OnePrime.exists_prime_under p OE w'`.

Establish `h1` using `comap_eq hp w' hP σ hσ`. Establish `h2` using `comap_eq hp w' hP τ hτ`. Establish `hP0 : P ≠ ⊥` using `fun h => by`. Rewrite `hpP` using `[h, Ideal.mem_bot]`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hpP`.

Use `haveI : Finite (OE ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0`. Use `letI : Field (OE ⧸ P) := Ideal.Quotient.field P`. Use `haveI : CharP (IsLocalRing.ResidueField R) p := by`. Use `(CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 ?_` and prove the remaining obligations. Rewrite using `[← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff]`.

Conclude with `hp`. Take `⟨i, hi⟩` from `exists_pow_of_finite_field p (k := IsLocalRing.ResidueField R) (Ideal.quotientMap (IsLocalRing.maximalIdeal R) σ h1.ge) (Ideal.quotientMap (IsLocalRing.maximalIdeal R) τ h2.ge)`. Use `⟨i, fun a => ?_⟩` and prove the remaining obligations. Establish `h3 : IsLocalRing.residue R (τ a) = IsLocalRing.residue R (σ a) ^ p ^ i` using `hi (Ideal.Quotient.mk P a)`. Establish `h4 : τ a - σ a ^ p ^ i ∈ IsLocalRing.maximalIdeal R`.

Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, h3, sub_self]`. Conclude with `lt_of_le_of_ne (hv.map_le_one _) fun h => h4 (hv.isUnit_iff_valuation_eq_one.2 h)`.
-/
theorem exists_frobenius_pow : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [IsDedekindDomain OE] [CharZero OE] [Module.Finite ℤ OE] (C : Type) [Field C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R],
    v.Integers R → ¬ IsUnit (p : R) → ∀ (w : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.PlaceU p OE)
    (σ τ : OE →+* R), σ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e →
    τ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e →
    ∃ i : ℕ, ∀ a : OE, v (algebraMap R C (τ a - σ a ^ (p ^ i))) < 1 := by
  intro p _ OE _ _ _ _ C _ v R _ _ _ hv hp w σ τ hσ hτ
  haveI : IsDomain R := hv.hom_inj.isDomain (algebraMap R C)
  haveI : ValuationRing R := ValuationRing.of_integers v hv
  let w' : Place p OE := ⟨w.e, w.idem, w.ne_zero, w.prim⟩
  obtain ⟨P, hPm, hpP, -, hP⟩ := GlobalTheory.OnePrime.exists_prime_under p OE w'
  have h1 := comap_eq hp w' hP σ hσ
  have h2 := comap_eq hp w' hP τ hτ
  have hP0 : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hpP
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hpP
  haveI : Finite (OE ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  letI : Field (OE ⧸ P) := Ideal.Quotient.field P
  haveI : CharP (IsLocalRing.ResidueField R) p := by
    refine (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 ?_
    rw [← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff]
    exact hp
  obtain ⟨i, hi⟩ := exists_pow_of_finite_field p (k := IsLocalRing.ResidueField R)
    (Ideal.quotientMap (IsLocalRing.maximalIdeal R) σ h1.ge)
    (Ideal.quotientMap (IsLocalRing.maximalIdeal R) τ h2.ge)
  refine ⟨i, fun a => ?_⟩
  have h3 : IsLocalRing.residue R (τ a) = IsLocalRing.residue R (σ a) ^ p ^ i :=
    hi (Ideal.Quotient.mk P a)
  have h4 : τ a - σ a ^ p ^ i ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, h3, sub_self]
  exact lt_of_le_of_ne (hv.map_le_one _) fun h => h4 (hv.isUnit_iff_valuation_eq_one.2 h)

end GlobalTheory.EmbFrob
