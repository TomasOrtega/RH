import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueMaximalAbovePlace

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.EmbFrob

open Polynomial

/- English proof (translation)
Equip the data with the indicated structure. Equip the data with the indicated structure. Equip the data with the indicated structure. Introduce a local definition for the expression. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Equip the data with the indicated structure. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
