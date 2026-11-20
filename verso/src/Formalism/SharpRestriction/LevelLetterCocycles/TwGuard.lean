import Formalism.SharpRestriction.LevelLetterCocycles.TwGood

noncomputable section

namespace Formalism.MainNotions

open NumberField IsDedekindDomain Formalism.BasicNotions

def PlaceLiesOver (D : D7) (w' : D.what₂.places.Pl) (v : HeightOneSpectrum (𝓞 D.LL0)) : Prop :=
  ∀ x : 𝓞 D.LL0, 0 < D.what₂.places.val w' ((x : D.LL0) : D.what₂.LL) ↔ x ∈ v.asIdeal

def SetAt (D : D7) (i : D.ntw.Tw) (v : HeightOneSpectrum (𝓞 D.LL0)) : Prop :=
  ∀ x : 𝓞 D.LL0, (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i (x : D.LL0)) ↔ x ∈ v.asIdeal

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem nonzeroIndexPlace_iff_exists_setAt (D : D7) (W : Set (HeightOneSpectrum (𝓞 D.LL0)))
    (hW : ∀ w', D.what₂.muAt w' ≠ D.what₂.mu0 ↔ ∃ v ∈ W, PlaceLiesOver D w' v)
    (hExt : ∀ v ∈ W, ∃ w', PlaceLiesOver D w' v) (i : D.ntw.Tw) :
    D.ntw.NonzeroIndexPlace i ↔ ∃ v ∈ W, SetAt D i v := by
  constructor
  · rintro ⟨w', hmu, hx⟩
    obtain ⟨v, hv, hov⟩ := (hW w').1 hmu
    exact ⟨v, hv, fun x => (hx x).trans (hov x)⟩
  · rintro ⟨v, hv, hs⟩
    obtain ⟨w', hov⟩ := hExt v hv
    exact ⟨w', (hW w').2 ⟨v, hv, hov⟩, fun x => (hs x).trans (hov x).symm⟩

abbrev integersBaseMap (D : D7) : 𝓞 D.LL0 →+* 𝓞 D.what₂.LL := RingOfIntegers.mapRingHom D.LL0.val.toRingHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem integersBaseMap_coe (D : D7) (x : 𝓞 D.LL0) :
    algebraMap (𝓞 D.what₂.LL) D.what₂.LL (integersBaseMap D x) = ((x : D.LL0) : D.what₂.LL) := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem integersBaseMap_injective (D : D7) : Function.Injective (integersBaseMap D) := by
  intro a b h
  have h1 := congrArg (algebraMap (𝓞 D.what₂.LL) D.what₂.LL) h
  rw [integersBaseMap_coe, integersBaseMap_coe] at h1
  exact FaithfulSMul.algebraMap_injective (𝓞 D.LL0) D.LL0 (Subtype.ext h1)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem vAdd_pos_iff_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K}
    (ha : a ≠ 0) : 0 < vAdd la (a : K) ↔ a ∈ la.asIdeal := by
  have h0 : la.valuation K (a : K) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact_mod_cast ha
  have hle := la.valuation_le_one (K := K) a
  have hlt : la.valuation K (algebraMap (𝓞 K) K a) < 1 ↔ a ∈ la.asIdeal := la.valuation_lt_one_iff_mem a
  unfold vAdd
  constructor
  · intro h
    by_contra hm
    have h1 : la.valuation K (a : K) = 1 := le_antisymm hle (not_lt.1 fun h' => hm (hlt.1 h'))
    rw [h1] at h
    simp at h
  · intro hm
    have h2 : la.valuation K (a : K) < 1 := hlt.2 hm
    have h3 := (WithZero.log_lt_log h0 one_ne_zero).2 h2
    simp at h3
    omega

/- English proof (translation)
Equip the data with the indicated structure. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_placeOver_of_place (D : D7) (v : HeightOneSpectrum (𝓞 D.LL0)) : ∃ w', PlaceLiesOver D w' v := by
  letI : Algebra (𝓞 D.LL0) (𝓞 D.what₂.LL) := (integersBaseMap D).toAlgebra
  haveI hint : Algebra.IsIntegral (𝓞 D.LL0) (𝓞 D.what₂.LL) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := ℤ) x).tower_top⟩
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 D.what₂.LL)) (by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    have : x = 0 := integersBaseMap_injective D (by rw [map_zero]; exact hx)
    rw [this]; exact Ideal.zero_mem _)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv, eq_bot_iff]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    rw [Ideal.mem_bot]
    exact integersBaseMap_injective D (by rw [map_zero]; exact hx)
  let P : HeightOneSpectrum (𝓞 D.what₂.LL) := ⟨Q, hQ, hQ0⟩
  refine ⟨D.plEq.symm P, fun x => ?_⟩
  have hmem : x ∈ v.asIdeal ↔ integersBaseMap D x ∈ Q := by
    rw [← hQv, Ideal.mem_comap]
    rfl
  by_cases hx : x = 0
  · subst hx
    simp only [ZeroMemClass.coe_zero, map_zero, Submodule.zero_mem, iff_true]
    rw [AddValuation.map_zero]
    exact WithTop.coe_lt_top (0 : ℤ)
  · have hx' : ((x : D.LL0) : D.what₂.LL) ≠ 0 := by
      intro h
      apply hx
      apply integersBaseMap_injective D
      apply FaithfulSMul.algebraMap_injective (𝓞 D.what₂.LL) D.what₂.LL
      rw [integersBaseMap_coe, h, map_zero, map_zero]
    rw [D.val_eq _ _ hx', Equiv.apply_symm_apply, hmem, ← integersBaseMap_coe]
    have hne : integersBaseMap D x ≠ 0 := fun h => hx (integersBaseMap_injective D (by rw [h, map_zero]))
    rw [WithTop.coe_pos]
    exact vAdd_pos_iff_mem P hne

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem inNonzeroPlaces_recursive_iff (D : D7) (W : Set (HeightOneSpectrum (𝓞 D.LL0)))
    (hW : ∀ w', D.what₂.muAt w' ≠ D.what₂.mu0 ↔ ∃ v ∈ W, PlaceLiesOver D w' v) (i : D.ntw.Tw) :
    D.ntw.NonzeroIndexPlace i ↔ ∃ v ∈ W, SetAt D i v :=
  nonzeroIndexPlace_iff_exists_setAt D W hW (fun v _ => exists_placeOver_of_place D v) i

end Formalism.MainNotions

end
