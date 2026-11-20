import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.BasisExtend

namespace GlobalTheory.CompanionTheory.FieldDeg

open ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension

/- English proof (translation)
Take `⟨b', -, -⟩` from `basis_extend (σ := I) (Module.finBasis Ω₀ Ω)`. Set `φ : FractionRing (MvPolynomial I Ω₀) →+* FractionRing (MvPolynomial I Ω)` to `liftY (L := Ω₀) (E := Ω) (σ := I)`. Use `letI : Algebra (FractionRing (MvPolynomial I Ω₀)) (FractionRing (MvPolynomial I Ω)) := φ.toAlgebra`. Establish `h1 : Module.finrank (FractionRing (MvPolynomial I Ω₀)) (FractionRing (MvPolynomial I Ω)) = Module.finrank Ω₀ Ω`. Rewrite using `[Module.finrank_eq_card_basis b']`.

Simplify using the standard rewrite rules. Use `set K := IntermediateField.adjoin Ω₀ (Set.range fun q : I => algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X q)) with hK`. Establish `hφ : ∀ a : MvPolynomial I Ω₀, φ (algebraMap _ _ a) = algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.map (algebraMap Ω₀ Ω) a)` using `fun a => by`. Simplify using `only [φ, liftY, IsFractionRing.lift_algebraMap, RingHom.comp_apply]`. Establish `hpoly : ∀ a : MvPolynomial I Ω₀, algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.map (algebraMap Ω₀ Ω) a) ∈ K` using `fun a => by`.

Proceed by induction on `a using MvPolynomial.induction_on with`. Consider the case `C r`. Use `K.algebraMap_mem r` as an intermediate fact. Rewrite `this` using `[hF]`. Simplify `this` using `[MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply Ω (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))]`.

Consider the case `add p q hp hq => simpa using K.add_mem hp hq`. Consider the case `mul_X p i hp`. Establish `hX : algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X i) ∈ K` using `IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩`. Simplify using `using K.mul_mem hp hX`. Establish `hmem : ∀ x, φ x ∈ K` using `fun x => by`.

Take `⟨a, c, -, rfl⟩` from `IsFractionRing.div_surjective (A := MvPolynomial I Ω₀) x`. Rewrite using `[map_div₀, hφ, hφ]`. Conclude with `K.div_mem (hpoly a) (hpoly c)`. Establish `hle : K ≤ Subfield.toIntermediateField φ.fieldRange (fun r => by`. Use `⟨algebraMap (MvPolynomial I Ω₀) _ (MvPolynomial.C r), ?_⟩` and prove the remaining obligations.

Rewrite using `[hφ, hF]`. Simplify using `[MvPolynomial.map_C, MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply Ω (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))]) := by`. Use `IntermediateField.adjoin_le_iff.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`. Use `⟨algebraMap (MvPolynomial I Ω₀) _ (MvPolynomial.X q), ?_⟩` and prove the remaining obligations.

Rewrite using `[hφ]`. Simplify using the standard rewrite rules. Set `ψ : FractionRing (MvPolynomial I Ω₀) →+* K` to `φ.codRestrict K hmem`. Establish `hψ : Function.Bijective ψ`. Use `⟨fun x y h => φ.injective (congrArg Subtype.val h), fun y => ?_⟩` and prove the remaining obligations.

Take `⟨x, hx⟩` from `hle y.2`. Conclude with `⟨x, Subtype.ext hx⟩`. Rewrite using `[← h1]`. Conclude with `(Algebra.finrank_eq_of_equiv_equiv (RingEquiv.ofBijective ψ hψ) (RingEquiv.refl _) (by ext x; rfl)).symm`.
-/
theorem finrank_fraction_over_adjoin_X_eq (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    [FiniteDimensional Ω₀ Ω] (I : Type)
    [Algebra Ω₀ (FractionRing (MvPolynomial I Ω))]
    (hF : algebraMap Ω₀ (FractionRing (MvPolynomial I Ω)) =
      (algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp (algebraMap Ω₀ Ω)) :
    Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : I =>
        algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X q)))
      (FractionRing (MvPolynomial I Ω)) = Module.finrank Ω₀ Ω := by
  classical
  obtain ⟨b', -, -⟩ := basis_extend (σ := I) (Module.finBasis Ω₀ Ω)
  let φ : FractionRing (MvPolynomial I Ω₀) →+* FractionRing (MvPolynomial I Ω) :=
    liftY (L := Ω₀) (E := Ω) (σ := I)
  letI : Algebra (FractionRing (MvPolynomial I Ω₀)) (FractionRing (MvPolynomial I Ω)) :=
    φ.toAlgebra
  have h1 : Module.finrank (FractionRing (MvPolynomial I Ω₀)) (FractionRing (MvPolynomial I Ω)) =
      Module.finrank Ω₀ Ω := by
    rw [Module.finrank_eq_card_basis b']; simp
  set K := IntermediateField.adjoin Ω₀ (Set.range fun q : I =>
        algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X q)) with hK
  have hφ : ∀ a : MvPolynomial I Ω₀, φ (algebraMap _ _ a) =
      algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))
        (MvPolynomial.map (algebraMap Ω₀ Ω) a) := fun a => by
    simp only [φ, liftY, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  have hpoly : ∀ a : MvPolynomial I Ω₀, algebraMap (MvPolynomial I Ω)
      (FractionRing (MvPolynomial I Ω)) (MvPolynomial.map (algebraMap Ω₀ Ω) a) ∈ K := fun a => by
    induction a using MvPolynomial.induction_on with
    | C r =>
      have := K.algebraMap_mem r
      rw [hF] at this
      simpa [MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply Ω (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))] using this
    | add p q hp hq => simpa using K.add_mem hp hq
    | mul_X p i hp =>
      have hX : algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X i) ∈ K :=
        IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
      simpa using K.mul_mem hp hX
  have hmem : ∀ x, φ x ∈ K := fun x => by
    obtain ⟨a, c, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial I Ω₀) x
    rw [map_div₀, hφ, hφ]
    exact K.div_mem (hpoly a) (hpoly c)
  have hle : K ≤ Subfield.toIntermediateField φ.fieldRange (fun r => by
      refine ⟨algebraMap (MvPolynomial I Ω₀) _ (MvPolynomial.C r), ?_⟩
      rw [hφ, hF]
      simp [MvPolynomial.map_C, MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply Ω (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))]) := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨q, rfl⟩
    refine ⟨algebraMap (MvPolynomial I Ω₀) _ (MvPolynomial.X q), ?_⟩
    rw [hφ]; simp
  let ψ : FractionRing (MvPolynomial I Ω₀) →+* K := φ.codRestrict K hmem
  have hψ : Function.Bijective ψ := by
    refine ⟨fun x y h => φ.injective (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨x, hx⟩ := hle y.2
    exact ⟨x, Subtype.ext hx⟩
  rw [← h1]
  exact (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.ofBijective ψ hψ) (RingEquiv.refl _)
    (by ext x; rfl)).symm

/- English proof (translation)
Introduce `Ω₀ Ω _ _ fn I d hd hfin`. Use `letI : Algebra Ω₀ Ω := fn.toAlgebra`. Use `haveI : FiniteDimensional Ω₀ Ω := Module.finite_of_finrank_pos (hfin ▸ hd)`. Use `letI : Algebra Ω₀ (FractionRing (MvPolynomial I Ω)) := ((algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp fn).toAlgebra`. Conclude with `(finrank_fraction_over_adjoin_X_eq Ω₀ Ω I rfl).trans hfin`.
-/
theorem finrank_adjoin_vars : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) (I : Type) (d : ℕ), 0 < d → (letI := fn.toAlgebra; Module.finrank Ω₀ Ω = d) → letI := ((algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp fn).toAlgebra; Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : I => algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X q))) (FractionRing (MvPolynomial I Ω)) = d := by
  intro Ω₀ Ω _ _ fn I d hd hfin
  letI : Algebra Ω₀ Ω := fn.toAlgebra
  haveI : FiniteDimensional Ω₀ Ω := Module.finite_of_finrank_pos (hfin ▸ hd)
  letI : Algebra Ω₀ (FractionRing (MvPolynomial I Ω)) :=
    ((algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp fn).toAlgebra
  exact (finrank_fraction_over_adjoin_X_eq Ω₀ Ω I rfl).trans hfin

end GlobalTheory.CompanionTheory.FieldDeg
