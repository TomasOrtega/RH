import Mathlib

namespace ModelDimension

open MvPolynomial

/- English proof (translation)
Introduce `κ K L I _ _ _ _ ψ T hT`. Set `f : κ →+* L` to `(algebraMap K L).comp ψ.toRingHom`. Set `ρ : MvPolynomial I κ →+* L` to `MvPolynomial.eval₂Hom f T`. Establish `hρ : ∀ p, ρ p = MvPolynomial.aeval T (MvPolynomial.map ψ.toRingHom p)`. Introduce `p`.

Simplify using `[ρ, f, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]`. Establish `hinj : Function.Injective ρ`. Introduce `p q h`. Rewrite `h` using `[hρ, hρ]`. Conclude with `MvPolynomial.map_injective _ ψ.injective (hT h)`.

Set `φ : FractionRing (MvPolynomial I κ) →+* L` to `IsFractionRing.lift hinj`. Establish `hφ : ∀ p, φ (algebraMap (MvPolynomial I κ) _ p) = ρ p` using `IsFractionRing.lift_algebraMap hinj`. Use `⟨φ, fun a => by rw [hφ]; simp [ρ, f], fun i => by rw [hφ]; simp [ρ], ?_⟩` and prove the remaining obligations. Set `S` to `IntermediateField.adjoin K (Set.range T)`. Establish `hρS : ∀ p, ρ p ∈ S`.

Introduce `p`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp [ρ, f]`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `S.add_mem hp hq`.

Consider the case `mul_X p i hp`. Rewrite using `[map_mul]`. Conclude with `S.mul_mem hp (by simpa [ρ] using IntermediateField.subset_adjoin K (Set.range T) ⟨i, rfl⟩)`. Establish `hφS : ∀ x, φ x ∈ S`. Introduce `x`.

Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := MvPolynomial I κ) x`. Rewrite using `[map_div₀, hφ, hφ]`. Conclude with `S.div_mem (hρS a) (hρS b)`. Establish `hS : S ≤ φ.fieldRange.toIntermediateField (K` using `K) (fun k => RingHom.mem_fieldRange.2 ⟨algebraMap _ _ (MvPolynomial.C (ψ.symm k)), by rw [hφ]; simp [ρ, f]⟩) := by`. Rewrite using `[IntermediateField.adjoin_le_iff]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `RingHom.mem_fieldRange.2 ⟨algebraMap _ _ (MvPolynomial.X i), by rw [hφ]; simp [ρ]⟩`. Set `g : FractionRing (MvPolynomial I κ) →+* S` to `φ.codRestrict S hφS`. Establish `hg : Function.Bijective g`. Use `⟨fun x y h => φ.injective (congrArg Subtype.val h), ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨s, hs⟩`. Take `⟨x, hx⟩` from `RingHom.mem_fieldRange.1 (hS hs)`. Conclude with `⟨x, Subtype.ext hx⟩`. Set `_` to `φ.toAlgebra`. Conclude with `Algebra.finrank_eq_of_equiv_equiv (RingEquiv.ofBijective g hg) (RingEquiv.refl L) (RingHom.ext fun x => rfl)`.
-/
theorem polynomial_fraction_field_degree : ∀ (κ K L I : Type) [Field κ] [Field K] [Field L] [Algebra K L] (ψ : κ ≃+* K) (T : I → L), AlgebraicIndependent K T → ∃ φ : FractionRing (MvPolynomial I κ) →+* L, (∀ a, φ (algebraMap (MvPolynomial I κ) _ (MvPolynomial.C a)) = algebraMap K L (ψ a)) ∧ (∀ i, φ (algebraMap (MvPolynomial I κ) _ (MvPolynomial.X i)) = T i) ∧ (letI := φ.toAlgebra; Module.finrank (FractionRing (MvPolynomial I κ)) L) = Module.finrank (IntermediateField.adjoin K (Set.range T)) L := by
  intro κ K L I _ _ _ _ ψ T hT
  let f : κ →+* L := (algebraMap K L).comp ψ.toRingHom
  let ρ : MvPolynomial I κ →+* L := MvPolynomial.eval₂Hom f T
  have hρ : ∀ p, ρ p = MvPolynomial.aeval T (MvPolynomial.map ψ.toRingHom p) := by
    intro p
    simp [ρ, f, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  have hinj : Function.Injective ρ := by
    intro p q h
    rw [hρ, hρ] at h
    exact MvPolynomial.map_injective _ ψ.injective (hT h)
  let φ : FractionRing (MvPolynomial I κ) →+* L := IsFractionRing.lift hinj
  have hφ : ∀ p, φ (algebraMap (MvPolynomial I κ) _ p) = ρ p := IsFractionRing.lift_algebraMap hinj
  refine ⟨φ, fun a => by rw [hφ]; simp [ρ, f], fun i => by rw [hφ]; simp [ρ], ?_⟩
  let S := IntermediateField.adjoin K (Set.range T)
  have hρS : ∀ p, ρ p ∈ S := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp [ρ, f]
    | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact S.mul_mem hp (by simpa [ρ] using IntermediateField.subset_adjoin K (Set.range T) ⟨i, rfl⟩)
  have hφS : ∀ x, φ x ∈ S := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial I κ) x
    rw [map_div₀, hφ, hφ]
    exact S.div_mem (hρS a) (hρS b)
  have hS : S ≤ φ.fieldRange.toIntermediateField (K := K) (fun k =>
      RingHom.mem_fieldRange.2 ⟨algebraMap _ _ (MvPolynomial.C (ψ.symm k)), by rw [hφ]; simp [ρ, f]⟩) := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact RingHom.mem_fieldRange.2 ⟨algebraMap _ _ (MvPolynomial.X i), by rw [hφ]; simp [ρ]⟩
  let g : FractionRing (MvPolynomial I κ) →+* S := φ.codRestrict S hφS
  have hg : Function.Bijective g := by
    refine ⟨fun x y h => φ.injective (congrArg Subtype.val h), ?_⟩
    rintro ⟨s, hs⟩
    obtain ⟨x, hx⟩ := RingHom.mem_fieldRange.1 (hS hs)
    exact ⟨x, Subtype.ext hx⟩
  let _ := φ.toAlgebra
  exact Algebra.finrank_eq_of_equiv_equiv (RingEquiv.ofBijective g hg) (RingEquiv.refl L)
    (RingHom.ext fun x => rfl)

end ModelDimension
