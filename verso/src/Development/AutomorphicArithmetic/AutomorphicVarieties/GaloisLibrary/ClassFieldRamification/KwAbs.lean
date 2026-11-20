import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Kw

open NumberField IsDedekindDomain IntermediateField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

/- English proof (translation)
Introduce `Ω _ alg hc V hV hcomm`. Use `haveI : CharZero Ω := algebraRat.charZero Ω`. Take `rfl : alg = DivisionRing.toRatAlgebra` from `Subsingleton.elim _ _`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`.

Use `haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω`. Establish `hcl : IsClosed (V : Set (Ω ≃ₐ[ℚ] Ω))` using `Subgroup.isClosed_of_isOpen V hV`. Use `set L : IntermediateField ℚ Ω := IntermediateField.fixedField (V : Subgroup (Ω ≃ₐ[ℚ] Ω)) with hL`. Establish `hfix : L.fixingSubgroup = V` using `InfiniteGalois.fixingSubgroup_fixedField ⟨V, hcl⟩`. Establish `hnorm : V.Normal` using `⟨fun n hn g => by`.

Establish `h : g * n * g⁻¹ * n⁻¹ ∈ V` using `hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))`. Use `mul_mem h hn` as an intermediate fact. Rewrite using `[inv_mul_cancel_right] at this⟩` and apply the resulting hypothesis. Use `haveI hfin : FiniteDimensional ℚ L := (InfiniteGalois.isOpen_iff_finite L).1 (by rw [hfix]; exact hV)`. Use `haveI hgal : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois L).1 (by rw [hfix]; exact hnorm)`.

Establish `hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F` using `ℚ) (K₁ := Ω) L) := AlgEquiv.restrictNormalHom_surjective Ω`. Establish `hker : (AlgEquiv.restrictNormalHom (F` using `ℚ) (K₁ := Ω) L).ker = V := (@IntermediateField.restrictNormalHom_ker ℚ Ω _ _ _ L hgal.to_normal).trans hfix`. Use `haveI hab : IsAbelianGalois ℚ L := { is_comm := ⟨fun a b => by`. Take `⟨a, rfl⟩` from `hsurj a`. Take `⟨b, rfl⟩` from `hsurj b`.

Establish `h : a * b * a⁻¹ * b⁻¹ ∈ V` using `hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))`. Rewrite `h` using `[← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]`. Conclude with `h⟩ }`. Take `⟨N, ζ, hN, hζ, hle⟩` from `UpperTheory.V.CF.kw Ω L`. Use `⟨N, hN, fun g hg => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hfix]`. Use `IntermediateField.fixingSubgroup_le hle ?_` and prove the remaining obligations. Establish `h1 : ℚ⟮ζ⟯ ≤ IntermediateField.fixedField (Subgroup.zpowers (g : Ω ≃ₐ[ℚ] Ω))`. Rewrite using `[IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]`. Introduce `f hf`.

Establish `: Subgroup.zpowers (g : Ω ≃ₐ[ℚ] Ω) ≤ MulAction.stabilizer _ ζ` using `Subgroup.zpowers_le.2 (hg ζ hζ.pow_eq_one)`. Conclude with `this hf`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Conclude with `(IntermediateField.mem_fixedField_iff _ _).1 (h1 hx) g (Subgroup.mem_zpowers g)`.
-/
theorem UpperTheory.V.CF.kwAbs :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (V : Subgroup (G ℚ Ω)), IsOpen (V : Set (G ℚ Ω)) → commutator (G ℚ Ω) ≤ V → ∃ N : ℕ, 0 < N ∧ ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ) → g ∈ V := by
  intro Ω _ alg hc V hV hcomm
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : alg = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hcl : IsClosed (V : Set (Ω ≃ₐ[ℚ] Ω)) := Subgroup.isClosed_of_isOpen V hV
  set L : IntermediateField ℚ Ω := IntermediateField.fixedField (V : Subgroup (Ω ≃ₐ[ℚ] Ω)) with hL
  have hfix : L.fixingSubgroup = V := InfiniteGalois.fixingSubgroup_fixedField ⟨V, hcl⟩
  have hnorm : V.Normal := ⟨fun n hn g => by
    have h : g * n * g⁻¹ * n⁻¹ ∈ V :=
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have := mul_mem h hn
    rwa [inv_mul_cancel_right] at this⟩
  haveI hfin : FiniteDimensional ℚ L := (InfiniteGalois.isOpen_iff_finite L).1 (by rw [hfix]; exact hV)
  haveI hgal : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois L).1 (by rw [hfix]; exact hnorm)
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) L) :=
    AlgEquiv.restrictNormalHom_surjective Ω
  have hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) L).ker = V :=
    (@IntermediateField.restrictNormalHom_ker ℚ Ω _ _ _ L hgal.to_normal).trans hfix
  haveI hab : IsAbelianGalois ℚ L :=
    { is_comm := ⟨fun a b => by
        obtain ⟨a, rfl⟩ := hsurj a
        obtain ⟨b, rfl⟩ := hsurj b
        have h : a * b * a⁻¹ * b⁻¹ ∈ V :=
          hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
        rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
          mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
        exact h⟩ }
  obtain ⟨N, ζ, hN, hζ, hle⟩ := UpperTheory.V.CF.kw Ω L
  refine ⟨N, hN, fun g hg => ?_⟩
  rw [← hfix]
  refine IntermediateField.fixingSubgroup_le hle ?_
  have h1 : ℚ⟮ζ⟯ ≤ IntermediateField.fixedField (Subgroup.zpowers (g : Ω ≃ₐ[ℚ] Ω)) := by
    rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
    intro f hf
    have : Subgroup.zpowers (g : Ω ≃ₐ[ℚ] Ω) ≤ MulAction.stabilizer _ ζ :=
      Subgroup.zpowers_le.2 (hg ζ hζ.pow_eq_one)
    exact this hf
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).1 (h1 hx) g (Subgroup.mem_zpowers g)
