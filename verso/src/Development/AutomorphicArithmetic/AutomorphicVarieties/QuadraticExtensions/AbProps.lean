import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Introduce `A L _ _ hA`. Take `⟨N, hN, j, ζ, hmN, hζ, h⟩` from `hA`. Use `haveI := hN`. Use `haveI hcN : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ`. Use `haveI hab : IsAbelianGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isAbelianGalois {N} ℚ (CyclotomicField N ℚ)`.

Establish `hfix : ∀ τ : Gal(CyclotomicField N ℚ/ℚ), τ ∈ j.fieldRange.fixingSubgroup ↔ ∀ y : L, τ (j y) = j y`. Introduce `τ`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `H y`.

Conclude with `H _ (AlgHom.mem_fieldRange.2 ⟨y, rfl⟩)`. Introduce `H x hx`. Take `⟨y, rfl⟩` from `AlgHom.mem_fieldRange.1 hx`. Conclude with `H y`. Establish `hpow : ∀ τ : Gal(CyclotomicField N ℚ/ℚ), τ ζ = ζ ^ ((hζ.autToPow ℚ τ : ZMod N).val)` using `fun τ => (IsPrimitiveRoot.autToPow_spec ℚ hζ τ).symm`.

Establish `hker : ∀ v : (ZMod N)ˣ, A.ker ((v : ZMod N).val) ↔ ZMod.unitsMap hmN v ∈ A.H`. Introduce `v`. Establish `hc : ((ZMod.unitsMap hmN v : (ZMod A.m)ˣ) : ZMod A.m) = (((v : ZMod N).val : ℕ) : ZMod A.m)`. Rewrite using `[ZMod.natCast_val]`. Both sides reduce to the same expression.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, hua⟩`. Establish `: u = ZMod.unitsMap hmN v` using `Units.ext (hua.trans hc.symm)`. Rewrite using `[← this]` and apply the resulting hypothesis. Introduce `hv`.

Conclude with `⟨_, hv, hc⟩`. Establish `hinj : Function.Injective (hζ.autToPow ℚ)` using `hζ.autToPow_injective ℚ`. Establish `hcard : Nat.card Gal(CyclotomicField N ℚ/ℚ) = Nat.card (ZMod N)ˣ` using `Nat.card_congr (IsCyclotomicExtension.autEquivPow (CyclotomicField N ℚ) (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_neZero N))).toEquiv`. Establish `hsurj : Function.Surjective (hζ.autToPow ℚ)` using `((Nat.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩).2`. Use `⟨IsAbelianGalois.of_algHom j, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[(AlgEquiv.ofInjectiveField j).toLinearEquiv.finrank_eq]`. Express the relevant statement in the definitionally equal form `Module.finrank ℚ j.fieldRange = _`. Rewrite using `[IntermediateField.finrank_eq_fixingSubgroup_index]`. Establish `hS : j.fieldRange.fixingSubgroup = (A.H.comap (ZMod.unitsMap hmN)).comap (hζ.autToPow ℚ)`. Use extensionality with `τ`.

Rewrite using `[hfix, h τ _ (hpow τ)]`. Conclude with `hker _`. Rewrite using `[hS, Subgroup.index_comap_of_surjective _ hsurj, Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective hmN)]`. Both sides reduce to the same expression. Establish `hdvd : N / A.m ∣ N` using `Nat.div_dvd_of_dvd hmN`.

Establish `hp0 : N / A.m ≠ 0` using `(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hmN) A.pos).ne'`. Establish `hζm : IsPrimitiveRoot (ζ ^ (N / A.m)) A.m`. Use `hζ.pow_of_dvd hp0 hdvd` as an intermediate fact. Rewrite `this` using `[Nat.div_div_self hmN (NeZero.ne N)]`. Then use the resulting hypothesis. Use `haveI : NeZero A.m := ⟨A.pos.ne'⟩`.

Use `haveI hcm : IsCyclotomicExtension {A.m} ℚ (CyclotomicField A.m ℚ) := CyclotomicField.isCyclotomicExtension A.m ℚ`. Use `haveI : IsCyclotomicExtension {A.m} ℚ (IntermediateField.adjoin ℚ {ζ ^ (N / A.m)}) := hζm.intermediateField_adjoin_isCyclotomicExtension ℚ`. Establish `hMC : j.fieldRange ≤ IntermediateField.adjoin ℚ {ζ ^ (N / A.m)}`. Rewrite using `[← IsGalois.fixedField_fixingSubgroup (IntermediateField.adjoin ℚ {ζ ^ (N / A.m)}), IntermediateField.le_iff_le]`. Introduce `τ hτ`.

Rewrite using `[hfix, h τ _ (hpow τ)]`. Rewrite `hτ` using `[IntermediateField.mem_fixingSubgroup_iff]`. Establish `h1 : τ (ζ ^ (N / A.m)) = ζ ^ (N / A.m)` using `hτ _ (IntermediateField.mem_adjoin_simple_self ℚ _)`. Rewrite `h1` using `[map_pow, hpow τ, ← pow_mul, mul_comm, pow_mul]`. Generalize the expression as in `((hζ.autToPow ℚ τ : ZMod N)).val = a at h1 ⊢`.

Establish `hfo : IsOfFinOrder (ζ ^ (N / A.m))` using `isOfFinOrder_iff_pow_eq_one.2 ⟨A.m, A.pos, hζm.pow_eq_one⟩`. Establish `h2 : a ≡ 1 [MOD A.m]`. Rewrite using `[hζm.eq_orderOf]`. Conclude with `hfo.pow_eq_pow_iff_modEq.1 (by rw [pow_one]; exact h1)`. Use `⟨1, one_mem _, ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]`. Conclude with `h2.symm`. Conclude with `⟨(IsCyclotomicExtension.algEquiv {A.m} ℚ (IntermediateField.adjoin ℚ {ζ ^ (N / A.m)}) (CyclotomicField A.m ℚ)).toAlgHom.comp ((IntermediateField.inclusion hMC).comp (AlgEquiv.ofInjectiveField j).toAlgHom)⟩`.
-/
theorem UpperTheory.V.Two.abProps :
    ∀ (A : AbF) (L : Type) [Field L] [NumberField L], IsAbField A L → IsAbelianGalois ℚ L ∧ Module.finrank ℚ L = A.deg ∧ Nonempty (L →ₐ[ℚ] CyclotomicField A.m ℚ) := by
  intro A L _ _ hA
  obtain ⟨N, hN, j, ζ, hmN, hζ, h⟩ := hA
  haveI := hN
  haveI hcN : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  haveI hab : IsAbelianGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {N} ℚ (CyclotomicField N ℚ)
  have hfix : ∀ τ : Gal(CyclotomicField N ℚ/ℚ),
      τ ∈ j.fieldRange.fixingSubgroup ↔ ∀ y : L, τ (j y) = j y := by
    intro τ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro H y
      exact H _ (AlgHom.mem_fieldRange.2 ⟨y, rfl⟩)
    · intro H x hx
      obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.1 hx
      exact H y
  have hpow : ∀ τ : Gal(CyclotomicField N ℚ/ℚ), τ ζ = ζ ^ ((hζ.autToPow ℚ τ : ZMod N).val) :=
    fun τ => (IsPrimitiveRoot.autToPow_spec ℚ hζ τ).symm
  have hker : ∀ v : (ZMod N)ˣ, A.ker ((v : ZMod N).val) ↔ ZMod.unitsMap hmN v ∈ A.H := by
    intro v
    have hc : ((ZMod.unitsMap hmN v : (ZMod A.m)ˣ) : ZMod A.m) = (((v : ZMod N).val : ℕ) : ZMod A.m) := by
      rw [ZMod.natCast_val]
      rfl
    constructor
    · rintro ⟨u, hu, hua⟩
      have : u = ZMod.unitsMap hmN v := Units.ext (hua.trans hc.symm)
      rwa [← this]
    · intro hv
      exact ⟨_, hv, hc⟩
  have hinj : Function.Injective (hζ.autToPow ℚ) := hζ.autToPow_injective ℚ
  have hcard : Nat.card Gal(CyclotomicField N ℚ/ℚ) = Nat.card (ZMod N)ˣ :=
    Nat.card_congr (IsCyclotomicExtension.autEquivPow (CyclotomicField N ℚ)
      (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_neZero N))).toEquiv
  have hsurj : Function.Surjective (hζ.autToPow ℚ) :=
    ((Nat.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩).2
  refine ⟨IsAbelianGalois.of_algHom j, ?_, ?_⟩
  · rw [(AlgEquiv.ofInjectiveField j).toLinearEquiv.finrank_eq]
    change Module.finrank ℚ j.fieldRange = _
    rw [IntermediateField.finrank_eq_fixingSubgroup_index]
    have hS : j.fieldRange.fixingSubgroup = (A.H.comap (ZMod.unitsMap hmN)).comap (hζ.autToPow ℚ) := by
      ext τ
      rw [hfix, h τ _ (hpow τ)]
      exact hker _
    rw [hS, Subgroup.index_comap_of_surjective _ hsurj,
      Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective hmN)]
    rfl
  · have hdvd : N / A.m ∣ N := Nat.div_dvd_of_dvd hmN
    have hp0 : N / A.m ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hmN) A.pos).ne'
    have hζm : IsPrimitiveRoot (ζ ^ (N / A.m)) A.m := by
      have := hζ.pow_of_dvd hp0 hdvd
      rwa [Nat.div_div_self hmN (NeZero.ne N)] at this
    haveI : NeZero A.m := ⟨A.pos.ne'⟩
    haveI hcm : IsCyclotomicExtension {A.m} ℚ (CyclotomicField A.m ℚ) :=
      CyclotomicField.isCyclotomicExtension A.m ℚ
    haveI : IsCyclotomicExtension {A.m} ℚ (IntermediateField.adjoin ℚ {ζ ^ (N / A.m)}) :=
      hζm.intermediateField_adjoin_isCyclotomicExtension ℚ
    have hMC : j.fieldRange ≤ IntermediateField.adjoin ℚ {ζ ^ (N / A.m)} := by
      rw [← IsGalois.fixedField_fixingSubgroup (IntermediateField.adjoin ℚ {ζ ^ (N / A.m)}),
        IntermediateField.le_iff_le]
      intro τ hτ
      rw [hfix, h τ _ (hpow τ)]
      rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
      have h1 : τ (ζ ^ (N / A.m)) = ζ ^ (N / A.m) :=
        hτ _ (IntermediateField.mem_adjoin_simple_self ℚ _)
      rw [map_pow, hpow τ, ← pow_mul, mul_comm, pow_mul] at h1
      generalize ((hζ.autToPow ℚ τ : ZMod N)).val = a at h1 ⊢
      have hfo : IsOfFinOrder (ζ ^ (N / A.m)) :=
        isOfFinOrder_iff_pow_eq_one.2 ⟨A.m, A.pos, hζm.pow_eq_one⟩
      have h2 : a ≡ 1 [MOD A.m] := by
        rw [hζm.eq_orderOf]
        exact hfo.pow_eq_pow_iff_modEq.1 (by rw [pow_one]; exact h1)
      refine ⟨1, one_mem _, ?_⟩
      rw [Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact h2.symm
    exact ⟨(IsCyclotomicExtension.algEquiv {A.m} ℚ (IntermediateField.adjoin ℚ {ζ ^ (N / A.m)})
      (CyclotomicField A.m ℚ)).toAlgHom.comp
        ((IntermediateField.inclusion hMC).comp (AlgEquiv.ofInjectiveField j).toAlgHom)⟩
