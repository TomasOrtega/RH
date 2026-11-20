import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Decomp
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CondDisc
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CondDvd

namespace KStar.Ram

open NumberField DirichletCharacter IsCyclotomicExtension.Rat
open scoped Pointwise

variable {N : ℕ} [NeZero N] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]

/- English proof (translation)
Rewrite using `[fieldChars, mem_annihilator_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h σ hσ`. Conclude with `h _ ⟨σ, hσ, rfl⟩`. Introduce and unpack `h _ ⟨σ, hσ, rfl⟩`.

Conclude with `h σ hσ`.
-/
private theorem bv_mem (E : IntermediateField ℚ K) (ψ : DirichletCharacter ℂ N) :
    ψ ∈ fieldChars N E ↔ ∀ σ ∈ E.fixingSubgroup, ψ (galEquivZMod N K σ) = 1 := by
  rw [fieldChars, mem_annihilator_iff]
  constructor
  · intro h σ hσ
    exact h _ ⟨σ, hσ, rfl⟩
  · rintro h _ ⟨σ, hσ, rfl⟩
    exact h σ hσ

/- English proof (translation)
Use extensionality with `ψ`. Rewrite using `[bv_mem, mem_intermediateFieldEquivSubgroupChar_iff]`.
-/
private theorem bv_eq [IsAbelianGalois ℚ K] (E : IntermediateField ℚ K) :
    fieldChars N E = intermediateFieldEquivSubgroupChar N K ℂ E := by
  ext ψ
  rw [bv_mem, mem_intermediateFieldEquivSubgroupChar_iff]

/- English proof (translation)
Establish `hζ` using `IsCyclotomicExtension.zeta_spec N ℚ K`. Establish `key : φ.toRatAlgHom.comp (σ : K →ₐ[ℚ] K) = ((starRingEnd ℂ).comp φ).toRatAlgHom`. Apply `(hζ.powerBasis ℚ).algHom_ext` to reduce the goal to its premises. Rewrite using `[IsPrimitiveRoot.powerBasis_gen]`. Express the relevant statement in the definitionally equal form `φ (σ _) = starRingEnd ℂ (φ _)`.

Establish `h1 : ‖φ (IsCyclotomicExtension.zeta N ℚ K)‖ = 1` using `(hζ.map_of_injective φ.injective).norm'_eq_one (NeZero.ne N)`. Rewrite using `[← Complex.inv_eq_conj h1, ← map_inv₀, galEquivZMod_apply_of_pow_eq N K σ hζ.pow_eq_one, hσ]`. Use `congr 1`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]`.

Simplify using the standard rewrite rules. Conclude with `DFunLike.congr_fun key x`.
-/
private theorem bv_conj (σ : Gal(K/ℚ)) (hσ : galEquivZMod N K σ = -1) (φ : K →+* ℂ)
    (x : K) : φ (σ x) = starRingEnd ℂ (φ x) := by
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ K
  have key : φ.toRatAlgHom.comp (σ : K →ₐ[ℚ] K) = ((starRingEnd ℂ).comp φ).toRatAlgHom := by
    apply (hζ.powerBasis ℚ).algHom_ext
    rw [IsPrimitiveRoot.powerBasis_gen]
    change φ (σ _) = starRingEnd ℂ (φ _)
    have h1 : ‖φ (IsCyclotomicExtension.zeta N ℚ K)‖ = 1 :=
      (hζ.map_of_injective φ.injective).norm'_eq_one (NeZero.ne N)
    rw [← Complex.inv_eq_conj h1, ← map_inv₀, galEquivZMod_apply_of_pow_eq N K σ hζ.pow_eq_one, hσ]
    congr 1
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
    simp
  exact DFunLike.congr_fun key x

/- English proof (translation)
Establish `h1 : φ x = ComplexEmbedding.lift K φ (x : K)` using `(ComplexEmbedding.lift_algebraMap_apply K φ x).symm`. Rewrite using `[h1, RCLike.star_def, ← bv_conj σ hσ, (ComplexEmbedding.lift K φ).injective.eq_iff]`.
-/
private theorem bv_real (σ : Gal(K/ℚ)) (hσ : galEquivZMod N K σ = -1) (E : IntermediateField ℚ K)
    (φ : E →+* ℂ) (x : E) : star (φ x) = φ x ↔ σ x = x := by
  have h1 : φ x = ComplexEmbedding.lift K φ (x : K) :=
    (ComplexEmbedding.lift_algebraMap_apply K φ x).symm
  rw [h1, RCLike.star_def, ← bv_conj σ hσ, (ComplexEmbedding.lift K φ).injective.eq_iff]

/- English proof (translation)
Establish `h` using `(card_fieldChars (N := N) E).2`. Take `⟨σ, hσ⟩` from `(galEquivZMod N K).surjective (-1)`. Prove the components needed by the constructor for the conclusion. Introduce `hc`. Assume the negation of the conclusion as `hne`.

Use `push Not at hne`. Establish `hr` using `h.2 fun ψ hψ => ψ.even_or_odd.resolve_right (hne ψ hψ)`. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Conclude with `IsTotallyComplex.complexEmbedding_not_isReal φ (IsTotallyReal.complexEmbedding_isReal φ)`. Introduce and unpack `⟨ψ, hψ, hodd⟩`.

Use `⟨fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]`. Introduce `hw`. Use `hodd.not_even ψ (h.1 ⟨fun w' => ?_⟩ ψ hψ)` and prove the remaining obligations. Rewrite using `[InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]`.

Use extensionality with `x`. Conclude with `(bv_real σ hσ E _ x).2 ((bv_real σ hσ E _ x).1 (RingHom.congr_fun hw x))`.
-/
private theorem bv_complex (E : IntermediateField ℚ K) :
    IsTotallyComplex E ↔ ∃ ψ ∈ fieldChars N E, ψ.Odd := by
  have h := (card_fieldChars (N := N) E).2
  obtain ⟨σ, hσ⟩ := (galEquivZMod N K).surjective (-1)
  constructor
  · intro hc
    by_contra hne
    push Not at hne
    have hr := h.2 fun ψ hψ => ψ.even_or_odd.resolve_right (hne ψ hψ)
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact IsTotallyComplex.complexEmbedding_not_isReal φ (IsTotallyReal.complexEmbedding_isReal φ)
  · rintro ⟨ψ, hψ, hodd⟩
    refine ⟨fun w => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff,
      ComplexEmbedding.isReal_iff]
    intro hw
    refine hodd.not_even ψ (h.1 ⟨fun w' => ?_⟩ ψ hψ)
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    exact (bv_real σ hσ E _ x).2 ((bv_real σ hσ E _ x).1 (RingHom.congr_fun hw x))

/- English proof (translation)
Establish `: IsAbelianGalois ℚ K` using `IsCyclotomicExtension.isAbelianGalois {N} ℚ K`. Use `⟨?_, fun E E' => ⟨?_, ?_, ?_, (annihilator_charKer ⊥ (fieldUnits N E)).2.1⟩⟩` and prove the remaining obligations. Simplify using `only [bv_eq]`. Conclude with `(intermediateFieldEquivSubgroupChar N K ℂ).bijective`. Rewrite using `[bv_eq, bv_eq, OrderIso.le_iff_le]`.

Rewrite using `[bv_eq, bv_eq, bv_eq, OrderIso.map_sup]`. Rewrite using `[bv_eq, bv_eq, bv_eq, OrderIso.map_inf]`.
-/
theorem fieldChars_lattice :
    Function.Bijective (fun E : IntermediateField ℚ K => fieldChars N E) ∧
      ∀ E E' : IntermediateField ℚ K, (fieldChars N E ≤ fieldChars N E' ↔ E ≤ E') ∧
        fieldChars N (E ⊔ E') = fieldChars N E ⊔ fieldChars N E' ∧
        fieldChars N (E ⊓ E') = fieldChars N E ⊓ fieldChars N E' ∧
        charKer (fieldChars N E) = fieldUnits N E := by
  have : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {N} ℚ K
  refine ⟨?_, fun E E' => ⟨?_, ?_, ?_, (annihilator_charKer ⊥ (fieldUnits N E)).2.1⟩⟩
  · simp only [bv_eq]
    exact (intermediateFieldEquivSubgroupChar N K ℂ).bijective
  · rw [bv_eq, bv_eq, OrderIso.le_iff_le]
  · rw [bv_eq, bv_eq, bv_eq, OrderIso.map_sup]
  · rw [bv_eq, bv_eq, bv_eq, OrderIso.map_inf]

/- English proof (translation)
Establish `hcard` using `(card_fieldChars (N := N) E).1`. Establish `hdisc` using `(natAbs_discr_eq_finprod_conductor (N := N) E).1`. Establish `hsign` using `sign_discr E`. Establish `hcx` using `bv_complex (N := N) E`. Establish `hprod : ∀ ψ ∈ fieldChars N E, ψ.Odd → Nat.card (fieldChars N E) = 2 → (discr E).natAbs = ψ.conductor ∧ fieldChars N E = Subgroup.zpowers ψ ∧ ψ ^ 2 = 1`.

Introduce `ψ hψ hodd h2`. Rewrite using `[hdisc]`. Generalize the expression as in `fieldChars N E = X at hψ h2`. Establish `hne : (⟨ψ, hψ⟩ : X) ≠ 1`. Introduce `h`.

Establish `h' : ψ = 1` using `congrArg Subtype.val h`. Apply `hodd.not_even ψ` to reduce the goal to its premises. Rewrite using `[h', DirichletCharacter.Even]`. Conclude with `MulChar.one_apply (isUnit_one.neg)`. Establish `hall : ∀ χ : X, χ = 1 ∨ χ = ⟨ψ, hψ⟩`.

Introduce `χ`. Establish `h3` using `(Nat.card_eq_two_iff' (1 : X)).1 h2`. Distinguish the cases in `h1 : χ = 1`. Conclude with `Or.inl h1`. Conclude with `Or.inr (h3.unique h1 hne)`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[finprod_eq_single _ (⟨ψ, hψ⟩ : X)]`. Introduce `χ hχ`. Rewrite using `[(hall χ).resolve_right hχ]`. Conclude with `conductor_one`.

Use `le_antisymm (fun χ hχ => ?_) (by simpa using hψ)` and prove the remaining obligations. Break down `hall ⟨χ, hχ⟩ with h | h` into its components or cases. Rewrite using `[show χ = 1 from congrArg Subtype.val h]`. Conclude with `one_mem _`. Rewrite using `[show χ = ψ from congrArg Subtype.val h]`.

Conclude with `Subgroup.mem_zpowers _`. Establish `h4 : (⟨ψ, hψ⟩ : X) ^ Nat.card X = 1` using `pow_card_eq_one'`. Rewrite `h4` using `[h2]`. Conclude with `congrArg Subtype.val h4`. Establish `hrk` using `InfinitePlace.card_add_two_mul_card_eq_rank E`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h2, hd⟩`. Establish `hneg : discr E < 0` using `lt_of_le_of_ne (by omega) (discr_ne_zero E)`. Rewrite `hsign` using `[Int.sign_eq_neg_one_of_neg hneg]`. Establish `h0 : InfinitePlace.nrComplexPlaces E ≠ 0`.

Introduce `h`. Rewrite `hsign` using `[h]`. Simplify using `at hsign`. Take `⟨ψ, hψ, hodd⟩` from `hcx.1 (nrRealPlaces_eq_zero_iff.1 (by omega))`. Take `⟨a, b, c⟩` from `hprod ψ hψ hodd (hcard.trans h2)`.

Conclude with `⟨ψ, ⟨c, hodd, by omega⟩, b⟩`. Introduce and unpack `⟨ψ, ⟨h1, hodd, hc⟩, hX⟩`. Establish `hψ : ψ ∈ fieldChars N E` using `hX ▸ Subgroup.mem_zpowers ψ`. Establish `hne : ψ ≠ 1`. Introduce `h'`.

Apply `hodd.not_even ψ` to reduce the goal to its premises. Rewrite using `[h', DirichletCharacter.Even]`. Conclude with `MulChar.one_apply (isUnit_one.neg)`. Establish `h2 : Nat.card (fieldChars N E) = 2`. Rewrite using `[hX, Nat.card_zpowers, orderOf_eq_prime h1 hne]`.

Establish `h0` using `nrRealPlaces_eq_zero_iff.2 (hcx.2 ⟨ψ, hψ, hodd⟩)`. Establish `h3 : InfinitePlace.nrComplexPlaces E = 1` using `by omega`. Rewrite `hsign` using `[h3, pow_one, Int.sign_eq_neg_one_iff_neg]`. Use `(hprod ψ hψ hodd h2).1` as an intermediate fact. Conclude with `⟨by omega, by omega⟩`.
-/
theorem quadratic_discr_iff (E : IntermediateField ℚ K) (d : ℕ) :
    (Module.finrank ℚ E = 2 ∧ discr E = -(d : ℤ)) ↔
      ∃ ψ, IsImagQuad ψ d ∧ fieldChars N E = Subgroup.zpowers ψ := by
  have hcard := (card_fieldChars (N := N) E).1
  have hdisc := (natAbs_discr_eq_finprod_conductor (N := N) E).1
  have hsign := sign_discr E
  have hcx := bv_complex (N := N) E
  have hprod : ∀ ψ ∈ fieldChars N E, ψ.Odd → Nat.card (fieldChars N E) = 2 →
      (discr E).natAbs = ψ.conductor ∧ fieldChars N E = Subgroup.zpowers ψ ∧ ψ ^ 2 = 1 := by
    intro ψ hψ hodd h2
    rw [hdisc]
    generalize fieldChars N E = X at hψ h2
    have hne : (⟨ψ, hψ⟩ : X) ≠ 1 := by
      intro h
      have h' : ψ = 1 := congrArg Subtype.val h
      apply hodd.not_even ψ
      rw [h', DirichletCharacter.Even]
      exact MulChar.one_apply (isUnit_one.neg)
    have hall : ∀ χ : X, χ = 1 ∨ χ = ⟨ψ, hψ⟩ := by
      intro χ
      have h3 := (Nat.card_eq_two_iff' (1 : X)).1 h2
      by_cases h1 : χ = 1
      · exact Or.inl h1
      · exact Or.inr (h3.unique h1 hne)
    refine ⟨?_, ?_, ?_⟩
    · rw [finprod_eq_single _ (⟨ψ, hψ⟩ : X)]
      intro χ hχ
      rw [(hall χ).resolve_right hχ]
      exact conductor_one
    · refine le_antisymm (fun χ hχ => ?_) (by simpa using hψ)
      rcases hall ⟨χ, hχ⟩ with h | h
      · rw [show χ = 1 from congrArg Subtype.val h]
        exact one_mem _
      · rw [show χ = ψ from congrArg Subtype.val h]
        exact Subgroup.mem_zpowers _
    · have h4 : (⟨ψ, hψ⟩ : X) ^ Nat.card X = 1 := pow_card_eq_one'
      rw [h2] at h4
      exact congrArg Subtype.val h4
  have hrk := InfinitePlace.card_add_two_mul_card_eq_rank E
  constructor
  · rintro ⟨h2, hd⟩
    have hneg : discr E < 0 := lt_of_le_of_ne (by omega) (discr_ne_zero E)
    rw [Int.sign_eq_neg_one_of_neg hneg] at hsign
    have h0 : InfinitePlace.nrComplexPlaces E ≠ 0 := by
      intro h
      rw [h] at hsign
      simp at hsign
    obtain ⟨ψ, hψ, hodd⟩ := hcx.1 (nrRealPlaces_eq_zero_iff.1 (by omega))
    obtain ⟨a, b, c⟩ := hprod ψ hψ hodd (hcard.trans h2)
    exact ⟨ψ, ⟨c, hodd, by omega⟩, b⟩
  · rintro ⟨ψ, ⟨h1, hodd, hc⟩, hX⟩
    have hψ : ψ ∈ fieldChars N E := hX ▸ Subgroup.mem_zpowers ψ
    have hne : ψ ≠ 1 := by
      intro h'
      apply hodd.not_even ψ
      rw [h', DirichletCharacter.Even]
      exact MulChar.one_apply (isUnit_one.neg)
    have h2 : Nat.card (fieldChars N E) = 2 := by
      rw [hX, Nat.card_zpowers, orderOf_eq_prime h1 hne]
    have h0 := nrRealPlaces_eq_zero_iff.2 (hcx.2 ⟨ψ, hψ, hodd⟩)
    have h3 : InfinitePlace.nrComplexPlaces E = 1 := by omega
    rw [h3, pow_one, Int.sign_eq_neg_one_iff_neg] at hsign
    have := (hprod ψ hψ hodd h2).1
    exact ⟨by omega, by omega⟩

end KStar.Ram
