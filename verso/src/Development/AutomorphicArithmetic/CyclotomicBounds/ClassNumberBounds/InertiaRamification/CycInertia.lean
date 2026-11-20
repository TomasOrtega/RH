import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.BridgeDefs
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ConductorLocalPartDvdIff

namespace KStar.Ram

open NumberField DirichletCharacter IsCyclotomicExtension.Rat
open scoped Pointwise

variable {N : ℕ} [NeZero N] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]

/- English proof (translation)
Establish `hne : NeZero (ordCompl[l] N)` using `⟨(Nat.ordCompl_pos l (NeZero.ne N)).ne'⟩`. Establish `h1` using `Subgroup.card_mul_index (H.comap (ZMod.unitsMap (Nat.ordCompl_dvd N l)))`. Establish `h2` using `Subgroup.card_mul_index H`. Rewrite `h1` using `[Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective _)]`. Rewrite `h1` using `[Nat.card_eq_fintype_card (α := (ZMod N)ˣ), ZMod.card_units_eq_totient]`.

Rewrite `h2` using `[Nat.card_eq_fintype_card (α := (ZMod (ordCompl[l] N))ˣ), ZMod.card_units_eq_totient]`. Establish `h3 : Nat.totient N = Nat.totient (ordProj[l] N) * Nat.totient (ordCompl[l] N)`. Rewrite using `[← Nat.totient_mul (Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl.out (NeZero.ne N))), Nat.ordProj_mul_ordCompl_eq_self]`. Establish `h4 : H.index ≠ 0` using `Subgroup.index_ne_zero_of_finite`. Apply `Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h4)` to reduce the goal to its premises.

Rewrite using `[h1, h3, ← h2, mul_assoc]`.
-/
private theorem cycInertia_card_comap (l : ℕ) [hl : Fact l.Prime]
    (H : Subgroup (ZMod (ordCompl[l] N))ˣ) :
    Nat.card (H.comap (ZMod.unitsMap (Nat.ordCompl_dvd N l))) =
      Nat.totient (ordProj[l] N) * Nat.card H := by
  have hne : NeZero (ordCompl[l] N) := ⟨(Nat.ordCompl_pos l (NeZero.ne N)).ne'⟩
  have h1 := Subgroup.card_mul_index (H.comap (ZMod.unitsMap (Nat.ordCompl_dvd N l)))
  have h2 := Subgroup.card_mul_index H
  rw [Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective _)] at h1
  rw [Nat.card_eq_fintype_card (α := (ZMod N)ˣ), ZMod.card_units_eq_totient] at h1
  rw [Nat.card_eq_fintype_card (α := (ZMod (ordCompl[l] N))ˣ), ZMod.card_units_eq_totient] at h2
  have h3 : Nat.totient N = Nat.totient (ordProj[l] N) * Nat.totient (ordCompl[l] N) := by
    rw [← Nat.totient_mul (Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl.out (NeZero.ne N))),
      Nat.ordProj_mul_ordCompl_eq_self]
  have h4 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h4)
  rw [h1, h3, ← h2, mul_assoc]

/- English proof (translation)
Establish `h` using `(Nat.ordProj_mul_ordCompl_eq_self N l).symm`. Establish `hm : ¬ l ∣ ordCompl[l] N` using `Nat.not_dvd_ordCompl hl.out (NeZero.ne N)`. Generalize the expression as in `ordCompl[l] N = m at h hm ⊢`. Generalize the expression as in `N.factorization l = v at h ⊢`. Consider the cases of `v with`.

Consider the case `zero`. Rewrite `h` using `[pow_zero, one_mul]`. Substitute `h` using the available equality. Conclude with `⟨by simpa using ramificationIdxIn_eq_of_not_dvd l K hm, inertiaDegIn_eq_of_not_dvd l K hm⟩`. Consider the case `succ k`.

Conclude with `⟨by rw [ramificationIdxIn_eq N K h hm, Nat.totient_prime_pow_succ hl.out], inertiaDegIn_eq N K h hm⟩`.
-/
private theorem cycInertia_ef (l : ℕ) [hl : Fact l.Prime] :
    (Ideal.span {(l : ℤ)}).ramificationIdxIn (𝓞 K) = Nat.totient (ordProj[l] N) ∧
      (Ideal.span {(l : ℤ)}).inertiaDegIn (𝓞 K) = orderOf (l : ZMod (ordCompl[l] N)) := by
  have h := (Nat.ordProj_mul_ordCompl_eq_self N l).symm
  have hm : ¬ l ∣ ordCompl[l] N := Nat.not_dvd_ordCompl hl.out (NeZero.ne N)
  generalize ordCompl[l] N = m at h hm ⊢
  generalize N.factorization l = v at h ⊢
  cases v with
  | zero =>
    rw [pow_zero, one_mul] at h
    subst h
    exact ⟨by simpa using ramificationIdxIn_eq_of_not_dvd l K hm, inertiaDegIn_eq_of_not_dvd l K hm⟩
  | succ k =>
    exact ⟨by rw [ramificationIdxIn_eq N K h hm, Nat.totient_prime_pow_succ hl.out],
      inertiaDegIn_eq N K h hm⟩

/- English proof (translation)
Establish `hne : NeZero (ordCompl[l] N)` using `⟨(Nat.ordCompl_pos l (NeZero.ne N)).ne'⟩`. Establish `hζ` using `(IsCyclotomicExtension.zeta_spec N ℚ K).toInteger_isPrimitiveRoot`. Establish `hη` using `hζ.pow (NeZero.pos N) (Nat.ordProj_mul_ordCompl_eq_self N l).symm`. Use `set η := (IsCyclotomicExtension.zeta_spec N ℚ K).toInteger ^ (ordProj[l] N)`. Establish `h₀ : IsPrimitiveRoot (Ideal.Quotient.mk P η) (ordCompl[l] N)`.

Use `hη.idealQuotient_mk (by simpa using Ideal.IsPrime.ne_top inferInstance) ?_` and prove the remaining obligations. Rewrite using `[← Ideal.pow_inertiaDeg l]`. Conclude with `Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl.out (NeZero.ne N))`. Establish `hi` using `h η`. Rewrite `hi` using `[galEquivZMod_smul_of_pow_eq N _ _ ((hη.pow_eq_one_iff_dvd _).mpr (Nat.ordCompl_dvd N l)), map_pow, (h₀.isOfFinOrder (NeZero.ne _)).pow_inj_mod, ← h₀.eq_orderOf, ← ZMod.natCast_eq_natCast_iff', Nat.cast_pow]`.

Use `ext`. Rewrite using `[Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← hi, ZMod.natCast_val]`. Both sides reduce to the same expression.
-/
private theorem cycInertia_key (l : ℕ) [hl : Fact l.Prime] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(l : ℤ)})] (σ : Gal(K/ℚ)) (i : ℕ)
    (h : ∀ x : 𝓞 K, Ideal.Quotient.mk P (σ • x) = Ideal.Quotient.mk P x ^ l ^ i) :
    ZMod.unitsMap (Nat.ordCompl_dvd N l) (galEquivZMod N K σ) =
      ZMod.unitOfCoprime l (Nat.coprime_ordCompl hl.out (NeZero.ne N)) ^ i := by
  have hne : NeZero (ordCompl[l] N) := ⟨(Nat.ordCompl_pos l (NeZero.ne N)).ne'⟩
  have hζ := (IsCyclotomicExtension.zeta_spec N ℚ K).toInteger_isPrimitiveRoot
  have hη := hζ.pow (NeZero.pos N) (Nat.ordProj_mul_ordCompl_eq_self N l).symm
  set η := (IsCyclotomicExtension.zeta_spec N ℚ K).toInteger ^ (ordProj[l] N)
  have h₀ : IsPrimitiveRoot (Ideal.Quotient.mk P η) (ordCompl[l] N) := by
    refine hη.idealQuotient_mk
      (by simpa using Ideal.IsPrime.ne_top inferInstance) ?_
    rw [← Ideal.pow_inertiaDeg l]
    exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl.out (NeZero.ne N))
  have hi := h η
  rw [galEquivZMod_smul_of_pow_eq N _ _
    ((hη.pow_eq_one_iff_dvd _).mpr (Nat.ordCompl_dvd N l)), map_pow,
    (h₀.isOfFinOrder (NeZero.ne _)).pow_inj_mod,
    ← h₀.eq_orderOf, ← ZMod.natCast_eq_natCast_iff', Nat.cast_pow] at hi
  ext
  rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← hi, ZMod.natCast_val]
  rfl

/- English proof (translation)
The claim follows from `Subgroup.card_map_of_injective (galEquivZMod N K).injective`.
-/
private theorem cycInertia_card_map (H : Subgroup Gal(K/ℚ)) :
    Nat.card (H.map (galEquivZMod N K).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (galEquivZMod N K).injective

/- English proof (translation)
Establish `: IsGalois ℚ K` using `IsCyclotomicExtension.isGalois {N} ℚ K`. Apply `Subgroup.eq_of_le_of_card_ge` to reduce the goal to its premises. Introduce and unpack `_ ⟨σ, hσ, rfl⟩`. Use `cycInertia_key (N := N) l P σ 0 (fun x => by` as an intermediate fact. Rewrite using `[pow_zero, pow_one, Ideal.Quotient.eq]`.

Conclude with `hσ x)`. Rewrite `this` using `[pow_zero]`. Conclude with `this`. Rewrite using `[cycInertia_card_map, Ideal.card_inertia_eq_ramificationIdxIn (Ideal.span {(l : ℤ)}), (cycInertia_ef (N := N) l).1, inertiaUnits, ← MonoidHom.comap_bot, cycInertia_card_comap]`. Simplify using the standard rewrite rules.
-/
theorem map_inertia_eq (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(l : ℤ)})] :
    (P.inertia Gal(K/ℚ)).map (galEquivZMod N K).toMonoidHom = inertiaUnits N l := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨σ, hσ, rfl⟩
    have := cycInertia_key (N := N) l P σ 0 (fun x => by
      rw [pow_zero, pow_one, Ideal.Quotient.eq]
      exact hσ x)
    rw [pow_zero] at this
    exact this
  · rw [cycInertia_card_map, Ideal.card_inertia_eq_ramificationIdxIn (Ideal.span {(l : ℤ)}),
      (cycInertia_ef (N := N) l).1, inertiaUnits, ← MonoidHom.comap_bot, cycInertia_card_comap]
    simp

attribute [local instance] Ideal.Quotient.field in

/- English proof (translation)
Establish `: IsGalois ℚ K` using `IsCyclotomicExtension.isGalois {N} ℚ K`. Establish `hP : P ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(l : ℤ)}) (by simpa using (Fact.out : l.Prime).ne_zero) P`. Establish `: P.IsMaximal` using `Ideal.IsPrime.isMaximal inferInstance hP`. Apply `Subgroup.eq_of_le_of_card_ge` to reduce the goal to its premises. Introduce and unpack `_ ⟨σ, hσ, rfl⟩`.

Set `τ` to `IsFractionRing.stabilizerHom Gal(K/ℚ) (Ideal.span {(l : ℤ)}) P (ℤ ⧸ Ideal.span {(l : ℤ)}) (𝓞 K ⧸ P) ⟨σ, hσ⟩`. Establish `: CharP (ℤ ⧸ Ideal.span {(l : ℤ)}) l` using `ringChar.of_eq <| Int.ringChar_idealQuot l`. Establish `: Finite (𝓞 K ⧸ P)` using `Ring.HasFiniteQuotients.finiteQuotient hP`. Take `⟨i, hi⟩` from `FiniteField.exists_forall_apply_eq_pow (ℤ ⧸ Ideal.span {(l : ℤ)}) l (𝓞 K ⧸ P) τ`. Use `cycInertia_key (N := N) l P σ i (fun x => by` as an intermediate fact.

Establish `h₁` using `IsFractionRing.stabilizerHom_apply_apply_mk Gal(K/ℚ) (Ideal.span {(l : ℤ)}) P (ℤ ⧸ Ideal.span {(l : ℤ)}) (𝓞 K ⧸ P) ⟨σ, hσ⟩ x`. Simplify using `only [Algebra.algebraMap_self, RingHomCompTriple.comp_apply] at h₁`. Establish `h2` using `hi (Ideal.Quotient.mk P x)`. Rewrite using `[h₁, Int.card_ideal_quot] at h2)` and apply the resulting hypothesis. Conclude with `⟨i, by simpa using this.symm⟩`.

Rewrite using `[cycInertia_card_map, Ideal.card_stabilizer_eq (Ideal.span {(l : ℤ)}), (cycInertia_ef (N := N) l).1, (cycInertia_ef (N := N) l).2, decompUnits, cycInertia_card_comap, Nat.card_zpowers, ← orderOf_injective _ Units.coeHom_injective, Units.coeHom_apply, ZMod.coe_unitOfCoprime]`.
-/
theorem map_stabilizer_eq (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(l : ℤ)})] :
    (MulAction.stabilizer Gal(K/ℚ) P).map (galEquivZMod N K).toMonoidHom = decompUnits N l := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  have hP : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(l : ℤ)})
    (by simpa using (Fact.out : l.Prime).ne_zero) P
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨σ, hσ, rfl⟩
    let τ := IsFractionRing.stabilizerHom Gal(K/ℚ) (Ideal.span {(l : ℤ)}) P
      (ℤ ⧸ Ideal.span {(l : ℤ)}) (𝓞 K ⧸ P) ⟨σ, hσ⟩
    have : CharP (ℤ ⧸ Ideal.span {(l : ℤ)}) l := ringChar.of_eq <| Int.ringChar_idealQuot l
    have : Finite (𝓞 K ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
    obtain ⟨i, hi⟩ :=
      FiniteField.exists_forall_apply_eq_pow (ℤ ⧸ Ideal.span {(l : ℤ)}) l (𝓞 K ⧸ P) τ
    have := cycInertia_key (N := N) l P σ i (fun x => by
      have h₁ := IsFractionRing.stabilizerHom_apply_apply_mk Gal(K/ℚ) (Ideal.span {(l : ℤ)}) P
        (ℤ ⧸ Ideal.span {(l : ℤ)}) (𝓞 K ⧸ P) ⟨σ, hσ⟩ x
      simp only [Algebra.algebraMap_self, RingHomCompTriple.comp_apply] at h₁
      have h2 := hi (Ideal.Quotient.mk P x)
      rwa [h₁, Int.card_ideal_quot] at h2)
    exact ⟨i, by simpa using this.symm⟩
  · rw [cycInertia_card_map, Ideal.card_stabilizer_eq (Ideal.span {(l : ℤ)}),
      (cycInertia_ef (N := N) l).1, (cycInertia_ef (N := N) l).2, decompUnits,
      cycInertia_card_comap, Nat.card_zpowers, ← orderOf_injective _ Units.coeHom_injective,
      Units.coeHom_apply, ZMod.coe_unitOfCoprime]

/- English proof (translation)
Establish `hζ` using `IsCyclotomicExtension.zeta_spec N ℚ K`. Establish `key : φ.toRatAlgHom.comp (σ : K →ₐ[ℚ] K) = ((starRingEnd ℂ).comp φ).toRatAlgHom`. Apply `(hζ.powerBasis ℚ).algHom_ext` to reduce the goal to its premises. Rewrite using `[IsPrimitiveRoot.powerBasis_gen]`. Express the relevant statement in the definitionally equal form `φ (σ _) = starRingEnd ℂ (φ _)`.

Establish `h1 : ‖φ (IsCyclotomicExtension.zeta N ℚ K)‖ = 1` using `(hζ.map_of_injective φ.injective).norm'_eq_one (NeZero.ne N)`. Rewrite using `[← Complex.inv_eq_conj h1, ← map_inv₀, galEquivZMod_apply_of_pow_eq N K σ hζ.pow_eq_one, hσ]`. Use `congr 1`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]`.

Simplify using the standard rewrite rules. Conclude with `DFunLike.congr_fun key x`.
-/
private theorem cycInertia_conj (σ : Gal(K/ℚ)) (hσ : galEquivZMod N K σ = -1) (φ : K →+* ℂ)
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
Establish `: IsAbelianGalois ℚ K` using `IsCyclotomicExtension.isAbelianGalois {N} ℚ K`. Establish `hmem : ∀ ψ, ψ ∈ fieldChars N E ↔ ∀ σ ∈ E.fixingSubgroup, ψ (galEquivZMod N K σ) = 1`. Introduce `ψ`. Rewrite using `[fieldChars, mem_annihilator_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `h σ hσ`. Conclude with `h _ ⟨σ, hσ, rfl⟩`. Introduce and unpack `h _ ⟨σ, hσ, rfl⟩`. Conclude with `h σ hσ`. Establish `heq : fieldChars N E = intermediateFieldEquivSubgroupChar N K ℂ E`.

Use extensionality with `ψ`. Rewrite using `[hmem, mem_intermediateFieldEquivSubgroupChar_iff]`. Use `⟨by rw [heq, card_intermediateFieldEquivSubgroupChar], ?_⟩` and prove the remaining obligations. Take `⟨σ, hσ⟩` from `(galEquivZMod N K).surjective (-1)`. Establish `heq2 : fieldChars N E = (subgroupGalEquivSubgroupChar N K ℂ E.fixingSubgroup).ofDual`.

Use extensionality with `ψ`. Rewrite using `[hmem, mem_subgroupGalEquivSubgroupChar_iff]`. Use `clear hmem heq`. Generalize the expression as in `fieldChars N E = X at heq2 ⊢`. Establish `h1 : σ ∈ E.fixingSubgroup ↔ ∀ ψ ∈ X, ψ.Even`.

Use `mem_subgroupGalEquivSubgroupChar_symm_iff N K ℂ σ X` as an intermediate fact. Rewrite `this` using `[hσ]`. Use `conv_lhs at this => rw [heq2, OrderDual.toDual_ofDual, OrderIso.symm_apply_apply]`. Simplify `this` using `[DirichletCharacter.Even]`. Rewrite using `[← h1, IntermediateField.mem_fixingSubgroup_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Take `⟨φ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[cycInertia_conj σ hσ]`.

Use `IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap E K))` as an intermediate fact. Rewrite `this` using `[ComplexEmbedding.isReal_iff]`. Conclude with `RingHom.congr_fun this ⟨x, hx⟩`. Introduce `h`. Use `⟨fun w => ?_⟩` and prove the remaining obligations.

Rewrite using `[InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, ← ComplexEmbedding.lift_algebraMap_apply K w.embedding, ← cycInertia_conj σ hσ]`. Use `congr 1`. Conclude with `h x x.2`.
-/
theorem card_fieldChars (E : IntermediateField ℚ K) :
    Nat.card (fieldChars N E) = Module.finrank ℚ E ∧
      (IsTotallyReal E ↔ ∀ ψ ∈ fieldChars N E, ψ.Even) := by
  have : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {N} ℚ K
  have hmem : ∀ ψ, ψ ∈ fieldChars N E ↔
      ∀ σ ∈ E.fixingSubgroup, ψ (galEquivZMod N K σ) = 1 := by
    intro ψ
    rw [fieldChars, mem_annihilator_iff]
    constructor
    · intro h σ hσ
      exact h _ ⟨σ, hσ, rfl⟩
    · rintro h _ ⟨σ, hσ, rfl⟩
      exact h σ hσ
  have heq : fieldChars N E = intermediateFieldEquivSubgroupChar N K ℂ E := by
    ext ψ
    rw [hmem, mem_intermediateFieldEquivSubgroupChar_iff]
  refine ⟨by rw [heq, card_intermediateFieldEquivSubgroupChar], ?_⟩
  obtain ⟨σ, hσ⟩ := (galEquivZMod N K).surjective (-1)
  have heq2 : fieldChars N E = (subgroupGalEquivSubgroupChar N K ℂ E.fixingSubgroup).ofDual := by
    ext ψ
    rw [hmem, mem_subgroupGalEquivSubgroupChar_iff]
  clear hmem heq
  generalize fieldChars N E = X at heq2 ⊢
  have h1 : σ ∈ E.fixingSubgroup ↔ ∀ ψ ∈ X, ψ.Even := by
    have := mem_subgroupGalEquivSubgroupChar_symm_iff N K ℂ σ X
    rw [hσ] at this
    conv_lhs at this => rw [heq2, OrderDual.toDual_ofDual, OrderIso.symm_apply_apply]
    simpa [DirichletCharacter.Even] using this
  rw [← h1, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    apply φ.injective
    rw [cycInertia_conj σ hσ]
    have := IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap E K))
    rw [ComplexEmbedding.isReal_iff] at this
    exact RingHom.congr_fun this ⟨x, hx⟩
  · intro h
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, ← ComplexEmbedding.lift_algebraMap_apply K w.embedding,
      ← cycInertia_conj σ hσ]
    congr 1
    exact h x x.2

end KStar.Ram
