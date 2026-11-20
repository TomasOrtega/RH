import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

/- English proof (translation)
The claim follows from `InfiniteGalois.fixingSubgroup_fixedField ⟨H, H.isClosed_of_isOpen h⟩`.
-/
private theorem fix_fix {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (H : Subgroup (Ω ≃ₐ[ℚ] Ω))
    (h : IsOpen (H : Set (Ω ≃ₐ[ℚ] Ω))) : (IntermediateField.fixedField H).fixingSubgroup = H :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨H, H.isClosed_of_isOpen h⟩

/- English proof (translation)
Rewrite using `[commutator_def, Subgroup.commutator_le]`. Introduce `a _ b _`. Rewrite using `[MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]`. Conclude with `mul_comm _ _`.
-/
private theorem commutator_le_ker_of_hom_int_units {Γ : Type*} [Group Γ] (η : Γ →* ℤˣ) : commutator Γ ≤ η.ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

/- English proof (translation)
Introduce `hc`. Establish `him : z.im = 0` using `Complex.conj_eq_iff_im.mp hc`. Establish `h1` using `congrArg Complex.re h`. Simplify using `[pow_two, him] at h1`. Establish `hD' : (0 : ℝ) < D` using `by exact_mod_cast hD`.

Use polynomial arithmetic with `[mul_self_nonneg z.re]`.
-/
private theorem conj_ne_self_of_sq_eq_neg_natCast (z : ℂ) (D : ℕ) (hD : 0 < D) (h : z ^ 2 = -(D : ℂ)) :
    starRingEnd ℂ z ≠ z := by
  intro hc
  have him : z.im = 0 := Complex.conj_eq_iff_im.mp hc
  have h1 := congrArg Complex.re h
  simp [pow_two, him] at h1
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  nlinarith [mul_self_nonneg z.re]

/- English proof (translation)
Introduce `Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG m U hU`. Take `⟨D, δ, hD, -, hδ2, hδ⟩` from `hG.quad`. Establish `hδ0 : δ ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hδ2`.

Use linear arithmetic over natural numbers and integers. Establish `hker : ∀ s : G ℚ Ω, η s = 1 ↔ s δ = δ`. Introduce `s`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite using `[hδ s, h]`. Simplify using the standard rewrite rules. Introduce `h`. Break down `Int.units_eq_one_or (η s) with h1 | h1` into its components or cases. Conclude with `h1`.

It suffices to derive a contradiction. Rewrite `h` using `[hδ s, h1]`. Simplify using `at h`. Establish `h2 : (2 : Ω) * δ = 0` using `by linear_combination -h`. Break down `mul_eq_zero.mp h2 with h3 | h3` into its components or cases.

Conclude with `two_ne_zero h3`. Conclude with `hδ0 h3`. Establish `hint : IsIntegral ℚ δ` using `Algebra.IsIntegral.isIntegral δ`. Use `haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {δ}) := IntermediateField.adjoin.finiteDimensional hint`. Establish `hkerO : IsOpen (η.ker : Set (G ℚ Ω))`.

Use `Subgroup.isOpen_mono ?_ (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {δ}))` and prove the remaining obligations. Introduce `s hs`. Rewrite using `[MonoidHom.mem_ker, hker]`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).mp hs δ (IntermediateField.mem_adjoin_simple_self ℚ δ)`. Establish `hHo : IsOpen ((U ⊓ η.ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω))`.

Rewrite using `[Subgroup.coe_inf]`. Conclude with `hU.isOpen.inter hkerO`. Establish `hcomm : commutator (G ℚ Ω) ≤ U ⊓ η.ker` using `le_inf hU.ab (commutator_le_ker_of_hom_int_units η)`. Use `set L := IntermediateField.fixedField (U ⊓ η.ker) with hLdef`. Establish `hfix : L.fixingSubgroup = U ⊓ η.ker` using `fix_fix _ hHo`.

Use `haveI : FiniteDimensional ℚ L := (InfiniteGalois.isOpen_iff_finite L).mp (by rw [hfix]; exact hHo)`. Use `haveI : NumberField L := ⟨⟩`. Establish `hN : (L.fixingSubgroup).Normal`. Rewrite using `[hfix]`. Use `⟨fun n hn g => ?_⟩` and prove the remaining obligations.

Establish `hc : g * n * g⁻¹ * n⁻¹ ∈ U ⊓ η.ker` using `hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))`. Establish `he : g * n * g⁻¹ = g * n * g⁻¹ * n⁻¹ * n` using `by group`. Rewrite using `[he]`. Conclude with `Subgroup.mul_mem _ hc hn`. Establish `hAb : @IsAbelianGalois ℚ L _ _ (IntermediateField.algebra' L)`.

Use `letI : Algebra ℚ L := IntermediateField.algebra' L`. Use `haveI hg : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois L).mp hN`. Use `haveI : IsMulCommutative Gal(L/ℚ) := ⟨⟨fun a b => by`. Take `⟨a', rfl⟩` from `AlgEquiv.restrictNormalHom_surjective Ω a`. Take `⟨b', rfl⟩` from `AlgEquiv.restrictNormalHom_surjective Ω b`.

Establish `hc : a' * b' * a'⁻¹ * b'⁻¹ ∈ (AlgEquiv.restrictNormalHom (F` using `ℚ) (K₁ := Ω) L).ker := by`. Rewrite using `[IntermediateField.restrictNormalHom_ker, hfix]`. Conclude with `hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top a') (Subgroup.mem_top b'))`. Rewrite `hc` using `[MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]`. Conclude with `mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc)⟩⟩`.

Conclude with `⟨⟩`. Use `haveI : IsAbelianGalois ℚ L := by`. Apply the tactic sequence `convert hAb <;> exact Subsingleton.elim _ _`. Establish `hδL : δ ∈ L`. Rewrite using `[IntermediateField.mem_fixedField_iff]`.

Introduce `s hs`. Conclude with `(hker s).mp (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hs).2)`. Establish `hδL2 : (⟨δ, hδL⟩ : L) ^ 2 = -(D : L)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using hδ2`.

Use `haveI : NumberField.IsTotallyComplex L := ⟨fun v => by`. Rewrite using `[← NumberField.InfinitePlace.not_isReal_iff_isComplex, NumberField.InfinitePlace.isReal_iff]`. Introduce `hv`. Apply `conj_ne_self_of_sq_eq_neg_natCast (v.embedding ⟨δ, hδL⟩) D hD` to reduce the goal to its premises. Rewrite using `[← map_pow, hδL2]`.

Simplify using the standard rewrite rules. Use `RingHom.congr_fun hv ⟨δ, hδL⟩` as an intermediate fact. Rewrite using `[NumberField.ComplexEmbedding.conjugate_coe_eq] at this⟩` and apply the resulting hypothesis. Take `⟨j, hj⟩` from `hG.cc`. Establish `hσU : σ ∈ U` using `hU.real σ hG.cc`.

Establish `hησ : η σ = -1`. Break down `Int.units_eq_one_or (η σ) with h | h` into its components or cases. It suffices to derive a contradiction. Establish `hσδ : σ δ = δ` using `(hker σ).mp h`. Apply `conj_ne_self_of_sq_eq_neg_natCast (j δ) D hD` to reduce the goal to its premises.

Rewrite using `[← map_pow, hδ2]`. Simplify using the standard rewrite rules. Rewrite using `[← hj, hσδ]`. Conclude with `h`. Establish `hcc : ∀ z : L, σ (z : Ω) = ((NumberField.IsCMField.complexConj L z : L) : Ω)`.

Introduce `z`. Apply `j.injective` to reduce the goal to its premises. Rewrite using `[hj]`. Conclude with `(NumberField.IsCMField.complexEmbedding_complexConj L (j.comp (algebraMap L Ω)) z).symm`. Use `⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `s`. Express the relevant statement in the definitionally equal form `(∀ x ∈ NumberField.maximalRealSubfield L, s (algebraMap L Ω x) = algebraMap L Ω x) ↔ s ∈ U`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← fix_fix U hU.isOpen, IntermediateField.mem_fixingSubgroup_iff]`.

Introduce `y hy`. Establish `hyL : y ∈ L` using `(IntermediateField.mem_fixedField_iff _ _).mpr fun f hf => (IntermediateField.mem_fixedField_iff _ _).mp hy f (Subgroup.mem_inf.mp hf).1`. Establish `hre : (⟨y, hyL⟩ : L) ∈ NumberField.maximalRealSubfield L`. Rewrite using `[← NumberField.IsCMField.complexConj_eq_self_iff]`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[← hcc]`. Conclude with `(IntermediateField.mem_fixedField_iff _ _).mp hy σ hσU`. Conclude with `h _ hre`. Introduce `hs x hx`. Establish `hσx : σ (x : Ω) = x`.

Rewrite using `[hcc, (NumberField.IsCMField.complexConj_eq_self_iff L x).mpr hx]`. Use `show s (x : Ω) = x`. Break down `Int.units_eq_one_or (η s) with h1 | h1` into its components or cases. Conclude with `(IntermediateField.mem_fixedField_iff _ _).mp x.2 s (Subgroup.mem_inf.mpr ⟨hs, h1⟩)`. Establish `hm : σ * s ∈ U ⊓ η.ker`.

Use `Subgroup.mem_inf.mpr ⟨U.mul_mem hσU hs, ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.mem_ker, map_mul, hησ, h1]`. Both sides reduce to the same expression. Use `(IntermediateField.mem_fixedField_iff _ _).mp x.2 (σ * s) hm` as an intermediate fact. Rewrite `this` using `[AlgEquiv.mul_apply]`.

Apply `σ.injective` to reduce the goal to its premises. Rewrite using `[this, hσx]`. Use extensionality with `s`. Express the relevant statement in the definitionally equal form `(∀ x : L, s (algebraMap L Ω x) = algebraMap L Ω x) ↔ s ∈ U ⊓ η.ker`. Rewrite using `[← hfix, IntermediateField.mem_fixingSubgroup_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Conclude with `h ⟨x, hx⟩`. Introduce `h x`. Conclude with `h x x.2`.
-/
theorem UpperTheory.V.Fr.field_ex :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (m : ℕ) (U : Subgroup (G ℚ Ω)), UFacts l η Ψ M m U → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : IsCMField L) (_ : Algebra L Ω), IsAbelianGalois ℚ L ∧ upl Ω L = U ∧ galOf ℚ L Ω = U ⊓ η.ker := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG m U hU
  obtain ⟨D, δ, hD, -, hδ2, hδ⟩ := hG.quad
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    simp at hδ2
    omega
  have hker : ∀ s : G ℚ Ω, η s = 1 ↔ s δ = δ := by
    intro s
    constructor
    · intro h
      rw [hδ s, h]
      simp
    · intro h
      rcases Int.units_eq_one_or (η s) with h1 | h1
      · exact h1
      · exfalso
        rw [hδ s, h1] at h
        simp at h
        have h2 : (2 : Ω) * δ = 0 := by linear_combination -h
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact two_ne_zero h3
        · exact hδ0 h3
  have hint : IsIntegral ℚ δ := Algebra.IsIntegral.isIntegral δ
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {δ}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hkerO : IsOpen (η.ker : Set (G ℚ Ω)) := by
    refine Subgroup.isOpen_mono ?_ (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {δ}))
    intro s hs
    rw [MonoidHom.mem_ker, hker]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hs δ
      (IntermediateField.mem_adjoin_simple_self ℚ δ)
  have hHo : IsOpen ((U ⊓ η.ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
    rw [Subgroup.coe_inf]
    exact hU.isOpen.inter hkerO
  have hcomm : commutator (G ℚ Ω) ≤ U ⊓ η.ker := le_inf hU.ab (commutator_le_ker_of_hom_int_units η)
  set L := IntermediateField.fixedField (U ⊓ η.ker) with hLdef
  have hfix : L.fixingSubgroup = U ⊓ η.ker := fix_fix _ hHo
  haveI : FiniteDimensional ℚ L := (InfiniteGalois.isOpen_iff_finite L).mp (by rw [hfix]; exact hHo)
  haveI : NumberField L := ⟨⟩
  have hN : (L.fixingSubgroup).Normal := by
    rw [hfix]
    refine ⟨fun n hn g => ?_⟩
    have hc : g * n * g⁻¹ * n⁻¹ ∈ U ⊓ η.ker :=
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    have he : g * n * g⁻¹ = g * n * g⁻¹ * n⁻¹ * n := by
      group
    rw [he]
    exact Subgroup.mul_mem _ hc hn
  have hAb : @IsAbelianGalois ℚ L _ _ (IntermediateField.algebra' L) := by
    letI : Algebra ℚ L := IntermediateField.algebra' L
    haveI hg : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois L).mp hN
    haveI : IsMulCommutative Gal(L/ℚ) := ⟨⟨fun a b => by
      obtain ⟨a', rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω a
      obtain ⟨b', rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω b
      have hc : a' * b' * a'⁻¹ * b'⁻¹ ∈ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) L).ker := by
        rw [IntermediateField.restrictNormalHom_ker, hfix]
        exact hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top a') (Subgroup.mem_top b'))
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hc
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc)⟩⟩
    exact ⟨⟩
  haveI : IsAbelianGalois ℚ L := by
    convert hAb <;> exact Subsingleton.elim _ _
  have hδL : δ ∈ L := by
    rw [IntermediateField.mem_fixedField_iff]
    intro s hs
    exact (hker s).mp (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hs).2)
  have hδL2 : (⟨δ, hδL⟩ : L) ^ 2 = -(D : L) := by
    apply Subtype.ext
    simpa using hδ2
  haveI : NumberField.IsTotallyComplex L := ⟨fun v => by
    rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex, NumberField.InfinitePlace.isReal_iff]
    intro hv
    apply conj_ne_self_of_sq_eq_neg_natCast (v.embedding ⟨δ, hδL⟩) D hD
    · rw [← map_pow, hδL2]
      simp
    · have := RingHom.congr_fun hv ⟨δ, hδL⟩
      rwa [NumberField.ComplexEmbedding.conjugate_coe_eq] at this⟩
  obtain ⟨j, hj⟩ := hG.cc
  have hσU : σ ∈ U := hU.real σ hG.cc
  have hησ : η σ = -1 := by
    rcases Int.units_eq_one_or (η σ) with h | h
    · exfalso
      have hσδ : σ δ = δ := (hker σ).mp h
      apply conj_ne_self_of_sq_eq_neg_natCast (j δ) D hD
      · rw [← map_pow, hδ2]
        simp
      · rw [← hj, hσδ]
    · exact h
  have hcc : ∀ z : L, σ (z : Ω) = ((NumberField.IsCMField.complexConj L z : L) : Ω) := by
    intro z
    apply j.injective
    rw [hj]
    exact (NumberField.IsCMField.complexEmbedding_complexConj L (j.comp (algebraMap L Ω)) z).symm
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · ext s
    change (∀ x ∈ NumberField.maximalRealSubfield L, s (algebraMap L Ω x) = algebraMap L Ω x) ↔ s ∈ U
    constructor
    · intro h
      rw [← fix_fix U hU.isOpen, IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have hyL : y ∈ L := (IntermediateField.mem_fixedField_iff _ _).mpr fun f hf =>
        (IntermediateField.mem_fixedField_iff _ _).mp hy f (Subgroup.mem_inf.mp hf).1
      have hre : (⟨y, hyL⟩ : L) ∈ NumberField.maximalRealSubfield L := by
        rw [← NumberField.IsCMField.complexConj_eq_self_iff]
        apply Subtype.ext
        rw [← hcc]
        exact (IntermediateField.mem_fixedField_iff _ _).mp hy σ hσU
      exact h _ hre
    · intro hs x hx
      have hσx : σ (x : Ω) = x := by
        rw [hcc, (NumberField.IsCMField.complexConj_eq_self_iff L x).mpr hx]
      show s (x : Ω) = x
      rcases Int.units_eq_one_or (η s) with h1 | h1
      · exact (IntermediateField.mem_fixedField_iff _ _).mp x.2 s (Subgroup.mem_inf.mpr ⟨hs, h1⟩)
      · have hm : σ * s ∈ U ⊓ η.ker := by
          refine Subgroup.mem_inf.mpr ⟨U.mul_mem hσU hs, ?_⟩
          rw [MonoidHom.mem_ker, map_mul, hησ, h1]
          rfl
        have := (IntermediateField.mem_fixedField_iff _ _).mp x.2 (σ * s) hm
        rw [AlgEquiv.mul_apply] at this
        apply σ.injective
        rw [this, hσx]
  · ext s
    change (∀ x : L, s (algebraMap L Ω x) = algebraMap L Ω x) ↔ s ∈ U ⊓ η.ker
    rw [← hfix, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x x.2
